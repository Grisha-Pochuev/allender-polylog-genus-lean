import Allender.MacroblockCircuit
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Standalone circuits for concrete macroblocks

A block relation has two kinds of input: the original `n` input bits and an
incoming width-`w` boundary state.  This module turns those data into one
ordinary `(n+w)`-input source circuit.  Its first layer loads the boundary
state, and the remaining layers are the concrete macroblock layers with their
original external-input references widened from `n` to `n+w`.

The construction is semantic, not an interface: Lean proves that evaluating
the resulting circuit returns exactly the corresponding `evalLayers` output.
-/

namespace Allender

namespace BitState

/-- Concatenate an original input with an incoming boundary state. -/
def append {n w : Nat} (x : BitState n) (boundary : BitState w) :
    BitState (n + w) :=
  Fin.addCases x boundary

@[simp] theorem append_castAdd {n w : Nat} (x : BitState n)
    (boundary : BitState w) (i : Fin n) :
    append x boundary (Fin.castAdd w i) = x i := by
  simp [append]

@[simp] theorem append_natAdd {n w : Nat} (x : BitState n)
    (boundary : BitState w) (j : Fin w) :
    append x boundary (Fin.natAdd n j) = boundary j := by
  simp [append]

end BitState

/-- Widen only the external-input indices of a source gate.  Parent positions
in the preceding width-`w` state are unchanged. -/
def Gate.widenInput {n w extra : Nat} : Gate n w → Gate (n + extra) w
  | .input i negated => .input (Fin.castAdd extra i) negated
  | .constant value => .constant value
  | .copyGate source => .copyGate source
  | .andGate left right => .andGate left right
  | .orGate left right => .orGate left right

@[simp] theorem Gate.widenInput_parents {n w extra : Nat} (g : Gate n w) :
    (g.widenInput : Gate (n + extra) w).parents = g.parents := by
  cases g <;> rfl

@[simp] theorem Gate.widenInput_eval {n w extra : Nat} (g : Gate n w)
    (x : BitState n) (suffix : BitState extra) (previous : BitState w) :
    (g.widenInput : Gate (n + extra) w).eval (BitState.append x suffix)
      previous = g.eval x previous := by
  cases g with
  | input i negated =>
      cases negated <;> simp [Gate.widenInput, Gate.eval]
  | constant value => rfl
  | copyGate source => rfl
  | andGate left right => rfl
  | orGate left right => rfl

/-- Widen all external-input references in one circuit layer. -/
def CircuitLayer.widenInput {n w extra : Nat} (layer : CircuitLayer n w) :
    CircuitLayer (n + extra) w :=
  fun j => (layer j).widenInput

@[simp] theorem CircuitLayer.widenInput_eval {n w extra : Nat}
    (layer : CircuitLayer n w) (x : BitState n) (suffix : BitState extra)
    (previous : BitState w) :
    layer.widenInput.eval (BitState.append x suffix) previous =
      layer.eval x previous := by
  funext j
  exact Gate.widenInput_eval (layer j) x suffix previous

/-- A first layer that loads the incoming boundary state from the last `w`
external input coordinates. -/
def boundaryInputLayer (n w : Nat) : CircuitLayer (n + w) w :=
  fun j => Gate.input (Fin.natAdd n j) false

@[simp] theorem boundaryInputLayer_eval (n w : Nat) (x : BitState n)
    (boundary previous : BitState w) :
    (boundaryInputLayer n w).eval (BitState.append x boundary) previous =
      boundary := by
  funext j
  simp [boundaryInputLayer, CircuitLayer.eval]

/-- Standalone source circuit for one concrete macroblock and one selected
output coordinate. -/
def Circuit.macroblockCircuit {n w : Nat} (C : Circuit n w)
    (block : List TransitionTag) (output : Fin w) : Circuit (n + w) w where
  layers := boundaryInputLayer n w ::
    (C.macroblockLayers block).map CircuitLayer.widenInput
  output := output

/-- Widening every layer preserves the exact segment computation. -/
theorem evalLayers_widenInput {n w extra : Nat}
    (layers : List (CircuitLayer n w)) (x : BitState n)
    (suffix : BitState extra) (initial : BitState w) :
    evalLayers (layers.map CircuitLayer.widenInput)
        (BitState.append x suffix) initial =
      evalLayers layers x initial := by
  induction layers generalizing initial with
  | nil => rfl
  | cons layer layers ih =>
      simp only [List.map_cons, evalLayers, List.foldl_cons]
      rw [CircuitLayer.widenInput_eval]
      exact ih (layer.eval x initial)

/-- The standalone block circuit computes exactly the selected bit of the
original macroblock transition from the supplied boundary state. -/
theorem Circuit.macroblockCircuit_eval {n w : Nat} (C : Circuit n w)
    (block : List TransitionTag) (output : Fin w)
    (x : BitState n) (boundary : BitState w) :
    (C.macroblockCircuit block output).eval (BitState.append x boundary) =
      evalLayers (C.macroblockLayers block) x boundary output := by
  unfold Circuit.eval Circuit.finalState Circuit.macroblockCircuit
  simp only [List.foldl_cons]
  rw [boundaryInputLayer_eval]
  exact congrFun
    (evalLayers_widenInput (C.macroblockLayers block) x boundary boundary)
    output

/-- The standalone block circuit adds exactly one boundary-loading layer. -/
@[simp] theorem Circuit.macroblockCircuit_layers_length {n w : Nat}
    (C : Circuit n w) (block : List TransitionTag) (output : Fin w) :
    (C.macroblockCircuit block output).layers.length = block.length + 1 := by
  simp [Circuit.macroblockCircuit]

/-- Exact padded gate count of the standalone block circuit. -/
theorem Circuit.macroblockCircuit_size {n w : Nat} (C : Circuit n w)
    (block : List TransitionTag) (output : Fin w) :
    (C.macroblockCircuit block output).size = (block.length + 1) * w := by
  simp [Circuit.size]

/-- Every local layer number of a canonical block circuit maps to an actual
layer number of the ambient circuit. -/
theorem Circuit.macroblock_start_add_lt_layers {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (i : Nat) (hi : i < block.length + 1) :
    (block.head (macroblock_ne_nil hblock)).index + i <
      C.layers.length := by
  have hne : block ≠ [] := macroblock_ne_nil hblock
  let first := block.head hne
  have hchain := macroblock_index_isChain hblock
  cases i with
  | zero =>
      have hfirstMem : first ∈ block := List.head_mem hne
      have hfirstAll := mem_transitionTags_of_mem_macroblock hblock hfirstMem
      have hindex :=
        (transitionTag_mem_transitionTags_iff _ _ first.index first.bad).1 hfirstAll |>.1
      have htail : C.layers.tail.length ≤ C.layers.length := by simp
      simpa [first] using hindex.trans_le htail
  | succ i =>
      have hiBlock : i < block.length := by omega
      let tag := block[i]
      have htagMem : tag ∈ block := List.getElem_mem hiBlock
      have htagAll := mem_transitionTags_of_mem_macroblock hblock htagMem
      have htagIndex :=
        (transitionTag_mem_transitionTags_iff _ _ tag.index tag.bad).1 htagAll |>.1
      have hposition : tag.index = first.index + i := by
        simpa [first, tag] using
          transitionTag_index_getElem hne hchain i hiBlock
      have htailLength : C.layers.tail.length = C.layers.length - 1 := by simp
      dsimp [first] at hposition ⊢
      omega

/-- Inject the local vertices of a standalone canonical block circuit into the
corresponding ambient circuit layers. -/
def Circuit.macroblockVertexEmbedding {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (output : Fin w) :
    (C.macroblockCircuit block output).Vertex ↪ C.Vertex where
  toFun := fun v =>
    let hne : block ≠ [] := macroblock_ne_nil hblock
    (⟨(block.head hne).index + v.1.val,
        C.macroblock_start_add_lt_layers cuts hblock v.1.val
          (by simpa using v.1.isLt)⟩, v.2)
  inj' := by
    intro u v huv
    apply Prod.ext
    · apply Fin.ext
      have hlayers := congrArg (fun z => z.1.val) huv
      exact Nat.add_left_cancel hlayers
    · simpa using congrArg Prod.snd huv

@[simp] theorem Circuit.macroblockVertexEmbedding_layer {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (output : Fin w) (v : (C.macroblockCircuit block output).Vertex) :
    (C.macroblockVertexEmbedding cuts hblock output v).1.val =
      (block.head (macroblock_ne_nil hblock)).index +
        v.1.val := rfl

@[simp] theorem Circuit.macroblockVertexEmbedding_position {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (output : Fin w) (v : (C.macroblockCircuit block output).Vertex) :
    (C.macroblockVertexEmbedding cuts hblock output v).2 = v.2 := rfl

/-- Layer `i+1` of the standalone circuit is precisely the widened target
layer of transition tag `i` in the block. -/
theorem Circuit.macroblockCircuit_layer_succ {n w : Nat}
    (C : Circuit n w) (block : List TransitionTag) (output : Fin w)
    (i : Nat) (hi : i < block.length) :
    (C.macroblockCircuit block output).layers.get
        ⟨i + 1, by simp [Circuit.macroblockCircuit]; omega⟩ =
      (C.layerAfterTransition block[i]).widenInput := by
  simp [Circuit.macroblockCircuit, Circuit.macroblockLayers]

/-- A canonical transition tag is in range, so its total `getD` target layer
is the corresponding dependent `List.get`. -/
theorem Circuit.layerAfterTransition_eq_get {n w : Nat}
    (C : Circuit n w) (tag : TransitionTag)
    (hindex : tag.index < C.layers.tail.length) :
    C.layerAfterTransition tag =
      C.layers.get ⟨tag.index + 1, by
        have htail : C.layers.tail.length = C.layers.length - 1 := by simp
        omega⟩ := by
  have hlt : tag.index + 1 < C.layers.length := by
    have htail : C.layers.tail.length = C.layers.length - 1 := by simp
    omega
  unfold Circuit.layerAfterTransition
  rw [List.getD_eq_getElem C.layers Circuit.fallbackLayer hlt]
  rfl

/-- Every directed dependency edge of a standalone canonical block circuit
maps to the corresponding directed edge of the ambient block graph. -/
theorem Circuit.macroblockCircuit_edge_embedding {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (output : Fin w)
    {u v : (C.macroblockCircuit block output).Vertex}
    (hedge : (C.macroblockCircuit block output).layeredGraph.edge u v) :
    (C.macroblockGraph block).edge
      (C.macroblockVertexEmbedding cuts hblock output u)
      (C.macroblockVertexEmbedding cuts hblock output v) := by
  have hne : block ≠ [] := macroblock_ne_nil hblock
  let first := block.head hne
  let i := u.1.val
  have hvLayer : v.1.val = i + 1 := hedge.1
  have hvBound : v.1.val < block.length + 1 := by
    simpa using v.1.isLt
  have hi : i < block.length := by omega
  let tag := block[i]
  have htagMem : tag ∈ block := List.getElem_mem hi
  have htagAll := mem_transitionTags_of_mem_macroblock hblock htagMem
  have htagIndex : tag.index < C.layers.tail.length :=
    (transitionTag_mem_transitionTags_iff _ _ tag.index tag.bad).1 htagAll |>.1
  have htagPosition : tag.index = first.index + i := by
    simpa [tag, first] using transitionTag_index_getElem hne
      (macroblock_index_isChain hblock) i hi
  have hheadIndex :
      (block.head (macroblock_ne_nil hblock)).index = first.index := by
    rfl
  have hlocalTarget : v.1 =
      ⟨i + 1, by simp [Circuit.macroblockCircuit]; omega⟩ := by
    apply Fin.ext
    exact hvLayer
  have hparents := hedge.2
  rw [hlocalTarget, C.macroblockCircuit_layer_succ block output i hi] at hparents
  refine ⟨?_, tag, htagMem, ?_⟩
  · constructor
    · simp only [Circuit.macroblockVertexEmbedding_layer]
      omega
    · have htargetLayer :
          (C.macroblockVertexEmbedding cuts hblock output v).1 =
            ⟨tag.index + 1, by
              have htail : C.layers.tail.length = C.layers.length - 1 := by simp
              omega⟩ := by
          apply Fin.ext
          change (block.head (macroblock_ne_nil hblock)).index + v.1.val =
            tag.index + 1
          rw [hheadIndex, htagPosition, hvLayer]
          omega
      rw [htargetLayer]
      rw [← C.layerAfterTransition_eq_get tag htagIndex]
      simpa [CircuitLayer.widenInput, tag] using hparents
  · simp only [Circuit.macroblockVertexEmbedding_layer]
    exact htagPosition

/-- After injective relabelling, the entire undirected dependency graph of a
standalone canonical block circuit is a subgraph of the ambient block graph. -/
theorem Circuit.macroblockCircuit_graph_map_le {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (output : Fin w) :
    (C.macroblockCircuit block output).layeredGraph.toSimpleGraph.map
        (C.macroblockVertexEmbedding cuts hblock output) ≤
      (C.macroblockGraph block).toSimpleGraph := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  rcases huv with huv | hvu
  · exact Or.inl (C.macroblockCircuit_edge_embedding cuts hblock output huv)
  · exact Or.inr (C.macroblockCircuit_edge_embedding cuts hblock output hvu)

/-- Every standalone circuit extracted from a good canonical macroblock is
planar.  The only additional topology fact beyond the ambient block theorem is
genus invariance under the explicit injective vertex relabelling. -/
theorem Circuit.macroblockCircuit_isPlanar {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hremainder : OrientableGenus.IsPlanar
      (C.layeredGraph.deleteLayers cuts).toSimpleGraph)
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (hgood : GoodMacroblock block) (output : Fin w) :
    OrientableGenus.IsPlanar
      (C.macroblockCircuit block output).layeredGraph.toSimpleGraph := by
  apply OrientableGenus.isPlanar_of_map_le
    (C.macroblockVertexEmbedding cuts hblock output)
    (C.macroblockCircuit_graph_map_le cuts hblock output)
  exact C.goodMacroblock_isPlanar cuts hremainder hblock hgood

/-- Combined concrete output of Sections 3 and 4: a genus-`g` circuit admits
a bounded canonical cut set, a bounded canonical macroblock list, and every
good block/output pair yields an actual planar standalone circuit.

`Nonempty C.Vertex` excludes the degenerate zero-layer graph required by the
current median-component API; circuits used in a family simulation have a
real output layer and satisfy this condition.
-/
theorem Circuit.exists_planarizingCuts_with_planar_good_macroblocks
    {n w g : Nat} (C : Circuit n w) [Nonempty C.Vertex]
    (hgenus : OrientableGenus.genus C.layeredGraph.toSimpleGraph ≤ g) :
    ∃ cuts : Finset Nat,
      cuts.card ≤ g * (Nat.log 2 C.size + 1) ∧
      (macroblockTags C.layers.tail.length cuts).length ≤
        4 * cuts.card + 1 ∧
      ∀ block ∈ macroblockTags C.layers.tail.length cuts,
        GoodMacroblock block → ∀ output : Fin w,
          OrientableGenus.IsPlanar
            (C.macroblockCircuit block output).layeredGraph.toSimpleGraph := by
  classical
  letI : DecidableRel C.layeredGraph.edge := by
    intro u v
    unfold Circuit.layeredGraph
    infer_instance
  rcases C.layeredGraph.exists_planarizing_layer_set hgenus with
    ⟨cuts, hcuts, hplanar⟩
  refine ⟨cuts, ?_, macroblockTags_length_le_of_cuts _ cuts, ?_⟩
  · simpa [C.size_eq_card_vertex] using hcuts
  · intro block hblock hgood output
    exact C.macroblockCircuit_isPlanar cuts hplanar hblock hgood output

end Allender
