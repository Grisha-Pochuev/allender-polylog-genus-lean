import Allender.BlockCircuit

/-!
# Macroblock circuits with a fixed incoming state

Hansen's theorem is applied to ordinary circuits whose only varying input is
the original input `x`.  A macroblock relation entry additionally fixes an
incoming boundary state `p` and asks for one outgoing coordinate.  This module
implements that specialization concretely.

The first layer consists of Boolean constants holding `p`; all later layers
are the actual macroblock layers.  The first layer of the earlier standalone
circuit instead reads `p` from suffix inputs.  Both kinds of gates have no
parents, so their dependency graphs are identical after the explicit vertex
relabeling below.
-/

namespace Allender

/-- A width-`w` layer which loads a fixed state. -/
def constantStateLayer {n w : Nat} (state : BitState w) : CircuitLayer n w :=
  fun j => Gate.constant (state j)

@[simp] theorem constantStateLayer_eval {n w : Nat} (state : BitState w)
    (x : BitState n) (previous : BitState w) :
    (constantStateLayer state).eval x previous = state := by
  funext j
  simp [constantStateLayer, CircuitLayer.eval, Gate.eval]

namespace Circuit

/-- A macroblock/output circuit whose incoming boundary state is fixed to
`state`; its only external inputs are the original `n` input bits. -/
def fixedBoundaryMacroblockCircuit {n w : Nat} (C : Circuit n w)
    (block : List TransitionTag) (state : BitState w) (output : Fin w) :
    Circuit n w where
  layers := constantStateLayer state :: C.macroblockLayers block
  output := output

/-- Exact semantics of the fixed-boundary macroblock circuit. -/
@[simp] theorem fixedBoundaryMacroblockCircuit_eval {n w : Nat}
    (C : Circuit n w) (block : List TransitionTag) (state : BitState w)
    (output : Fin w) (x : BitState n) :
    (C.fixedBoundaryMacroblockCircuit block state output).eval x =
      evalLayers (C.macroblockLayers block) x state output := by
  unfold Circuit.eval Circuit.finalState fixedBoundaryMacroblockCircuit
  simp only [List.foldl_cons]
  rw [constantStateLayer_eval]
  rfl

@[simp] theorem fixedBoundaryMacroblockCircuit_layers_length {n w : Nat}
    (C : Circuit n w) (block : List TransitionTag) (state : BitState w)
    (output : Fin w) :
    (C.fixedBoundaryMacroblockCircuit block state output).layers.length =
      block.length + 1 := by
  simp [fixedBoundaryMacroblockCircuit]

@[simp] theorem fixedBoundaryMacroblockCircuit_size {n w : Nat}
    (C : Circuit n w) (block : List TransitionTag) (state : BitState w)
    (output : Fin w) :
    (C.fixedBoundaryMacroblockCircuit block state output).size =
      (block.length + 1) * w := by
  simp [Circuit.size]

/-- Relabel circuit vertices when two circuits have equal layer counts. -/
def vertexEmbeddingOfLengthEq {n n' w : Nat} (C : Circuit n w)
    (D : Circuit n' w) (h : C.layers.length = D.layers.length) :
    C.Vertex ↪ D.Vertex where
  toFun := fun v => (Fin.cast h v.1, v.2)
  inj' := by
    intro u v huv
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z => z.1.val) huv
    · simpa using congrArg Prod.snd huv

/-- Equal-length circuits whose corresponding gates have the same parents
have the same dependency edges after explicit relabeling. -/
theorem graph_map_le_of_parents {n n' w : Nat} (C : Circuit n w)
    (D : Circuit n' w) (h : C.layers.length = D.layers.length)
    (hparents : ∀ (i : Fin C.layers.length) (j : Fin w),
      ((C.layers.get i) j).parents =
        ((D.layers.get (Fin.cast h i)) j).parents) :
    C.layeredGraph.toSimpleGraph.map (C.vertexEmbeddingOfLengthEq D h) ≤
      D.layeredGraph.toSimpleGraph := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  rcases huv with huv | hvu
  · left
    constructor
    · exact huv.1
    · change u.2 ∈ ((D.layers.get (Fin.cast h v.1)) v.2).parents
      rw [← hparents v.1 v.2]
      exact huv.2
  · right
    constructor
    · exact hvu.1
    · change v.2 ∈ ((D.layers.get (Fin.cast h u.1)) u.2).parents
      rw [← hparents u.1 u.2]
      exact hvu.2

/-- Fixed-boundary and suffix-input standalone circuits have identical
dependency parents at corresponding vertices. -/
theorem fixedBoundary_parents_eq_macroblockCircuit {n w : Nat}
    (C : Circuit n w) (block : List TransitionTag) (state : BitState w)
    (output : Fin w)
    (i : Fin (C.fixedBoundaryMacroblockCircuit block state output).layers.length)
    (j : Fin w) :
    (((C.fixedBoundaryMacroblockCircuit block state output).layers.get i) j).parents =
      (((C.macroblockCircuit block output).layers.get
        (Fin.cast (by simp) i)) j).parents := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [fixedBoundaryMacroblockCircuit, Circuit.macroblockCircuit,
      constantStateLayer, boundaryInputLayer]
  · simp [fixedBoundaryMacroblockCircuit, Circuit.macroblockCircuit,
      CircuitLayer.widenInput]

/-- Every fixed-boundary circuit extracted from a good macroblock is planar. -/
theorem fixedBoundaryMacroblockCircuit_isPlanar {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hremainder : OrientableGenus.IsPlanar
      (C.layeredGraph.deleteLayers cuts).toSimpleGraph)
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (hgood : GoodMacroblock block) (state : BitState w) (output : Fin w) :
    OrientableGenus.IsPlanar
      (C.fixedBoundaryMacroblockCircuit block state output).layeredGraph.toSimpleGraph := by
  let fixed := C.fixedBoundaryMacroblockCircuit block state output
  let standalone := C.macroblockCircuit block output
  have hlength : fixed.layers.length = standalone.layers.length := by
    simp [fixed, standalone]
  apply OrientableGenus.isPlanar_of_map_le
    (fixed.vertexEmbeddingOfLengthEq standalone hlength)
    (fixed.graph_map_le_of_parents standalone hlength ?_)
  · exact C.macroblockCircuit_isPlanar cuts hremainder hblock hgood output
  · intro i j
    simpa [fixed, standalone] using
      C.fixedBoundary_parents_eq_macroblockCircuit block state output i j

end Circuit
end Allender
