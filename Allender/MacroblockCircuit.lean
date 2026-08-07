import Allender.CanonicalPlanarization
import Allender.BoundaryPredicates
import Allender.CircuitGraph
import Allender.MacroblockPartition
import Mathlib.Data.List.Induction
import Mathlib.Data.List.GetD

/-!
# Concrete circuit graphs of macroblocks

This module connects the combinatorial transition partition to the actual
dependency graph of a circuit.  A macroblock graph keeps precisely the circuit
edges whose source transition index occurs in the block.  If every transition
tag in the block is good, both endpoint layers survive the chosen whole-layer
deletion.  The block graph is consequently a spanning subgraph of the planar
remainder.

No circuit-simulation theorem is assumed here.  The only topological fact used
by the final planarity theorem is genus monotonicity from the explicit
`OrientableGenus` boundary.
-/

namespace Allender

/-- Every transition in a good macroblock avoids the cut layers at both
endpoints. -/
def GoodMacroblock (block : List TransitionTag) : Prop :=
  ∀ tag ∈ block, tag.bad = false

/-- Decidable Boolean test corresponding to `GoodMacroblock`. -/
def goodMacroblockBool (block : List TransitionTag) : Bool :=
  block.all fun tag => !tag.bad

@[simp] theorem goodMacroblockBool_eq_true (block : List TransitionTag) :
    goodMacroblockBool block = true ↔ GoodMacroblock block := by
  simp [goodMacroblockBool, GoodMacroblock]

@[simp] theorem sameGoodRun_eq_true_iff (a b : TransitionTag) :
    sameGoodRun a b = true ↔ a.bad = false ∧ b.bad = false := by
  rcases a with ⟨a, abad⟩
  rcases b with ⟨b, bbad⟩
  cases abad <;> cases bbad <;> simp [sameGoodRun]

/-- Once the head of a same-good-run chain is good, every tag in the chain is
good. -/
theorem goodMacroblock_of_chain {a : TransitionTag} {tail : List TransitionTag}
    (ha : a.bad = false)
    (hchain : (a :: tail).IsChain fun x y => sameGoodRun x y) :
    GoodMacroblock (a :: tail) := by
  induction tail generalizing a with
  | nil =>
      intro tag htag
      simp only [List.mem_singleton] at htag
      subst tag
      exact ha
  | cons b tail ih =>
      have hab : sameGoodRun a b = true := by
        have hhead := (List.isChain_cons.mp hchain).1
        simpa using hhead b
      have hb : b.bad = false := (sameGoodRun_eq_true_iff a b).1 hab |>.2
      have htail : (b :: tail).IsChain fun x y => sameGoodRun x y :=
        (List.isChain_cons.mp hchain).2
      have hgoodTail : GoodMacroblock (b :: tail) := ih hb htail
      intro tag htag
      rcases List.mem_cons.mp htag with rfl | htag
      · exact ha
      · exact hgoodTail tag htag

/-- Every canonical macroblock is either a good run or a singleton transition.
This is the exact structural dichotomy used in Section 4 of the manuscript. -/
theorem macroblock_good_or_singleton {count : Nat} {cuts : Finset Nat}
    {block : List TransitionTag} (hblock : block ∈ macroblockTags count cuts) :
    GoodMacroblock block ∨ ∃ tag, block = [tag] := by
  have hne : block ≠ [] := by
    exact fun hnil => nil_not_mem_macroblockTags count cuts (hnil ▸ hblock)
  have hchain := macroblock_isChain hblock
  rcases block with _ | ⟨a, tail⟩
  · exact (hne rfl).elim
  · rcases tail with _ | ⟨b, tail⟩
    · exact Or.inr ⟨a, rfl⟩
    · apply Or.inl
      have hab : sameGoodRun a b = true := by
        have hhead := (List.isChain_cons.mp hchain).1
        simpa using hhead b
      exact goodMacroblock_of_chain
        ((sameGoodRun_eq_true_iff a b).1 hab).1 hchain

/-- In a canonical block, the number of bad tags is zero for a good block and
one otherwise. -/
theorem countP_bad_tags_of_macroblock {count : Nat} {cuts : Finset Nat}
    {block : List TransitionTag} (hblock : block ∈ macroblockTags count cuts) :
    block.countP (fun tag => tag.bad) =
      if goodMacroblockBool block then 0 else 1 := by
  by_cases hgood : GoodMacroblock block
  · have hgoodBool : goodMacroblockBool block = true :=
      (goodMacroblockBool_eq_true block).2 hgood
    simp only [hgoodBool]
    apply List.countP_eq_zero.mpr
    intro tag htag
    simp [hgood tag htag]
  · have hgoodBool : goodMacroblockBool block = false := by
      cases h : goodMacroblockBool block
      · rfl
      · exact (hgood ((goodMacroblockBool_eq_true block).1 h)).elim
    simp only [hgoodBool]
    rcases macroblock_good_or_singleton hblock with hgood' | ⟨tag, rfl⟩
    · exact (hgood hgood').elim
    · have hbad : tag.bad = true := by
        cases htag : tag.bad
        · exfalso
          apply hgood
          intro other hmem
          simp only [List.mem_singleton] at hmem
          subst other
          exact htag
        · rfl
      simp [hbad]

/-- A Boolean sequence with no adjacent true entries contains at most one more
true entry than false entries. -/
theorem countP_le_neg_countP_add_one {α : Type*} (p : α → Bool)
    (items : List α)
    (hchain : items.IsChain fun a b => p a = true → p b = false) :
    items.countP p ≤ items.countP (fun a => !p a) + 1 := by
  induction items using List.twoStepInduction with
  | nil => simp
  | singleton a =>
      cases ha : p a <;> simp [ha]
  | cons_cons a b rest ihRest ihTail =>
      have htail := hchain.tail
      have hrest := htail.tail
      cases ha : p a with
      | false =>
          have ih := ihTail b htail
          rw [List.countP_cons_of_neg (p := p) (by simp [ha])]
          rw [List.countP_cons_of_pos (p := fun x => !p x) (by simp [ha])]
          omega
      | true =>
          have hab : p b = false := by
            have hhead := (List.isChain_cons.mp hchain).1
            exact hhead b (by simp) ha
          have ih := ihRest hrest
          rw [List.countP_cons_of_pos (p := p) (by simp [ha])]
          rw [List.countP_cons_of_neg (p := fun x => !p x) (by simp [ha])]
          rw [List.countP_cons_of_neg (p := p) (by simp [hab])]
          rw [List.countP_cons_of_pos (p := fun x => !p x) (by simp [hab])]
          omega

/-- Counting false Boolean tests is the sum of their zero/one indicators. -/
theorem countP_not_eq_sum_indicator {α : Type*} (p : α → Bool)
    (items : List α) :
    items.countP (fun a => !p a) =
      (items.map fun a => if p a then 0 else 1).sum := by
  induction items with
  | nil => rfl
  | cons a items ih =>
      cases ha : p a <;> simp [ha, ih, Nat.add_comm]

/-- Consecutive canonical blocks cannot both be good. -/
theorem canonicalMacroblocks_good_chain (count : Nat) (cuts : Finset Nat) :
    (macroblockTags count cuts).IsChain fun a b =>
      goodMacroblockBool a = true → goodMacroblockBool b = false := by
  apply (macroblocks_separated count cuts).imp
  intro a b hsep ha
  cases hb : goodMacroblockBool b
  · rfl
  · exfalso
    have hgoodA : GoodMacroblock a :=
      (goodMacroblockBool_eq_true a).1 ha
    have hgoodB : GoodMacroblock b :=
      (goodMacroblockBool_eq_true b).1 hb
    rcases hsep with ⟨haNonempty, hbNonempty, hfalse⟩
    have hlast : (a.getLast haNonempty).bad = false :=
      hgoodA _ (List.getLast_mem haNonempty)
    have hhead : (b.head hbNonempty).bad = false :=
      hgoodB _ (List.head_mem hbNonempty)
    have htrue : sameGoodRun (a.getLast haNonempty)
        (b.head hbNonempty) = true :=
      (sameGoodRun_eq_true_iff _ _).2 ⟨hlast, hhead⟩
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse

/-- The number of non-good canonical blocks is exactly the number of bad tags
in the original transition list. -/
theorem countP_nonGood_macroblocks_eq_bad_tags (count : Nat)
    (cuts : Finset Nat) :
    (macroblockTags count cuts).countP (fun block =>
      !goodMacroblockBool block) =
    (transitionTags count cuts).countP (fun tag => tag.bad) := by
  let blocks := macroblockTags count cuts
  have hall : ∀ block ∈ blocks,
      block.countP (fun tag => tag.bad) =
        if goodMacroblockBool block then 0 else 1 := by
    intro block hblock
    exact countP_bad_tags_of_macroblock hblock
  calc
    blocks.countP (fun block => !goodMacroblockBool block) =
        (blocks.map fun block =>
          if goodMacroblockBool block then 0 else 1).sum :=
      countP_not_eq_sum_indicator goodMacroblockBool blocks
    _ = (blocks.map fun block =>
          block.countP (fun tag => tag.bad)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro block hblock
      exact (hall block hblock).symm
    _ = blocks.flatten.countP (fun tag => tag.bad) := by
      rw [List.countP_flatten]
    _ = (transitionTags count cuts).countP (fun tag => tag.bad) := by
      rw [show blocks.flatten = transitionTags count cuts by
        exact flatten_macroblockTags count cuts]

/-- Restricting the transition range cannot contain more bad tags than the
entire finite set of bad transition indices. -/
theorem countP_bad_transitionTags_le (count : Nat) (cuts : Finset Nat) :
    (transitionTags count cuts).countP (fun tag => tag.bad) ≤
      (badTransitions cuts).card := by
  classical
  rw [transitionTags, List.countP_map]
  change (List.range count).countP
      (fun i => decide (i ∈ badTransitions cuts)) ≤ _
  rw [List.countP_eq_length_filter]
  let selected := (List.range count).filter
    (fun i => decide (i ∈ badTransitions cuts))
  have hnodup : selected.Nodup := by
    exact List.Nodup.filter _ (@List.nodup_range count)
  have hsubset : selected.toFinset ⊆ badTransitions cuts := by
    intro i hi
    have hiList : i ∈ selected := by simpa using hi
    have hiFilter := List.mem_filter.mp hiList
    simpa using hiFilter.2
  calc
    selected.length = selected.toFinset.card :=
      (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (badTransitions cuts).card := Finset.card_le_card hsubset

/-- The actual canonical partition satisfies the manuscript's
`4|cuts| + 1` macroblock bound; no abstract partition inequality remains. -/
theorem macroblockTags_length_le_of_cuts (count : Nat) (cuts : Finset Nat) :
    (macroblockTags count cuts).length ≤ 4 * cuts.card + 1 := by
  let blocks := macroblockTags count cuts
  let goodCount := blocks.countP goodMacroblockBool
  let badCount := blocks.countP (fun block => !goodMacroblockBool block)
  have hsplit : blocks.length = goodCount + badCount := by
    calc
      blocks.length = blocks.countP goodMacroblockBool +
          blocks.countP (fun block => ¬goodMacroblockBool block) :=
        List.length_eq_countP_add_countP goodMacroblockBool
      _ = goodCount + badCount := by
        unfold goodCount badCount
        congr 1
        apply congrArg (fun q => blocks.countP q)
        funext block
        cases goodMacroblockBool block <;> rfl
  have halt : goodCount ≤ badCount + 1 := by
    exact countP_le_neg_countP_add_one goodMacroblockBool blocks
      (canonicalMacroblocks_good_chain count cuts)
  have hbadEq : badCount =
      (transitionTags count cuts).countP (fun tag => tag.bad) :=
    countP_nonGood_macroblocks_eq_bad_tags count cuts
  have hbad : badCount ≤ (badTransitions cuts).card := by
    rw [hbadEq]
    exact countP_bad_transitionTags_le count cuts
  apply macroblock_count_le_of_cuts cuts
  rw [hsplit]
  omega

@[simp] theorem transitionTag_mem_transitionTags_iff
    (count : Nat) (cuts : Finset Nat) (i : Nat) (bad : Bool) :
    (⟨i, bad⟩ : TransitionTag) ∈ transitionTags count cuts ↔
      i < count ∧ bad = decide (i ∈ badTransitions cuts) := by
  simp [transitionTags, eq_comm]

/-- Transition indices in the complete canonical tag list increase by exactly
one at every step. -/
theorem transitionTags_index_isChain (count : Nat) (cuts : Finset Nat) :
    (transitionTags count cuts).IsChain fun a b =>
      b.index = a.index + 1 := by
  unfold transitionTags
  rw [List.isChain_map]
  exact (List.isChain_range (fun a b => b = a + 1) count).2
    (fun _ _ => rfl)

/-- Every block produced by `splitBy` is a contiguous infix of the complete
tag list, hence its transition indices also increase by exactly one. -/
theorem macroblock_index_isChain {count : Nat} {cuts : Finset Nat}
    {block : List TransitionTag} (hblock : block ∈ macroblockTags count cuts) :
    block.IsChain fun a b => b.index = a.index + 1 := by
  apply (transitionTags_index_isChain count cuts).infix
  rw [← flatten_macroblockTags count cuts]
  exact List.infix_of_mem_flatten hblock

/-- Every canonical macroblock is nonempty. -/
theorem macroblock_ne_nil {count : Nat} {cuts : Finset Nat}
    {block : List TransitionTag} (hblock : block ∈ macroblockTags count cuts) :
    block ≠ [] := by
  intro hnil
  exact nil_not_mem_macroblockTags count cuts (hnil ▸ hblock)

/-- In a nonempty list whose adjacent tag indices increase by one, the tag at
position `i` has index `head.index + i`. -/
theorem transitionTag_index_getElem {block : List TransitionTag}
    (hne : block ≠ [])
    (hchain : block.IsChain fun a b => b.index = a.index + 1)
    (i : Nat) (hi : i < block.length) :
    block[i].index = (block.head hne).index + i := by
  induction block generalizing i with
  | nil => exact (hne rfl).elim
  | cons a tail ih =>
      cases i with
      | zero => rfl
      | succ i =>
          cases tail with
          | nil => simp at hi
          | cons b rest =>
              have hiTail : i < (b :: rest).length := by simpa using hi
              have htailNe : b :: rest ≠ [] := by simp
              have htailChain : (b :: rest).IsChain fun x y =>
                  y.index = x.index + 1 := hchain.tail
              have ih' := ih htailNe htailChain i hiTail
              have hab : b.index = a.index + 1 := hchain.rel
              simp only [List.getElem_cons_succ] at ih' ⊢
              simpa [hab, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih'

/-- Every tag in a canonical block belongs to the complete transition list. -/
theorem mem_transitionTags_of_mem_macroblock {count : Nat} {cuts : Finset Nat}
    {block : List TransitionTag} (hblock : block ∈ macroblockTags count cuts)
    {tag : TransitionTag} (htag : tag ∈ block) :
    tag ∈ transitionTags count cuts := by
  rw [← flatten_macroblockTags count cuts]
  exact List.mem_flatten.mpr ⟨block, hblock, htag⟩

/-- A good tag in the canonical transition list avoids the cut layer at both
ends of its transition. -/
theorem good_transition_avoids_cuts {count : Nat} {cuts : Finset Nat}
    {tag : TransitionTag} (hmem : tag ∈ transitionTags count cuts)
    (hgood : tag.bad = false) :
    tag.index ∉ cuts ∧ tag.index + 1 ∉ cuts := by
  rcases tag with ⟨i, bad⟩
  have htag := (transitionTag_mem_transitionTags_iff count cuts i bad).1 hmem
  have hdecide : decide (i ∈ badTransitions cuts) = false := by
    rw [← htag.2]
    exact hgood
  have hnotBad : i ∉ badTransitions cuts := of_decide_eq_false hdecide
  constructor
  · intro hi
    exact hnotBad (Finset.mem_union_left _ hi)
  · intro hsucc
    apply hnotBad
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i + 1, hsucc, by simp⟩

namespace Circuit

/-- A harmless total fallback used only outside the valid transition range. -/
def fallbackLayer {n w : Nat} : CircuitLayer n w :=
  fun _ => Gate.constant false

/-- The target circuit layer of a transition tag.  Canonical tags are always in
range; `getD` merely keeps the definition total for arbitrary external input. -/
def layerAfterTransition {n w : Nat} (C : Circuit n w)
    (tag : TransitionTag) : CircuitLayer n w :=
  C.layers.getD (tag.index + 1) fallbackLayer

/-- The concrete list of target layers evaluated by one macroblock. -/
def macroblockLayers {n w : Nat} (C : Circuit n w)
    (block : List TransitionTag) : List (CircuitLayer n w) :=
  block.map C.layerAfterTransition

@[simp] theorem macroblockLayers_length {n w : Nat} (C : Circuit n w)
    (block : List TransitionTag) :
    (C.macroblockLayers block).length = block.length := by
  simp [macroblockLayers]

/-- Mapping every block to its concrete target layers commutes with flattening
the canonical partition. -/
theorem flatten_macroblockLayers {n w count : Nat} (C : Circuit n w)
    (cuts : Finset Nat) :
    ((macroblockTags count cuts).map C.macroblockLayers).flatten =
      (transitionTags count cuts).map C.layerAfterTransition := by
  unfold macroblockLayers
  rw [← List.map_flatten, flatten_macroblockTags]

/-- For the actual number of between-layer transitions, the concrete tagged
layers are exactly all circuit layers after the first boundary layer. -/
theorem transitionTagLayers_eq_tail {n w : Nat} (C : Circuit n w)
    (cuts : Finset Nat) :
    (transitionTags C.layers.tail.length cuts).map C.layerAfterTransition =
      C.layers.tail := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp only [transitionTags, List.getElem_map, List.getElem_range,
      layerAfterTransition]
    have htail := hright
    have hlen : C.layers.tail.length = C.layers.length - 1 := by simp
    rw [hlen] at hright
    have hi : i + 1 < C.layers.length := by omega
    rw [List.getD_eq_getElem C.layers fallbackLayer hi]
    exact (List.getElem_tail htail).symm

/-- Hence the concrete macroblock layer lists concatenate to the exact tail of
the original circuit, with no omitted or duplicated transition. -/
theorem flatten_canonicalMacroblockLayers_eq_tail {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) :
    ((macroblockTags C.layers.tail.length cuts).map
      C.macroblockLayers).flatten = C.layers.tail := by
  rw [flatten_macroblockLayers, transitionTagLayers_eq_tail]

/-- Ordered semantic relations of all concrete macroblocks of a circuit. -/
def macroblockRelations {n w : Nat} (C : Circuit n w)
    (cuts : Finset Nat) (x : BitState n) : List (Rel (BitState w)) :=
  (macroblockTags C.layers.tail.length cuts).map fun block =>
    SegmentRelation (C.macroblockLayers block) x

/-- The composite of the concrete macroblock relations is exactly the segment
relation of every circuit layer after the initial boundary layer. -/
theorem compose_macroblockRelations_eq_tailSegment {n w : Nat}
    (C : Circuit n w) (cuts : Finset Nat) (x : BitState n) :
    Rel.composeList (C.macroblockRelations cuts x) =
      SegmentRelation C.layers.tail x := by
  unfold macroblockRelations SegmentRelation
  have hmap :
      (macroblockTags C.layers.tail.length cuts).map (fun block =>
        Rel.composeList (layerRelations (C.macroblockLayers block) x)) =
      ((macroblockTags C.layers.tail.length cuts).map (fun block =>
        layerRelations (C.macroblockLayers block) x)).map Rel.composeList := by
    simp [List.map_map, Function.comp_def]
  rw [hmap]
  rw [Rel.composeList_map_composeList]
  apply congrArg Rel.composeList
  unfold layerRelations
  have hblocksMap :
      (macroblockTags C.layers.tail.length cuts).map (fun block =>
        (C.macroblockLayers block).map fun layer => layer.transition x) =
      ((macroblockTags C.layers.tail.length cuts).map
        C.macroblockLayers).map (List.map fun layer => layer.transition x) := by
    simp [List.map_map, Function.comp_def]
  rw [hblocksMap, ← List.map_flatten,
    flatten_canonicalMacroblockLayers_eq_tail]

/-- Exact acceptance decomposition through the concrete canonical
macroblocks.  This is the proposition-level formula from Section 5, before
implementing its relation entries by target `AC⁰[m]` circuits. -/
theorem accept_cons_iff_macroblockRelations {n w : Nat}
    (first : CircuitLayer n w) (rest : List (CircuitLayer n w))
    (output : Fin w) (cuts : Finset Nat) (x : BitState n) :
    let C : Circuit n w := ⟨first :: rest, output⟩
    C.eval x = true ↔
      ∃ initial final,
        InitialStatePredicate first x initial ∧
          Rel.composeList (C.macroblockRelations cuts x) initial final ∧
            AcceptingState output final := by
  let C : Circuit n w := ⟨first :: rest, output⟩
  change evalLayers (first :: rest) x (BitState.zero w) output = true ↔ _
  rw [accept_cons_iff_exists_boundary_states]
  constructor
  · rintro ⟨initial, final, hinitial, hsegment, hfinal⟩
    refine ⟨initial, final, hinitial, ?_, hfinal⟩
    rw [compose_macroblockRelations_eq_tailSegment]
    exact hsegment
  · rintro ⟨initial, final, hinitial, hblocks, hfinal⟩
    refine ⟨initial, final, hinitial, ?_, hfinal⟩
    rw [compose_macroblockRelations_eq_tailSegment] at hblocks
    exact hblocks

/-- The actual dependency edges selected by a list of transition tags.  The
ambient vertex type is retained; vertices outside the block become isolated. -/
def macroblockGraph {n w : Nat} (C : Circuit n w)
    (block : List TransitionTag) : LayeredDigraph C.Vertex where
  edge := fun u v =>
    C.layeredGraph.edge u v ∧
      ∃ tag ∈ block, tag.index = u.1.val
  layer := C.layeredGraph.layer
  edge_next := by
    intro u v h
    exact C.layeredGraph.edge_next h.1

instance instDecidableRelMacroblockGraphEdge {n w : Nat} (C : Circuit n w)
    (block : List TransitionTag) : DecidableRel (C.macroblockGraph block).edge := by
  intro u v
  unfold macroblockGraph layeredGraph
  infer_instance

/-- A good canonical block graph is literally a spanning subgraph of the graph
remaining after deletion of all cut layers. -/
theorem macroblockGraph_toSimpleGraph_le_deleteLayers {n w count : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags count cuts)
    (hgood : GoodMacroblock block) :
    (C.macroblockGraph block).toSimpleGraph ≤
      (C.layeredGraph.deleteLayers cuts).toSimpleGraph := by
  intro u v hadj
  rcases hadj with huv | hvu
  · left
    rcases huv with ⟨hedge, tag, htagBlock, htagIndex⟩
    have htagAll : tag ∈ transitionTags count cuts := by
      rw [← flatten_macroblockTags count cuts]
      exact List.mem_flatten.mpr ⟨block, hblock, htagBlock⟩
    have havoids := good_transition_avoids_cuts htagAll
      (hgood tag htagBlock)
    refine ⟨hedge, ?_, ?_⟩
    · show u.1.val ∉ cuts
      rw [← htagIndex]
      exact havoids.1
    · show v.1.val ∉ cuts
      rw [hedge.1, ← htagIndex]
      exact havoids.2
  · right
    rcases hvu with ⟨hedge, tag, htagBlock, htagIndex⟩
    have htagAll : tag ∈ transitionTags count cuts := by
      rw [← flatten_macroblockTags count cuts]
      exact List.mem_flatten.mpr ⟨block, hblock, htagBlock⟩
    have havoids := good_transition_avoids_cuts htagAll
      (hgood tag htagBlock)
    refine ⟨hedge, ?_, ?_⟩
    · show v.1.val ∉ cuts
      rw [← htagIndex]
      exact havoids.1
    · show u.1.val ∉ cuts
      rw [hedge.1, ← htagIndex]
      exact havoids.2

/-- If the whole-layer remainder is planar, every good canonical macroblock is
planar as an actual circuit dependency subgraph. -/
theorem goodMacroblock_isPlanar {n w count : Nat}
    (C : Circuit n w) (cuts : Finset Nat) {block : List TransitionTag}
    (hremainder : OrientableGenus.IsPlanar
      (C.layeredGraph.deleteLayers cuts).toSimpleGraph)
    (hblock : block ∈ macroblockTags count cuts)
    (hgood : GoodMacroblock block) :
    OrientableGenus.IsPlanar (C.macroblockGraph block).toSimpleGraph := by
  unfold OrientableGenus.IsPlanar at hremainder ⊢
  have hmono := OrientableGenus.genus_mono
    (macroblockGraph_toSimpleGraph_le_deleteLayers C cuts hblock hgood)
  omega

end Circuit
end Allender
