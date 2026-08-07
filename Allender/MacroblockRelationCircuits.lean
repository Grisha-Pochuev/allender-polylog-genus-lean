import Allender.BadBlockRelations
import Allender.GoodBlockRelations

/-!
# One target relation circuit for every canonical macroblock

Good blocks use the common Hansen simulation.  Every remaining canonical
block is proved to be a singleton and uses the direct one-transition circuit.
The resulting construction covers the original ordered macroblock list.
-/

namespace Allender
namespace Circuit

/-- Locate a known good canonical block in the filtered good-block list. -/
noncomputable def goodBlockIndex {n w : Nat} (C : Circuit n w)
    (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (hgood : GoodMacroblock block) : Fin (C.goodMacroblocks cuts).length := by
  classical
  let hmem : block ∈ C.goodMacroblocks cuts := by
    rw [goodMacroblocks, List.mem_filter]
    exact ⟨hblock, (goodMacroblockBool_eq_true block).2 hgood⟩
  exact ⟨List.idxOf block (C.goodMacroblocks cuts),
    List.idxOf_lt_length_iff.mpr hmem⟩

@[simp] theorem get_goodBlockIndex {n w : Nat} (C : Circuit n w)
    (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (hgood : GoodMacroblock block) :
    (C.goodMacroblocks cuts).get (C.goodBlockIndex cuts hblock hgood) = block := by
  classical
  exact List.getElem_idxOf _

/-- The unique tag selected from a canonical block known not to be good. -/
noncomputable def badBlockTag {n w : Nat} (C : Circuit n w)
    (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (hnot : ¬ GoodMacroblock block) : TransitionTag :=
  Classical.choose ((macroblock_good_or_singleton hblock).resolve_left hnot)

theorem badBlock_eq_singleton {n w : Nat} (C : Circuit n w)
    (cuts : Finset Nat) {block : List TransitionTag}
    (hblock : block ∈ macroblockTags C.layers.tail.length cuts)
    (hnot : ¬ GoodMacroblock block) :
    block = [C.badBlockTag cuts hblock hnot] :=
  Classical.choose_spec ((macroblock_good_or_singleton hblock).resolve_left hnot)

end Circuit

namespace PlanarizedFamily

/-- Target circuit for one entry of one block in the original canonical
macroblock list. -/
noncomputable def macroblockRelationCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (b : Fin (macroblockTags (F.circuit n).layers.tail.length
      (P.cuts n)).length)
    (initial final : BitState F.width) : PackedACmCircuit m n := by
  let block := (macroblockTags (F.circuit n).layers.tail.length
    (P.cuts n)).get b
  have hblock : block ∈ macroblockTags (F.circuit n).layers.tail.length
      (P.cuts n) := List.get_mem _ _
  by_cases hgood : GoodMacroblock block
  · exact P.goodRelationCircuit A hn
      ((F.circuit n).goodBlockIndex (P.cuts n) hblock hgood) initial final
  · let tag := (F.circuit n).badBlockTag (P.cuts n) hblock hgood
    exact ((F.circuit n).layerAfterTransition tag).relationCircuit m initial final

/-- Every selected circuit recognizes exactly its concrete macroblock relation
entry. -/
theorem macroblockRelationCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n)
    (b : Fin (macroblockTags (F.circuit n).layers.tail.length
      (P.cuts n)).length)
    (initial final : BitState F.width) (x : BitState n) :
    (P.macroblockRelationCircuit A hn b initial final).circuit.eval x = true ↔
      SegmentRelation
        ((F.circuit n).macroblockLayers
          ((macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).get b))
        x initial final := by
  let block := (macroblockTags (F.circuit n).layers.tail.length
    (P.cuts n)).get b
  have hblock : block ∈ macroblockTags (F.circuit n).layers.tail.length
      (P.cuts n) := List.get_mem _ _
  unfold macroblockRelationCircuit
  dsimp only
  by_cases hgoodActual : GoodMacroblock
      ((macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).get b)
  · rw [dif_pos hgoodActual]
    have hblockActual :
        (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).get b ∈
          macroblockTags (F.circuit n).layers.tail.length (P.cuts n) :=
      List.get_mem _ _
    have hrel := P.goodRelationCircuit_eval_iff A hsim hn
      ((F.circuit n).goodBlockIndex (P.cuts n) hblockActual hgoodActual)
      initial final x
    rw [Circuit.get_goodBlockIndex] at hrel
    exact hrel
  · rw [dif_neg hgoodActual]
    have hblockActual :
        (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).get b ∈
          macroblockTags (F.circuit n).layers.tail.length (P.cuts n) :=
      List.get_mem _ _
    let tag := (F.circuit n).badBlockTag (P.cuts n) hblockActual hgoodActual
    have hsingleton :
        (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).get b = [tag] :=
      (F.circuit n).badBlock_eq_singleton (P.cuts n)
        hblockActual hgoodActual
    have hblockeq : block = [tag] := by simpa [block] using hsingleton
    rw [show (F.circuit n).macroblockLayers block =
        [(F.circuit n).layerAfterTransition tag] by
      rw [hblockeq]
      rfl]
    exact ((F.circuit n).layerAfterTransition tag).relationCircuit_eval_iff
      m initial final x

/-- Uniform depth bound for every canonical macroblock relation entry. -/
theorem macroblockRelationCircuit_depth_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (b : Fin (macroblockTags (F.circuit n).layers.tail.length
      (P.cuts n)).length)
    (initial final : BitState F.width) (D : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D) :
    (P.macroblockRelationCircuit A hn b initial final).circuit.depth ≤
      D + 4 := by
  let block := (macroblockTags (F.circuit n).layers.tail.length
    (P.cuts n)).get b
  have hblock : block ∈ macroblockTags (F.circuit n).layers.tail.length
      (P.cuts n) := List.get_mem _ _
  unfold macroblockRelationCircuit
  dsimp only
  by_cases hgoodActual : GoodMacroblock
      ((macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).get b)
  · rw [dif_pos hgoodActual]
    exact (P.goodRelationCircuit_depth_le A hn _ initial final D hdepth).trans
      (by omega)
  · rw [dif_neg hgoodActual]
    exact (((F.circuit n).layerAfterTransition
      ((F.circuit n).badBlockTag (P.cuts n)
        (List.get_mem _ _) hgoodActual)).relationCircuit_depth_le
          m initial final).trans (by omega)

/-- A common numerical gate-count bound covering both good blocks and the
direct singleton implementation of bad blocks. -/
def macroblockRelationSizeBound (w D S : Nat) : Nat :=
  (D + 3) * (w * (S + 1) + 1) + 4 * (w + 1)

theorem macroblockRelationCircuit_size_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (b : Fin (macroblockTags (F.circuit n).layers.tail.length
      (P.cuts n)).length)
    (initial final : BitState F.width) (D S : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D)
    (hsize : ∀ t, (A.circuit n t).size ≤ S) :
    (P.macroblockRelationCircuit A hn b initial final).circuit.size ≤
      macroblockRelationSizeBound F.width D S := by
  let block := (macroblockTags (F.circuit n).layers.tail.length
    (P.cuts n)).get b
  have hblock : block ∈ macroblockTags (F.circuit n).layers.tail.length
      (P.cuts n) := List.get_mem _ _
  unfold macroblockRelationCircuit
  dsimp only
  by_cases hgoodActual : GoodMacroblock
      ((macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).get b)
  · rw [dif_pos hgoodActual]
    exact (P.goodRelationCircuit_size_le A hn _ initial final D S
      hdepth hsize).trans (Nat.le_add_right _ _)
  · rw [dif_neg hgoodActual]
    exact ((((F.circuit n).layerAfterTransition
      ((F.circuit n).badBlockTag (P.cuts n)
        (List.get_mem _ _) hgoodActual)).relationCircuit_size_le
          m initial final).trans (Nat.le_add_left _ _))

end PlanarizedFamily
end Allender
