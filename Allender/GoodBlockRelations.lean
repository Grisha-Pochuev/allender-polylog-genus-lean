import Allender.ACC0Closure
import Allender.GoodBlockBatch

/-!
# Target circuits for complete good-macroblock relation entries

The simultaneous Hansen batch supplies one target circuit for each output bit.
Here those bits are negated when necessary and conjoined, producing the exact
predicate that a fixed incoming boundary state is sent to a fixed outgoing
boundary state.
-/

namespace Allender
namespace PlanarizedFamily

/-- Package the target circuit for one output coordinate of one good block. -/
noncomputable def goodOutputCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial : BitState F.width) (output : Fin F.width) :
    PackedACmCircuit m n := by
  let entry : P.GoodEntry n := (block, initial, output)
  let index := P.goodIndexOfEntry hn entry
  exact ⟨A.width n index, A.circuit n index⟩

/-- The packed output circuit computes exactly the corresponding coordinate
of the concrete macroblock transition. -/
theorem goodOutputCircuit_eval (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial : BitState F.width) (output : Fin F.width) (x : BitState n) :
    (P.goodOutputCircuit A hn block initial output).circuit.eval x =
      evalLayers
        ((F.circuit n).macroblockLayers
          (((F.circuit n).goodMacroblocks (P.cuts n)).get block))
        x initial output := by
  let entry : P.GoodEntry n := (block, initial, output)
  let index := P.goodIndexOfEntry hn entry
  have h := hsim n index x
  change (A.circuit n index).eval x =
    ((F.circuit n).fixedBoundaryMacroblockCircuit
      (((F.circuit n).goodMacroblocks (P.cuts n)).get
        (P.goodEntryOfIndex index).1)
      (P.goodEntryOfIndex index).2.1
      (P.goodEntryOfIndex index).2.2).eval x at h
  rw [show P.goodEntryOfIndex index = entry by
    exact P.goodEntryOfIndex_goodIndexOfEntry hn entry] at h
  rw [Circuit.fixedBoundaryMacroblockCircuit_eval] at h
  change (A.circuit n index).eval x = _
  simpa [goodOutputCircuit, entry, index] using h

/-- The selected output circuit inherits a common Hansen depth bound. -/
theorem goodOutputCircuit_depth_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial : BitState F.width) (output : Fin F.width) (D : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D) :
    (P.goodOutputCircuit A hn block initial output).circuit.depth ≤ D := by
  exact hdepth n (P.goodIndexOfEntry hn (block, initial, output))

/-- The selected output circuit inherits a common pointwise size bound. -/
theorem goodOutputCircuit_size_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial : BitState F.width) (output : Fin F.width) (S : Nat)
    (hsize : ∀ t, (A.circuit n t).size ≤ S) :
    (P.goodOutputCircuit A hn block initial output).circuit.size ≤ S := by
  exact hsize (P.goodIndexOfEntry hn (block, initial, output))

/-- Select the positive or negated output-bit circuit according to the desired
outgoing boundary state. -/
noncomputable def goodRequiredBitCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (j : Fin F.width) :
    PackedACmCircuit m n :=
  let outputCircuit := (P.goodOutputCircuit A hn block initial j).normalize
  if final j then outputCircuit else outputCircuit.not

/-- One required output literal has controlled depth after normalization. -/
theorem goodRequiredBitCircuit_depth_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (j : Fin F.width) (D : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D) :
    (P.goodRequiredBitCircuit A hn block initial final j).circuit.depth ≤
      D + 2 := by
  unfold goodRequiredBitCircuit
  dsimp only
  by_cases hfinal : final j = true
  · rw [if_pos hfinal]
    exact (PackedACmCircuit.normalize_depth_le _).trans
      (Nat.add_le_add_right
        (P.goodOutputCircuit_depth_le A hn block initial j D hdepth) 1)
        |>.trans (by omega)
  · rw [if_neg hfinal, PackedACmCircuit.not_depth]
    exact Nat.add_le_add_right
      ((PackedACmCircuit.normalize_depth_le _).trans
        (Nat.add_le_add_right
          (P.goodOutputCircuit_depth_le A hn block initial j D hdepth) 1)) 1

/-- Normalization controls the padded width by the genuine gate count. -/
theorem goodRequiredBitCircuit_width_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (j : Fin F.width) (S : Nat)
    (hsize : ∀ t, (A.circuit n t).size ≤ S) :
    (P.goodRequiredBitCircuit A hn block initial final j).width ≤ S + 1 := by
  unfold goodRequiredBitCircuit
  dsimp only
  by_cases hfinal : final j = true
  · rw [if_pos hfinal]
    exact (PackedACmCircuit.normalize_width_le _).trans
      (Nat.add_le_add_right
        (P.goodOutputCircuit_size_le A hn block initial j S hsize) 1)
  · rw [if_neg hfinal, PackedACmCircuit.not_width]
    exact (PackedACmCircuit.normalize_width_le _).trans
      (Nat.add_le_add_right
        (P.goodOutputCircuit_size_le A hn block initial j S hsize) 1)

/-- Conjoin all required output coordinates. -/
noncomputable def goodRelationCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) : PackedACmCircuit m n :=
  PackedACmCircuit.conjoinParallel
    (List.ofFn fun j => P.goodRequiredBitCircuit A hn block initial final j)

/-- A complete good-block relation entry has constant additive depth. -/
theorem goodRelationCircuit_depth_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (D : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D) :
    (P.goodRelationCircuit A hn block initial final).circuit.depth ≤ D + 3 := by
  apply PackedACmCircuit.conjoinParallel_depth_le _ (D + 2)
  rw [List.forall_mem_ofFn_iff]
  intro j
  exact P.goodRequiredBitCircuit_depth_le A hn block initial final j D hdepth

/-- A complete good-block relation entry has an explicit padded-width bound. -/
theorem goodRelationCircuit_width_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (S : Nat)
    (hsize : ∀ t, (A.circuit n t).size ≤ S) :
    (P.goodRelationCircuit A hn block initial final).width ≤
      F.width * (S + 1) + 1 := by
  calc
    (P.goodRelationCircuit A hn block initial final).width ≤
        ((List.ofFn fun j =>
          P.goodRequiredBitCircuit A hn block initial final j).map
            PackedACmCircuit.width).sum + 1 :=
      PackedACmCircuit.conjoinParallel_width_le _
    _ ≤ F.width * (S + 1) + 1 := by
      apply Nat.add_le_add_right
      apply (sum_le_mul_length_of_each_le _ (S + 1) ?_).trans
      · simp [Nat.mul_comm]
      · rw [List.forall_mem_map, List.forall_mem_ofFn_iff]
        intro j
        exact P.goodRequiredBitCircuit_width_le A hn block initial final j S hsize

/-- Gate-count consequence of the preceding depth and width estimates. -/
theorem goodRelationCircuit_size_le (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (D S : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D)
    (hsize : ∀ t, (A.circuit n t).size ≤ S) :
    (P.goodRelationCircuit A hn block initial final).circuit.size ≤
      (D + 3) * (F.width * (S + 1) + 1) := by
  exact Nat.mul_le_mul
    (P.goodRelationCircuit_depth_le A hn block initial final D hdepth)
    (P.goodRelationCircuit_width_le A hn block initial final S hsize)

/-- Exact correctness of the complete relation-entry circuit. -/
theorem goodRelationCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (x : BitState n) :
    (P.goodRelationCircuit A hn block initial final).circuit.eval x = true ↔
      SegmentRelation
        ((F.circuit n).macroblockLayers
          (((F.circuit n).goodMacroblocks (P.cuts n)).get block))
        x initial final := by
  rw [segmentRelation_iff_eval]
  rw [goodRelationCircuit,
    PackedACmCircuit.conjoinParallel_eval_eq_true_iff]
  rw [List.forall_mem_ofFn_iff]
  let result := evalLayers
    ((F.circuit n).macroblockLayers
      (((F.circuit n).goodMacroblocks (P.cuts n)).get block)) x initial
  constructor
  · intro hall
    funext j
    cases hfinal : final j with
    | false =>
        have hj :
            (P.goodOutputCircuit A hn block initial j).circuit.eval x = false := by
          have := hall j
          change (if final j = true then
              (P.goodOutputCircuit A hn block initial j).normalize
            else (P.goodOutputCircuit A hn block initial j).normalize.not).circuit.eval x = true at this
          rw [if_neg (by simp [hfinal])] at this
          rw [PackedACmCircuit.not_eval_eq_true_iff] at this
          simpa using this
        rw [P.goodOutputCircuit_eval A hsim hn block initial j x] at hj
        simpa [result, hfinal] using hj.symm
    | true =>
        have hj :
            (P.goodOutputCircuit A hn block initial j).circuit.eval x = true := by
          have := hall j
          change (if final j = true then
              (P.goodOutputCircuit A hn block initial j).normalize
            else (P.goodOutputCircuit A hn block initial j).normalize.not).circuit.eval x = true at this
          rw [if_pos hfinal] at this
          simpa using this
        rw [P.goodOutputCircuit_eval A hsim hn block initial j x] at hj
        simpa [result, hfinal] using hj.symm
  · intro heq j
    have hj := congrFun heq j
    cases hfinal : final j with
    | false =>
        have hresult : result j = false := by
          simpa [result, hfinal] using hj.symm
        change (if final j = true then
            (P.goodOutputCircuit A hn block initial j).normalize
          else (P.goodOutputCircuit A hn block initial j).normalize.not).circuit.eval x = true
        rw [if_neg (by simp [hfinal])]
        rw [PackedACmCircuit.not_eval_eq_true_iff]
        rw [PackedACmCircuit.normalize_eval,
          P.goodOutputCircuit_eval A hsim hn block initial j x]
        simpa [result] using hresult
    | true =>
        have hresult : result j = true := by
          simpa [result, hfinal] using hj.symm
        change (if final j = true then
            (P.goodOutputCircuit A hn block initial j).normalize
          else (P.goodOutputCircuit A hn block initial j).normalize.not).circuit.eval x = true
        rw [if_pos hfinal]
        rw [PackedACmCircuit.normalize_eval,
          P.goodOutputCircuit_eval A hsim hn block initial j x]
        simpa [result] using hresult

end PlanarizedFamily
end Allender
