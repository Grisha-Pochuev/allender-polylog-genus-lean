import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Weighted median cuts

A connected component of a layered graph determines a finite list of layer
weights.  The separator proof needs a layer for which at most half of the
component lies strictly below and at most half lies strictly above.  This file
proves that elementary finite statement.
-/

namespace Allender

/--
A cut position `k` represents deleting the layer at index `k - 1`.
The list prefix strictly before that layer and the suffix strictly after it
both have at most half of the total weight.
-/
def IsWeightedMedianCut (weights : List Nat) (k : Nat) : Prop :=
  1 ≤ k ∧
  k ≤ weights.length ∧
  2 * (weights.take (k - 1)).sum ≤ weights.sum ∧
  2 * (weights.drop k).sum ≤ weights.sum

/-- Every nonempty finite list of natural weights has a weighted median cut. -/
theorem exists_weightedMedianCut (weights : List Nat) (hne : weights ≠ []) :
    ∃ k, IsWeightedMedianCut weights k := by
  classical
  let P : Nat → Prop := fun k =>
    1 ≤ k ∧ k ≤ weights.length ∧ weights.sum ≤ 2 * (weights.take k).sum
  have hlen : 1 ≤ weights.length := by
    have hpos : 0 < weights.length := List.length_pos_of_ne_nil hne
    omega
  have hex : ∃ k, P k := by
    refine ⟨weights.length, hlen, le_rfl, ?_⟩
    simp only [List.take_length]
    omega
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  refine ⟨k, hk.1, hk.2.1, ?_, ?_⟩
  · by_cases hkone : k = 1
    · simp [hkone]
    · have hkpred_lt : k - 1 < k := by omega
      have hnotP : ¬P (k - 1) := Nat.find_min hex hkpred_lt
      have hkpred_one : 1 ≤ k - 1 := by omega
      have hkpred_len : k - 1 ≤ weights.length := by omega
      have hnotCross : ¬weights.sum ≤ 2 * (weights.take (k - 1)).sum := by
        intro hcross
        exact hnotP ⟨hkpred_one, hkpred_len, hcross⟩
      omega
  · have hsplit :
        (weights.take k).sum + (weights.drop k).sum = weights.sum := by
      simpa using congrArg List.sum (List.take_append_drop k weights)
    omega

end Allender
