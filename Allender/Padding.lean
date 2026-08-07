import Mathlib.Tactic

/-!
# Padding all block circuits into one family

The `t`-th block-output circuit at input length `n` is encoded at
`N(n,t)=(n+1)^(d+2)+t`.  The shift by one is essential: a polynomial batch can
have more than one member at input length one, while `1^d=1` for every `d`.
This file verifies that the resulting ranges are disjoint whenever
`t<(n+1)^d`.
-/

namespace Allender

/-- Padded input length used to combine all block circuits into one family. -/
def paddedLength (d n t : Nat) : Nat := (n + 1) ^ (d + 2) + t

/-- The gap between consecutive base lengths is larger than `n^d`. -/
theorem padding_gap (d n : Nat) (hn : 1 ≤ n) :
    n ^ (d + 2) + n ^ d < (n + 1) ^ (d + 2) := by
  have hpow : n ^ d ≤ (n + 1) ^ d :=
    Nat.pow_le_pow_left (Nat.le_succ n) d
  have hquad : n ^ 2 + 1 < (n + 1) ^ 2 := by
    nlinarith
  calc
    n ^ (d + 2) + n ^ d = n ^ d * (n ^ 2 + 1) := by ring
    _ ≤ (n + 1) ^ d * (n ^ 2 + 1) := Nat.mul_le_mul_right _ hpow
    _ < (n + 1) ^ d * (n + 1) ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hquad (Nat.pow_pos (by omega))
    _ = (n + 1) ^ (d + 2) := by ring

/-- Padding ranges for distinct positive input lengths cannot overlap. -/
theorem paddedLength_injective_on_ranges {d n m t s : Nat}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ht : t < (n + 1) ^ d) (hs : s < (m + 1) ^ d)
    (heq : paddedLength d n t = paddedLength d m s) :
    n = m ∧ t = s := by
  have hnm : n = m := by
    rcases lt_trichotomy n m with hlt | he | hgt
    · have hsucc : n + 1 ≤ m := by omega
      have hbaseMono : (n + 2) ^ (d + 2) ≤ (m + 1) ^ (d + 2) :=
        Nat.pow_le_pow_left (by omega) _
      have hleft : paddedLength d n t < (n + 2) ^ (d + 2) := by
        unfold paddedLength
        exact (Nat.add_lt_add_left ht _).trans (padding_gap d (n + 1) (by omega))
      have hright : (n + 2) ^ (d + 2) ≤ paddedLength d m s := by
        unfold paddedLength
        exact hbaseMono.trans (Nat.le_add_right _ _)
      rw [heq] at hleft
      exact (Nat.not_lt_of_ge hright hleft).elim
    · exact he
    · have hsucc : m + 1 ≤ n := by omega
      have hbaseMono : (m + 2) ^ (d + 2) ≤ (n + 1) ^ (d + 2) :=
        Nat.pow_le_pow_left (by omega) _
      have hleft : paddedLength d m s < (m + 2) ^ (d + 2) := by
        unfold paddedLength
        exact (Nat.add_lt_add_left hs _).trans (padding_gap d (m + 1) (by omega))
      have hright : (m + 2) ^ (d + 2) ≤ paddedLength d n t := by
        unfold paddedLength
        exact hbaseMono.trans (Nat.le_add_right _ _)
      rw [← heq] at hleft
      exact (Nat.not_lt_of_ge hright hleft).elim
  subst m
  constructor
  · rfl
  · unfold paddedLength at heq
    exact Nat.add_left_cancel heq

end Allender
