import Allender.FiniteState
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Counting intermediate state sequences

The explicit composition construction enumerates assignments to intermediate
boundary states. Since the width is fixed, a logarithmic block has only
polynomially many such assignments.
-/

namespace Allender

/-- Assignments of width-`w` states to `L` intermediate positions. -/
abbrev StateAssignments (w L : Nat) := Fin L → BitState w

/-- Exact number of intermediate state assignments. -/
theorem card_stateAssignments (w L : Nat) :
    Fintype.card (StateAssignments w L) = (2 ^ w) ^ L := by
  calc
    Fintype.card (StateAssignments w L) = Fintype.card (BitState w) ^ L :=
      Fintype.card_pi_const (BitState w) L
    _ = (2 ^ w) ^ L := by rw [BitState.card]

/-- For `L = log₂(n+2)`, enumeration of intermediate states is polynomial in `n`. -/
theorem card_stateAssignments_log_le (w n : Nat) :
    Fintype.card (StateAssignments w (Nat.log 2 (n + 2))) ≤ (n + 2) ^ w := by
  rw [card_stateAssignments]
  have hbase : 2 ^ Nat.log 2 (n + 2) ≤ n + 2 :=
    Nat.pow_log_le_self 2 (by omega)
  calc
    (2 ^ w) ^ Nat.log 2 (n + 2) =
        (2 ^ Nat.log 2 (n + 2)) ^ w := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (n + 2) ^ w := Nat.pow_le_pow_left hbase w

end Allender
