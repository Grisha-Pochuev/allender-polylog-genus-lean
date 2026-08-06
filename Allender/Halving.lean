import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Halving chains

This file isolates the quantitative core of the layer-separator recursion.
If every surviving nonempty descendant has at most half the size of its parent,
then no positive-size descendant can remain after `Nat.log 2 N + 1` rounds.
-/

namespace Allender

/--
`HalvingChain start rounds terminal` records a chain of component sizes starting
at `start`, ending at `terminal`, and taking `rounds` steps, with each child at
most half the size of its parent.
-/
inductive HalvingChain : Nat → Nat → Nat → Prop
  | nil (n : Nat) : HalvingChain n 0 n
  | cons {parent child rounds terminal : Nat}
      (step : 2 * child ≤ parent)
      (tail : HalvingChain child rounds terminal) :
      HalvingChain parent (rounds + 1) terminal

namespace HalvingChain

/-- After `r` halving steps, `2^r` times the terminal size is bounded by the start. -/
theorem pow_mul_terminal_le {start rounds terminal : Nat}
    (h : HalvingChain start rounds terminal) :
    2 ^ rounds * terminal ≤ start := by
  induction h with
  | nil n => simp
  | @cons parent child rounds terminal hstep htail ih =>
      calc
        2 ^ (rounds + 1) * terminal = 2 * (2 ^ rounds * terminal) := by ring
        _ ≤ 2 * child := Nat.mul_le_mul_left 2 ih
        _ ≤ parent := hstep

/-- A chain of `log₂ N + 1` halvings starting below `N` must end at zero. -/
theorem terminal_eq_zero_of_start_le {start N terminal : Nat}
    (h : HalvingChain start (Nat.log 2 N + 1) terminal)
    (hstart : start ≤ N) :
    terminal = 0 := by
  by_contra hterminal
  have hone : 1 ≤ terminal := Nat.one_le_iff_ne_zero.mpr hterminal
  have hpow_mul : 2 ^ (Nat.log 2 N + 1) * terminal ≤ start :=
    pow_mul_terminal_le h
  have hpow_le_mul :
      2 ^ (Nat.log 2 N + 1) ≤ 2 ^ (Nat.log 2 N + 1) * terminal := by
    calc
      2 ^ (Nat.log 2 N + 1) = 2 ^ (Nat.log 2 N + 1) * 1 := by simp
      _ ≤ 2 ^ (Nat.log 2 N + 1) * terminal :=
        Nat.mul_le_mul_left _ hone
  have hpow_le_N : 2 ^ (Nat.log 2 N + 1) ≤ N :=
    hpow_le_mul.trans (hpow_mul.trans hstart)
  have hN_lt_pow : N < 2 ^ (Nat.log 2 N + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (b := 2) (by omega) N)
  omega

/-- Positive terminal size is impossible after `log₂ N + 1` halving rounds. -/
theorem no_positive_terminal_after_log {start N terminal : Nat}
    (h : HalvingChain start (Nat.log 2 N + 1) terminal)
    (hstart : start ≤ N)
    (hterminal : 0 < terminal) : False := by
  have hz := terminal_eq_zero_of_start_le h hstart
  omega

end HalvingChain
end Allender
