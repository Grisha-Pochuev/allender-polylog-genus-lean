import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Additive genus budgets

The separator argument uses genus additivity only through a numerical
consequence: if every active nonplanar component has positive integer genus and
their genus sum is at most `g`, then there are at most `g` such components.
This file proves that consequence and the resulting bound over many rounds.
-/

namespace Allender

open scoped BigOperators

/-- A finite set of positive-cost objects has cardinality at most its total cost budget. -/
theorem card_le_of_positive_cost_sum_le {α : Type*} [DecidableEq α]
    (components : Finset α) (cost : α → Nat) {g : Nat}
    (hpositive : ∀ c ∈ components, 1 ≤ cost c)
    (hbudget : ∑ c in components, cost c ≤ g) :
    components.card ≤ g := by
  calc
    components.card = ∑ _c in components, 1 := by simp
    _ ≤ ∑ c in components, cost c := by
      exact Finset.sum_le_sum fun c hc => hpositive c hc
    _ ≤ g := hbudget

/-- If each round selects at most `g` layers, the sum of round counts is bounded by `g` times the number of rounds. -/
theorem sum_le_mul_length_of_each_le (counts : List Nat) (g : Nat)
    (hcounts : ∀ x ∈ counts, x ≤ g) :
    counts.sum ≤ g * counts.length := by
  induction counts with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ g := hcounts x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ g := by
        intro y hy
        exact hcounts y (by simp [hy])
      have htail := ih hxs
      simp only [List.sum_cons, List.length_cons]
      omega

/-- The exact quantitative layer bound used by the paper. -/
theorem separator_round_count_bound (counts : List Nat) (g N : Nat)
    (hlength : counts.length ≤ Nat.log 2 N + 1)
    (hcounts : ∀ x ∈ counts, x ≤ g) :
    counts.sum ≤ g * (Nat.log 2 N + 1) := by
  exact (sum_le_mul_length_of_each_le counts g hcounts).trans
    (Nat.mul_le_mul_left g hlength)

end Allender
