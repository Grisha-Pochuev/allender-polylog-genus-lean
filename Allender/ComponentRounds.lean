import Allender.Halving
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Global component rounds

The local median-cut theorem gives one half-size inequality for every child
component.  This file assembles those inequalities into the global round
argument from Lemma 3.1: every component in round `t+1` has an active parent in
round `t`, so no positive component can remain after `log₂ N + 1` rounds.
-/

namespace Allender

/--
An abstract system of active components through a fixed number of rounds.
Component identifiers live in one finite ambient type; membership in `active t`
records which identifiers occur in round `t`.
-/
structure ComponentRoundSystem (α : Type*) [DecidableEq α]
    (steps N : Nat) where
  active : Nat → Finset α
  size : Nat → α → Nat
  parent : Nat → α → α
  initial_bound : ∀ c ∈ active 0, size 0 c ≤ N
  positive : ∀ t, t ≤ steps → ∀ c ∈ active t, 0 < size t c
  parent_active : ∀ t, t < steps → ∀ c ∈ active (t + 1),
    parent t c ∈ active t
  halves : ∀ t, t < steps → ∀ c ∈ active (t + 1),
    2 * size (t + 1) c ≤ size t (parent t c)

namespace ComponentRoundSystem

variable {α : Type*} [DecidableEq α] {steps N : Nat}

/-- Every round-`t` component satisfies the accumulated `2^t` size bound. -/
theorem pow_mul_size_le (S : ComponentRoundSystem α steps N) :
    ∀ t, t ≤ steps → ∀ c ∈ S.active t,
      2 ^ t * S.size t c ≤ N := by
  intro t ht
  induction t with
  | zero =>
      intro c hc
      simpa using S.initial_bound c hc
  | succ t ih =>
      intro c hc
      have hlt : t < steps := Nat.lt_of_succ_le ht
      let p := S.parent t c
      have hp : p ∈ S.active t := S.parent_active t hlt c (by simpa using hc)
      have hparent : 2 ^ t * S.size t p ≤ N := ih hlt.le p hp
      have hhalf : 2 * S.size (t + 1) c ≤ S.size t p :=
        S.halves t hlt c (by simpa using hc)
      calc
        2 ^ (t + 1) * S.size (t + 1) c =
            2 ^ t * (2 * S.size (t + 1) c) := by ring
        _ ≤ 2 ^ t * S.size t p := Nat.mul_le_mul_left _ hhalf
        _ ≤ N := hparent

/-- After `log₂ N + 1` rounds the active-component set is empty. -/
theorem active_empty_after_log
    (S : ComponentRoundSystem α (Nat.log 2 N + 1) N) :
    S.active (Nat.log 2 N + 1) = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hbound :
      2 ^ (Nat.log 2 N + 1) * S.size (Nat.log 2 N + 1) c ≤ N :=
    S.pow_mul_size_le (Nat.log 2 N + 1) le_rfl c hc
  have hpositive : 0 < S.size (Nat.log 2 N + 1) c :=
    S.positive (Nat.log 2 N + 1) le_rfl c hc
  have hone : 1 ≤ S.size (Nat.log 2 N + 1) c := hpositive
  have hpow_le_product :
      2 ^ (Nat.log 2 N + 1) ≤
        2 ^ (Nat.log 2 N + 1) * S.size (Nat.log 2 N + 1) c := by
    calc
      2 ^ (Nat.log 2 N + 1) = 2 ^ (Nat.log 2 N + 1) * 1 := by simp
      _ ≤ 2 ^ (Nat.log 2 N + 1) * S.size (Nat.log 2 N + 1) c :=
        Nat.mul_le_mul_left _ hone
  have hpow_le_N : 2 ^ (Nat.log 2 N + 1) ≤ N :=
    hpow_le_product.trans hbound
  have hN_lt_pow : N < 2 ^ (Nat.log 2 N + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (b := 2) (by omega) N)
  omega

end ComponentRoundSystem
end Allender
