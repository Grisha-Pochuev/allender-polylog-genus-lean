import Allender.LayerSeparationProcess
import Allender.OrientableGenus
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Certified global layer planarization

This module packages the last purely logical part of the layer-separator
argument.  A `LayerSeparationProcess` already contains the actual finite
connected sets, median cuts, parent relation, and the local half-size proofs.
Here we additionally require a transparent coverage certificate: at each round,
every genuinely nonplanar connected component of the current remainder injects
into the active components supplied by the process.

From that certificate Lean proves that after `log₂ N + 1` rounds the remainder
is planar and that at most `g * (log₂ N + 1)` distinct layers were deleted.
The construction of the coverage certificate from the canonical connected
components of each remainder remains a separate obligation; no planarization
conclusion is assumed as a field.
-/

namespace Allender
namespace LayeredDigraph
namespace LayerSeparationProcess

open OrientableGenus

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : LayeredDigraph V} [DecidableRel G.edge]
variable {α : Type*} [DecidableEq α]
variable {steps N g : Nat}

/-- All layer indices selected before round `t`. -/
def cumulativeCuts (S : G.LayerSeparationProcess α steps N g) : Nat → Finset Nat
  | 0 => ∅
  | t + 1 => S.cumulativeCuts t ∪ S.roundCuts t

@[simp] theorem cumulativeCuts_zero
    (S : G.LayerSeparationProcess α steps N g) :
    S.cumulativeCuts 0 = ∅ := rfl

@[simp] theorem cumulativeCuts_succ
    (S : G.LayerSeparationProcess α steps N g) (t : Nat) :
    S.cumulativeCuts (t + 1) = S.cumulativeCuts t ∪ S.roundCuts t := rfl

/-- The cumulative cut set is monotone in the number of completed rounds. -/
theorem cumulativeCuts_subset_succ
    (S : G.LayerSeparationProcess α steps N g) (t : Nat) :
    S.cumulativeCuts t ⊆ S.cumulativeCuts (t + 1) := by
  intro m hm
  rw [S.cumulativeCuts_succ]
  exact Finset.mem_union_left _ hm

/-- After `t` valid rounds, at most `g * t` distinct layers have been cut. -/
theorem cumulativeCuts_card_le_mul
    (S : G.LayerSeparationProcess α steps N g) :
    ∀ t, t ≤ steps → (S.cumulativeCuts t).card ≤ g * t := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
      have htlt : t < steps := Nat.lt_of_succ_le ht
      calc
        (S.cumulativeCuts (t + 1)).card =
            (S.cumulativeCuts t ∪ S.roundCuts t).card := by rfl
        _ ≤ (S.cumulativeCuts t).card + (S.roundCuts t).card :=
          Finset.card_union_le
        _ ≤ g * t + g :=
          Nat.add_le_add (ih htlt.le) (S.roundCuts_card_le htlt)
        _ = g * (t + 1) := (Nat.mul_succ g t).symm

/-- The actual nonplanar components of the graph remaining before round `t`. -/
abbrev RemainderNonplanar
    (S : G.LayerSeparationProcess α steps N g) (t : Nat) :=
  {K // K ∈ OrientableGenus.nonplanarComponents
    ((G.deleteLayers (S.cumulativeCuts t)).toSimpleGraph)}

/-- Active component identifiers supplied by the separation process at round `t`. -/
abbrev ActiveAt
    (S : G.LayerSeparationProcess α steps N g) (t : Nat) :=
  {c // c ∈ S.active t}

/--
A non-circular coverage certificate for one round: every actual nonplanar
component of the current remainder is represented by a distinct active
component identifier.
-/
structure RoundCoverage
    (S : G.LayerSeparationProcess α steps N g) (t : Nat) where
  represent : S.RemainderNonplanar t → S.ActiveAt t
  injective : Function.Injective represent

/-- Coverage certificates for every round used by the process. -/
structure PlanarizationCoverage
    (S : G.LayerSeparationProcess α steps N g) where
  round : (t : Nat) → t ≤ steps → S.RoundCoverage t

namespace RoundCoverage

/-- Coverage bounds the number of actual nonplanar components by active ones. -/
theorem nonplanar_card_le_active_card
    {S : G.LayerSeparationProcess α steps N g} {t : Nat}
    (C : S.RoundCoverage t) :
    (OrientableGenus.nonplanarComponents
      ((G.deleteLayers (S.cumulativeCuts t)).toSimpleGraph)).card ≤
      (S.active t).card := by
  have hcard := Fintype.card_le_of_injective C.represent C.injective
  simpa [RemainderNonplanar, ActiveAt] using hcard

end RoundCoverage

namespace PlanarizationCoverage

/-- After logarithmically many certified rounds, the actual remainder is planar. -/
theorem final_isPlanar
    (S : G.LayerSeparationProcess α (Nat.log 2 N + 1) N g)
    (C : S.PlanarizationCoverage) :
    OrientableGenus.IsPlanar
      ((G.deleteLayers
        (S.cumulativeCuts (Nat.log 2 N + 1))).toSimpleGraph) := by
  let T := Nat.log 2 N + 1
  have hactive : S.active T = ∅ := by
    simpa [T] using S.active_empty_after_log
  have hle := (C.round T le_rfl).nonplanar_card_le_active_card
  rw [hactive] at hle
  have hcard :
      (OrientableGenus.nonplanarComponents
        ((G.deleteLayers (S.cumulativeCuts T)).toSimpleGraph)).card = 0 := by
    simpa using hle
  have hempty :
      OrientableGenus.nonplanarComponents
        ((G.deleteLayers (S.cumulativeCuts T)).toSimpleGraph) = ∅ :=
    Finset.card_eq_zero.mp hcard
  exact (OrientableGenus.isPlanar_iff_nonplanarComponents_eq_empty
    ((G.deleteLayers (S.cumulativeCuts T)).toSimpleGraph)).2 hempty

/-- The final certified planarization deletes at most `g(log₂ N + 1)` layers. -/
theorem final_cuts_card_le
    (S : G.LayerSeparationProcess α (Nat.log 2 N + 1) N g) :
    (S.cumulativeCuts (Nat.log 2 N + 1)).card ≤
      g * (Nat.log 2 N + 1) :=
  S.cumulativeCuts_card_le_mul _ le_rfl

end PlanarizationCoverage
end LayerSeparationProcess
end LayeredDigraph
end Allender
