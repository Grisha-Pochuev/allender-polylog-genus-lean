import Allender.LayerSeparationProcess
import Allender.OrientableGenus
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Conditional global layer planarization

This module packages the last logical part of the layer-separator argument. A
`LayerSeparationProcess` already contains finite connected sets, median cuts,
parent relations, and the local half-size proofs.

The genuinely missing graph-theoretic bridge is represented explicitly rather
than hidden as a planarization axiom:

* every initially nonplanar component is represented by an active component;
* representation is preserved locally from one cut round to the next.

Lean then iterates this local preservation, proves that no nonplanar component
survives `log₂ N + 1` rounds, and bounds the number of distinct deleted layers
by `g * (log₂ N + 1)`.

The construction of the initial and stepwise coverage maps from the canonical
connected components of the remainder is not proved in this module. Thus the
main planarization theorem below is explicitly conditional on
`PlanarizationCoverage`; it is not yet the unconditional Lemma 3.1 of the
manuscript.
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
          Finset.card_union_le (S.cumulativeCuts t) (S.roundCuts t)
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
Coverage at one round: every actual nonplanar component of the current
remainder is represented by a distinct active component identifier.
-/
structure RoundCoverage
    (S : G.LayerSeparationProcess α steps N g) (t : Nat) where
  represent : S.RemainderNonplanar t → S.ActiveAt t
  injective : Function.Injective represent

/--
Inductive coverage data. The initial map and one-step preservation are the
precise remaining graph-component obligations.
-/
structure PlanarizationCoverage
    (S : G.LayerSeparationProcess α steps N g) where
  initial : S.RoundCoverage 0
  step : ∀ t, t < steps → S.RoundCoverage t → S.RoundCoverage (t + 1)

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

/-- Iterate the local coverage-preservation law through any valid round. -/
def at {S : G.LayerSeparationProcess α steps N g}
    (C : S.PlanarizationCoverage) :
    (t : Nat) → t ≤ steps → S.RoundCoverage t
  | 0, _ => C.initial
  | t + 1, ht =>
      let hlt : t < steps := Nat.lt_of_succ_le ht
      C.step t hlt (at C t hlt.le)

/--
After logarithmically many locally covered rounds, the actual remainder is
planar. This theorem is conditional on the explicit initial and stepwise
coverage obligations above.
-/
theorem final_isPlanar_of_coverage
    (S : G.LayerSeparationProcess α (Nat.log 2 N + 1) N g)
    (C : S.PlanarizationCoverage) :
    OrientableGenus.IsPlanar
      ((G.deleteLayers
        (S.cumulativeCuts (Nat.log 2 N + 1))).toSimpleGraph) := by
  let T := Nat.log 2 N + 1
  have hactive : S.active T = ∅ := by
    simpa [T] using S.active_empty_after_log
  have hle := (C.at T le_rfl).nonplanar_card_le_active_card
  rw [hactive] at hle
  have hcard :
      (OrientableGenus.nonplanarComponents
        ((G.deleteLayers (S.cumulativeCuts T)).toSimpleGraph)).card = 0 := by
    simpa using hle
  have hempty :
      OrientableGenus.nonplanarComponents
        ((G.deleteLayers (S.cumulativeCuts T)).toSimpleGraph) = ∅ :=
    Finset.card_eq_zero.mp hcard
  have hplanarT :
      OrientableGenus.IsPlanar
        ((G.deleteLayers (S.cumulativeCuts T)).toSimpleGraph) :=
    (OrientableGenus.isPlanar_iff_nonplanarComponents_eq_empty
      ((G.deleteLayers (S.cumulativeCuts T)).toSimpleGraph)).2 hempty
  simpa [T] using hplanarT

/-- The final separation process deletes at most `g(log₂ N + 1)` layers. -/
theorem final_cuts_card_le
    (S : G.LayerSeparationProcess α (Nat.log 2 N + 1) N g) :
    (S.cumulativeCuts (Nat.log 2 N + 1)).card ≤
      g * (Nat.log 2 N + 1) :=
  S.cumulativeCuts_card_le_mul _ le_rfl

end PlanarizationCoverage
end LayerSeparationProcess
end LayeredDigraph
end Allender
