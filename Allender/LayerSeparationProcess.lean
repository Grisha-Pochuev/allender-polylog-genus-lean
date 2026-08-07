import Allender.ComponentRounds
import Allender.MedianExistence
import Allender.GenusBudget

/-!
# Layer-separation processes on actual connected vertex sets

This module connects the abstract global round argument to the finite connected
components used by the layer-separator proof. Topology is not assumed here: a
process supplies the active components and parent relation, while Lean derives
all size-halving and total layer-selection bounds from the median-cut lemmas.
-/

namespace Allender
namespace LayeredDigraph

variable {V : Type*} [DecidableEq V]

/-- A finite sequence of active connected components and their median cuts. -/
structure LayerSeparationProcess (G : LayeredDigraph V)
    (α : Type*) [DecidableEq α] (steps N g : Nat) where
  active : Nat → Finset α
  component : Nat → α → G.FiniteConnectedSet
  median : (t : Nat) → (c : α) → (component t c).MedianLayer
  parent : Nat → α → α
  initial_size_le : ∀ c ∈ active 0, (component 0 c).verts.card ≤ N
  active_card_le : ∀ t, t < steps → (active t).card ≤ g
  parent_active : ∀ t, t < steps → ∀ c ∈ active (t + 1),
    parent t c ∈ active t
  child_subset : ∀ t, t < steps → ∀ c ∈ active (t + 1),
    (component (t + 1) c).verts ⊆ (component t (parent t c)).verts
  child_avoids : ∀ t, t < steps → ∀ c ∈ active (t + 1),
    ∀ v ∈ (component (t + 1) c).verts,
      G.layer v ≠ (median t (parent t c)).index

namespace LayerSeparationProcess

variable {G : LayeredDigraph V} {α : Type*} [DecidableEq α]
variable {steps N g : Nat}

/-- A supplied child is a descendant after its parent's median cut. -/
def childDescendant (S : G.LayerSeparationProcess α steps N g)
    {t : Nat} (ht : t < steps) {c : α} (hc : c ∈ S.active (t + 1)) :
    (S.component t (S.parent t c)).DescendantAfterCut
      (S.median t (S.parent t c)).index where
  component := S.component (t + 1) c
  subset_parent := S.child_subset t ht c hc
  avoids := S.child_avoids t ht c hc

/-- The component process induces the numerical global-round system. -/
def toComponentRoundSystem (S : G.LayerSeparationProcess α steps N g) :
    ComponentRoundSystem α steps N where
  active := S.active
  size := fun t c => (S.component t c).verts.card
  parent := S.parent
  initial_bound := S.initial_size_le
  positive := by
    intro t ht c hc
    exact Finset.card_pos.mpr (S.component t c).nonempty
  parent_active := S.parent_active
  halves := by
    intro t ht c hc
    let D := S.childDescendant ht hc
    exact D.card_halves (S.median t (S.parent t c)) rfl

/-- No active component remains after `log₂ N + 1` valid median-cut rounds. -/
theorem active_empty_after_log
    (S : G.LayerSeparationProcess α (Nat.log 2 N + 1) N g) :
    S.active (Nat.log 2 N + 1) = ∅ :=
  S.toComponentRoundSystem.active_empty_after_log

/-- Distinct global layer indices selected in one round. -/
def roundCuts (S : G.LayerSeparationProcess α steps N g) (t : Nat) : Finset Nat :=
  (S.active t).image fun c => (S.median t c).index

/-- Selecting one median per active component uses at most `g` layers in a round. -/
theorem roundCuts_card_le (S : G.LayerSeparationProcess α steps N g)
    {t : Nat} (ht : t < steps) :
    (S.roundCuts t).card ≤ g := by
  calc
    (S.roundCuts t).card ≤ (S.active t).card := Finset.card_image_le
    _ ≤ g := S.active_card_le t ht

/-- List of the per-round numbers of selected distinct layers. -/
def selectedCounts (S : G.LayerSeparationProcess α steps N g) : List Nat :=
  (List.range steps).map fun t => (S.roundCuts t).card

@[simp] theorem selectedCounts_length (S : G.LayerSeparationProcess α steps N g) :
    S.selectedCounts.length = steps := by
  simp [selectedCounts]

/-- Sum of the per-round layer counts is at most `g * steps`. -/
theorem selectedCounts_sum_le (S : G.LayerSeparationProcess α steps N g) :
    S.selectedCounts.sum ≤ g * steps := by
  have hcounts : ∀ x ∈ S.selectedCounts, x ≤ g := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
    exact S.roundCuts_card_le (List.mem_range.mp ht)
  have h := sum_le_mul_length_of_each_le S.selectedCounts g hcounts
  simpa using h

/-- The exact separator-layer count for logarithmically many rounds. -/
theorem selectedCounts_sum_le_log
    (S : G.LayerSeparationProcess α (Nat.log 2 N + 1) N g) :
    S.selectedCounts.sum ≤ g * (Nat.log 2 N + 1) := by
  simpa using S.selectedCounts_sum_le

end LayerSeparationProcess
end LayeredDigraph
end Allender
