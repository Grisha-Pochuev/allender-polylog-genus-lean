import Allender.FiniteComponent
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Existence of a median layer for a finite component

The paper chooses the first layer at which the cumulative number of component
vertices reaches at least half of the total.  This file carries out that choice
with `Nat.find` and proves the two cardinality inequalities required by
`FiniteConnectedSet.MedianLayer`.
-/

namespace Allender
namespace LayeredDigraph
namespace FiniteConnectedSet

variable {V : Type*} [DecidableEq V] (G : LayeredDigraph V)

/-- The finite set of layer indices occupied by a component. -/
def layerImage (C : G.FiniteConnectedSet) : Finset Nat :=
  C.verts.image G.layer

/-- The occupied layer set is nonempty. -/
theorem layerImage_nonempty (C : G.FiniteConnectedSet) : C.layerImage.Nonempty :=
  C.nonempty.image G.layer

/-- The largest layer occupied by the component. -/
def maxLayer (C : G.FiniteConnectedSet) : Nat :=
  C.layerImage.max' C.layerImage_nonempty

/-- Every component vertex lies at or below `maxLayer`. -/
theorem layer_le_maxLayer (C : G.FiniteConnectedSet) {v : V} (hv : v ∈ C.verts) :
    G.layer v ≤ C.maxLayer := by
  have himage : G.layer v ∈ C.layerImage :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  exact Finset.le_max' C.layerImage (G.layer v) himage

/-- Component vertices on or below layer `m`. -/
def atOrBelow (C : G.FiniteConnectedSet) (m : Nat) : Finset V :=
  C.verts.filter fun v => G.layer v ≤ m

/-- At the maximal occupied layer, every component vertex has been accumulated. -/
theorem atOrBelow_maxLayer (C : G.FiniteConnectedSet) :
    C.atOrBelow C.maxLayer = C.verts := by
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact C.layer_le_maxLayer hv

/-- Every finite connected component has a weighted median layer. -/
theorem exists_medianLayer (C : G.FiniteConnectedSet) : Nonempty C.MedianLayer := by
  classical
  let P : Nat → Prop := fun m => C.verts.card ≤ 2 * (C.atOrBelow m).card
  have hex : ∃ m, P m := by
    refine ⟨C.maxLayer, ?_⟩
    rw [C.atOrBelow_maxLayer]
    omega
  let m := Nat.find hex
  have hcross : P m := Nat.find_spec hex
  refine ⟨⟨m, ?_, ?_⟩⟩
  · by_cases hmzero : m = 0
    · subst m
      simp [below]
    · have hpred_lt : m - 1 < m := by omega
      have hnotP : ¬P (m - 1) := Nat.find_min hex hpred_lt
      have hpred_eq : C.atOrBelow (m - 1) = C.below m := by
        ext v
        simp [atOrBelow, below]
        omega
      have hnotCross : ¬C.verts.card ≤ 2 * (C.below m).card := by
        intro h
        apply hnotP
        simpa [hpred_eq] using h
      omega
  · have hdisj : Disjoint (C.atOrBelow m) (C.above m) := by
      refine Finset.disjoint_left.mpr ?_
      intro v hvLow hvHigh
      simp [atOrBelow] at hvLow
      simp [above] at hvHigh
      omega
    have hunion : C.atOrBelow m ∪ C.above m = C.verts := by
      ext v
      simp [atOrBelow, above]
      omega
    have hcard : (C.atOrBelow m).card + (C.above m).card = C.verts.card := by
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    omega

end FiniteConnectedSet
end LayeredDigraph
end Allender
