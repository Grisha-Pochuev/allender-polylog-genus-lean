import Allender.FiniteComponent
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Existence of a median layer for a finite component

The paper chooses the first layer at which the cumulative number of component
vertices reaches at least half of the total. This file carries out that choice
with `Nat.find` and proves the two cardinality inequalities required by
`FiniteConnectedSet.MedianLayer`.
-/

namespace Allender
namespace LayeredDigraph
namespace FiniteConnectedSet

variable {V : Type*} [DecidableEq V] {G : LayeredDigraph V}

def layerImage (C : G.FiniteConnectedSet) : Finset Nat :=
  C.verts.image G.layer

theorem layerImage_nonempty (C : G.FiniteConnectedSet) : C.layerImage.Nonempty :=
  C.nonempty.image G.layer

def maxLayer (C : G.FiniteConnectedSet) : Nat :=
  C.layerImage.max' C.layerImage_nonempty

theorem layer_le_maxLayer (C : G.FiniteConnectedSet) {v : V} (hv : v ∈ C.verts) :
    G.layer v ≤ C.maxLayer := by
  have himage : G.layer v ∈ C.layerImage :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  exact Finset.le_max' C.layerImage (G.layer v) himage

def atOrBelow (C : G.FiniteConnectedSet) (m : Nat) : Finset V :=
  C.verts.filter fun v => G.layer v ≤ m

theorem atOrBelow_maxLayer (C : G.FiniteConnectedSet) :
    C.atOrBelow C.maxLayer = C.verts := by
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact C.layer_le_maxLayer hv

theorem exists_medianLayer (C : G.FiniteConnectedSet) : Nonempty C.MedianLayer := by
  classical
  let P : Nat → Prop := fun m => C.verts.card ≤ 2 * (C.atOrBelow m).card
  have hex : ∃ m, P m := by
    refine ⟨C.maxLayer, ?_⟩
    dsimp [P]
    rw [C.atOrBelow_maxLayer]
    omega
  let m := Nat.find hex
  have hcross : C.verts.card ≤ 2 * (C.atOrBelow m).card := by
    change P m
    exact Nat.find_spec hex
  refine ⟨⟨m, ?_, ?_⟩⟩
  · by_cases hmzero : m = 0
    · have hbelow : C.below m = ∅ := by
        ext v
        simp [below, hmzero]
      rw [hbelow]
      simp
    · have hpred_lt : m - 1 < m := by omega
      have hnotP : ¬P (m - 1) := Nat.find_min hex hpred_lt
      have hpred_eq : C.atOrBelow (m - 1) = C.below m := by
        ext v
        simp [atOrBelow, below]
        omega
      have hnotCross : ¬C.verts.card ≤ 2 * (C.below m).card := by
        intro h
        apply hnotP
        dsimp [P]
        rw [hpred_eq]
        exact h
      omega
  · have hdisj : Disjoint (C.atOrBelow m) (C.above m) := by
      refine Finset.disjoint_left.mpr ?_
      intro v hvLow hvHigh
      have hle : G.layer v ≤ m := (Finset.mem_filter.mp hvLow).2
      have hgt : m < G.layer v := (Finset.mem_filter.mp hvHigh).2
      omega
    have hunion : C.atOrBelow m ∪ C.above m = C.verts := by
      apply Finset.ext
      intro v
      simp only [atOrBelow, above, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hv, _⟩ | ⟨hv, _⟩)
        · exact hv
        · exact hv
      · intro hv
        rcases le_or_gt (G.layer v) m with hle | hgt
        · exact Or.inl ⟨hv, hle⟩
        · exact Or.inr ⟨hv, hgt⟩
    have hcard : (C.atOrBelow m).card + (C.above m).card = C.verts.card := by
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    omega

end FiniteConnectedSet
end LayeredDigraph
end Allender
