import Allender.LayeredWalk
import Mathlib.Tactic

/-!
# Finite connected vertex sets and median-layer cuts

This file connects the walk separator theorem to component cardinalities.  It
formalizes the exact one-round statement used in the paper: after deleting a
median layer from a connected component, every nonempty connected descendant
has at most half as many vertices.
-/

namespace Allender
namespace LayeredDigraph

variable {V : Type*} [DecidableEq V]

/-- A nonempty finite vertex set connected in the underlying undirected graph. -/
structure FiniteConnectedSet (G : LayeredDigraph V) where
  verts : Finset V
  nonempty : verts.Nonempty
  connected : ∀ {u v : V}, u ∈ verts → v ∈ verts →
    ∃ walk : G.UWalk u v, walk.All (fun x => x ∈ verts)

namespace FiniteConnectedSet

variable {G : LayeredDigraph V}

/-- Vertices of `C` strictly below layer `m`. -/
def below (C : G.FiniteConnectedSet) (m : Nat) : Finset V :=
  C.verts.filter fun v => G.layer v < m

/-- Vertices of `C` strictly above layer `m`. -/
def above (C : G.FiniteConnectedSet) (m : Nat) : Finset V :=
  C.verts.filter fun v => m < G.layer v

/-- A layer whose strict lower and upper sides each contain at most half of `C`. -/
structure MedianLayer (C : G.FiniteConnectedSet) where
  index : Nat
  below_half : 2 * (C.below index).card ≤ C.verts.card
  above_half : 2 * (C.above index).card ≤ C.verts.card

/--
A connected component surviving deletion of layer `m`, represented as a finite
connected vertex set contained in the parent and avoiding the deleted layer.
-/
structure DescendantAfterCut (C : G.FiniteConnectedSet) (m : Nat) where
  component : G.FiniteConnectedSet
  subset_parent : component.verts ⊆ C.verts
  avoids : ∀ v ∈ component.verts, G.layer v ≠ m

namespace DescendantAfterCut

/-- Every walk inside a surviving descendant avoids the deleted layer. -/
theorem walk_survives {C : G.FiniteConnectedSet} {m : Nat}
    (D : C.DescendantAfterCut m) {u v : V}
    (walk : G.UWalk u v)
    (hwalk : walk.All (fun x => x ∈ D.component.verts)) :
    walk.All (G.Survives {m}) := by
  apply hwalk.all_mono
  intro x hx
  have hne : G.layer x ≠ m := D.avoids x hx
  simpa [LayeredDigraph.Survives] using hne

/-- A connected surviving descendant lies entirely below or entirely above the cut. -/
theorem all_below_or_all_above {C : G.FiniteConnectedSet} {m : Nat}
    (D : C.DescendantAfterCut m) :
    (∀ v ∈ D.component.verts, G.layer v < m) ∨
      (∀ v ∈ D.component.verts, m < G.layer v) := by
  obtain ⟨root, hroot⟩ := D.component.nonempty
  have hroot_ne : G.layer root ≠ m := D.avoids root hroot
  rcases lt_or_gt_of_ne hroot_ne with hroot_below | hroot_above
  · left
    intro v hv
    by_contra hnotBelow
    have hge : m ≤ G.layer v := Nat.le_of_not_gt hnotBelow
    have hv_ne : G.layer v ≠ m := D.avoids v hv
    have hv_above : m < G.layer v := lt_of_le_of_ne hge (Ne.symm hv_ne)
    obtain ⟨walk, hwalk⟩ := D.component.connected hroot hv
    exact G.no_surviving_walk_across_layer hroot_below hv_above walk
      (D.walk_survives walk hwalk)
  · right
    intro v hv
    by_contra hnotAbove
    have hle : G.layer v ≤ m := Nat.le_of_not_gt hnotAbove
    have hv_ne : G.layer v ≠ m := D.avoids v hv
    have hv_below : G.layer v < m := lt_of_le_of_ne hle hv_ne
    obtain ⟨walk, hwalk⟩ := D.component.connected hv hroot
    exact G.no_surviving_walk_across_layer hv_below hroot_above walk
      (D.walk_survives walk hwalk)

/-- Every connected descendant after a median-layer cut has at most half the parent size. -/
theorem card_halves {C : G.FiniteConnectedSet} {m : Nat}
    (D : C.DescendantAfterCut m)
    (hmedian : C.MedianLayer) (hm : hmedian.index = m) :
    2 * D.component.verts.card ≤ C.verts.card := by
  subst m
  rcases D.all_below_or_all_above with hbelow | habove
  · have hsub : D.component.verts ⊆ C.below hmedian.index := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨D.subset_parent hv, hbelow v hv⟩
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans hmedian.below_half
  · have hsub : D.component.verts ⊆ C.above hmedian.index := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨D.subset_parent hv, habove v hv⟩
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans hmedian.above_half

end DescendantAfterCut
end FiniteConnectedSet
end LayeredDigraph
end Allender
