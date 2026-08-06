import Allender.LayerDeletion
import Allender.GenusBudget
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Exact external boundary for orientable graph genus

The candidate proof uses ordinary orientable graph genus only through
monotonicity and the Battle--Harary--Kodama--Youngs additivity theorem. Those
published topological results are isolated here. Crucially, no layer separator
or planarization conclusion is assumed.
-/

namespace Allender
namespace OrientableGenus

open scoped BigOperators

/-- Ordinary orientable genus of a finite simple graph (external definition). -/
axiom genus {V : Type*} [Finite V] (G : SimpleGraph V) : Nat

/-- Planarity expressed as orientable genus zero. -/
def IsPlanar {V : Type*} [Finite V] (G : SimpleGraph V) : Prop :=
  genus G = 0

/-- Genus is monotone under taking a spanning subgraph. -/
axiom genus_mono {V : Type*} [Finite V] {G H : SimpleGraph V}
    (h : G ≤ H) : genus G ≤ genus H

/-- Battle--Harary--Kodama--Youngs additivity over connected components. -/
axiom genus_eq_sum_components {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    genus G = ∑ c : G.ConnectedComponent, genus c.toSimpleGraph

/-- Connected components whose induced component graph has positive genus. -/
noncomputable def nonplanarComponents {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset G.ConnectedComponent := by
  classical
  exact Finset.univ.filter fun c => ¬IsPlanar c.toSimpleGraph

/-- The number of nonplanar components is at most the genus of the whole graph. -/
theorem nonplanarComponents_card_le_genus {V : Type*}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (nonplanarComponents G).card ≤ genus G := by
  classical
  calc
    (nonplanarComponents G).card =
        ∑ _c in nonplanarComponents G, 1 := by simp
    _ ≤ ∑ c in nonplanarComponents G, genus c.toSimpleGraph := by
      apply Finset.sum_le_sum
      intro c hc
      have hpositive : genus c.toSimpleGraph ≠ 0 := by
        simpa [nonplanarComponents, IsPlanar] using (Finset.mem_filter.mp hc).2
      exact Nat.one_le_iff_ne_zero.mpr hpositive
    _ ≤ ∑ c : G.ConnectedComponent, genus c.toSimpleGraph := by
      exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = genus G := (genus_eq_sum_components G).symm

/-- A finite graph is planar exactly when it has no nonplanar component. -/
theorem isPlanar_iff_nonplanarComponents_eq_empty {V : Type*}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsPlanar G ↔ nonplanarComponents G = ∅ := by
  classical
  constructor
  · intro hplanar
    have hcard : (nonplanarComponents G).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [IsPlanar, hplanar] using nonplanarComponents_card_le_genus G
    exact Finset.card_eq_zero.mp hcard
  · intro hempty
    unfold IsPlanar
    rw [genus_eq_sum_components G]
    apply Finset.sum_eq_zero
    intro c hc
    by_contra hpositive
    have hmem : c ∈ nonplanarComponents G := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, by simpa [IsPlanar]⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty c hmem

/-- Deleting layers cannot increase orientable genus. -/
theorem genus_deleteLayers_le {V : Type*} [Finite V]
    (G : LayeredDigraph V) (cuts : Finset Nat) :
    genus (G.deleteLayers cuts).toSimpleGraph ≤ genus G.toSimpleGraph :=
  genus_mono (G.deleteLayers_toSimpleGraph_le cuts)

end OrientableGenus
end Allender
