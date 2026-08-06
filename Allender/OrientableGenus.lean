import Allender.LayerDeletion
import Allender.GenusBudget
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Exact external boundary for orientable graph genus

The candidate proof uses ordinary orientable graph genus only through three
published topological facts:

1. the ordinary orientable genus of a finite graph is a natural number;
2. genus is monotone under taking subgraphs;
3. genus is additive over connected components
   (Battle--Harary--Kodama--Youngs).

These facts are deliberately isolated as named axioms. No separator,
planarization, circuit-simulation, or bounty conclusion is assumed here.
Every later theorem that uses topology will expose these dependencies through
`#print axioms`.
-/

namespace Allender
namespace OrientableGenus

open scoped BigOperators

/-- Ordinary orientable genus of a finite simple graph.

This is an external definition boundary: a future full topological
formalization may replace it by the minimum genus of an orientable surface in
which the graph embeds.
-/
axiom genus {V : Type*} [Finite V] (G : SimpleGraph V) : Nat

/-- Planarity expressed as orientable genus zero. -/
def IsPlanar {V : Type*} [Finite V] (G : SimpleGraph V) : Prop :=
  genus G = 0

/-- External theorem: orientable genus is monotone under taking a spanning
subgraph. -/
axiom genus_mono {V : Type*} [Finite V] {G H : SimpleGraph V}
    (h : G ≤ H) : genus G ≤ genus H

/-- A fixed finite enumeration of the connected components of `G`.

Using one named finset avoids accidental dependence on definitionally
different `Fintype` instances for connected components.
-/
noncomputable def components {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset G.ConnectedComponent := by
  classical
  exact Finset.univ

/-- The graph of one connected component, kept on the original ambient vertex
type by turning vertices outside the component into isolates.  This formulation
lets later subgraph comparisons stay on one vertex type. -/
def componentGraph {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : G.ConnectedComponent) : SimpleGraph V :=
  c.toSimpleGraph.spanningCoe

@[simp] theorem componentGraph_adj {V : Type*} [Fintype V]
    {G : SimpleGraph V} (c : G.ConnectedComponent) (u v : V) :
    (componentGraph c).Adj u v ↔ u ∈ c.supp ∧ G.Adj u v :=
  c.adj_spanningCoe_toSimpleGraph

/-- External theorem: Battle--Harary--Kodama--Youngs additivity of orientable
genus over connected components. Isolated ambient vertices do not affect the
genus of a component. -/
axiom genus_eq_sum_components {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    genus G = Finset.sum (components G) (fun c => genus (componentGraph c))

/-- Connected components whose induced component graph has positive genus. -/
noncomputable def nonplanarComponents {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset G.ConnectedComponent := by
  classical
  exact (components G).filter fun c => ¬IsPlanar (componentGraph c)

/-- The number of nonplanar components is at most the genus of the whole graph.

Unlike the three external declarations above, this is a proved consequence
inside Lean.
-/
theorem nonplanarComponents_card_le_genus {V : Type*}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (nonplanarComponents G).card ≤ genus G := by
  classical
  calc
    (nonplanarComponents G).card =
        Finset.sum (nonplanarComponents G) (fun _ => 1) := by simp
    _ ≤ Finset.sum (nonplanarComponents G)
          (fun c => genus (componentGraph c)) := by
      apply Finset.sum_le_sum
      intro c hc
      have hpositive : genus (componentGraph c) ≠ 0 := by
        simpa [nonplanarComponents, IsPlanar] using
          (Finset.mem_filter.mp hc).2
      exact Nat.one_le_iff_ne_zero.mpr hpositive
    _ ≤ Finset.sum (components G) (fun c => genus (componentGraph c)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro c hc hnot
        exact Nat.zero_le _
    _ = genus G := (genus_eq_sum_components G).symm

/-- A finite graph is planar exactly when it has no nonplanar component. -/
theorem isPlanar_iff_nonplanarComponents_eq_empty {V : Type*}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsPlanar G ↔ nonplanarComponents G = ∅ := by
  classical
  constructor
  · intro hplanar
    have hplanar' : genus G = 0 := hplanar
    have hle : (nonplanarComponents G).card ≤ 0 := by
      rw [← hplanar']
      exact nonplanarComponents_card_le_genus G
    have hcard : (nonplanarComponents G).card = 0 :=
      Nat.eq_zero_of_le_zero hle
    exact Finset.card_eq_zero.mp hcard
  · intro hempty
    unfold IsPlanar
    rw [genus_eq_sum_components G]
    apply Finset.sum_eq_zero
    intro c hc
    by_contra hpositive
    have hmem : c ∈ nonplanarComponents G := by
      exact Finset.mem_filter.mpr ⟨hc, by simpa [IsPlanar]⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty c hmem

/-- Deleting whole layers cannot increase orientable genus. -/
theorem genus_deleteLayers_le {V : Type*} [Finite V]
    (G : LayeredDigraph V) (cuts : Finset Nat) :
    genus (G.deleteLayers cuts).toSimpleGraph ≤ genus G.toSimpleGraph :=
  genus_mono (G.deleteLayers_toSimpleGraph_le cuts)

end OrientableGenus
end Allender
