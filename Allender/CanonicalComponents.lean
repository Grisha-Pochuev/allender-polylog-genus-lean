import Allender.ComponentSupport
import Allender.OrientableGenus

/-!
# Canonical active components of a graph remainder

This module makes the active set used by the separator recursion concrete.  An
active identifier is the finite support of an actual nonplanar connected
component.  Support injectivity ensures that no components are merged, and
genus additivity bounds the number of active identifiers.

The decoding function is total (as required by the existing process structure)
but is proved to recover exactly the intended component whenever its identifier
is active.
-/

namespace Allender
namespace LayeredDigraph

open OrientableGenus

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {G : LayeredDigraph V}

/-- Choose one vertex of a connected component. -/
noncomputable def componentRoot {H : SimpleGraph V}
    (c : H.ConnectedComponent) : V :=
  c.nonempty_supp.choose

theorem componentRoot_mem {H : SimpleGraph V}
    (c : H.ConnectedComponent) :
    componentRoot c ∈ c.supp :=
  c.nonempty_supp.choose_spec

/-- The component of a larger graph containing a given component of a spanning
subgraph. -/
noncomputable def parentComponent {H H' : SimpleGraph V}
    (h : H ≤ H') (c : H.ConnectedComponent) :
    H'.ConnectedComponent :=
  H'.connectedComponentMk (componentRoot c)

/-- Every child-component vertex lies in its canonical parent component. -/
theorem component_supp_subset_parent {H H' : SimpleGraph V}
    (h : H ≤ H') (c : H.ConnectedComponent) :
    c.supp ⊆ (parentComponent h c).supp := by
  intro v hv
  have hreach : H.Reachable v (componentRoot c) :=
    c.reachable_of_mem_supp hv (componentRoot_mem c)
  have hreach' : H'.Reachable v (componentRoot c) :=
    hreach.mono h
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact SimpleGraph.ConnectedComponent.sound hreach'

/-- The ambient-vertex component graph of a child is a spanning subgraph of
the ambient-vertex graph of its canonical parent. -/
theorem componentGraph_le_parentGraph {H H' : SimpleGraph V}
    (h : H ≤ H') (c : H.ConnectedComponent) :
    OrientableGenus.componentGraph c ≤
      OrientableGenus.componentGraph (parentComponent h c) := by
  intro u v huv
  rw [OrientableGenus.componentGraph_adj] at huv ⊢
  exact ⟨component_supp_subset_parent h c huv.1, h huv.2⟩

/-- A nonplanar child component always has a nonplanar canonical parent. -/
theorem parentComponent_mem_nonplanar {H H' : SimpleGraph V}
    [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (h : H ≤ H') {c : H.ConnectedComponent}
    (hc : c ∈ OrientableGenus.nonplanarComponents H) :
    parentComponent h c ∈
      OrientableGenus.nonplanarComponents H' := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · simp [OrientableGenus.components]
  · have hchild : OrientableGenus.genus
        (OrientableGenus.componentGraph c) ≠ 0 := by
      simpa [OrientableGenus.nonplanarComponents,
        OrientableGenus.IsPlanar] using
        (Finset.mem_filter.mp hc).2
    have hmono : OrientableGenus.genus
        (OrientableGenus.componentGraph c) ≤
        OrientableGenus.genus
          (OrientableGenus.componentGraph (parentComponent h c)) :=
      OrientableGenus.genus_mono (componentGraph_le_parentGraph h c)
    have hparent : OrientableGenus.genus
        (OrientableGenus.componentGraph (parentComponent h c)) ≠ 0 := by
      have hpos : 0 < OrientableGenus.genus
          (OrientableGenus.componentGraph c) :=
        Nat.pos_of_ne_zero hchild
      exact Nat.ne_of_gt (hpos.trans_le hmono)
    simpa [OrientableGenus.IsPlanar] using hparent

/-- If a component contains an isolated vertex, then its
ambient-vertex component graph is edgeless. -/
theorem componentGraph_eq_bot_of_isolated {H : SimpleGraph V}
    (c : H.ConnectedComponent) {v : V}
    (hv : v ∈ c.supp) (hiso : ∀ u, ¬H.Adj v u) :
    OrientableGenus.componentGraph c = ⊥ := by
  have hneighbor : H.neighborSet v = ∅ := by
    ext u
    simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false]
    exact iff_false_intro (hiso u)
  apply SimpleGraph.ext
  intro u w
  constructor
  · intro huw
    have hu : u ∈ c.supp :=
      ((OrientableGenus.componentGraph_adj c u w).1 huw).1
    have hreach : H.Reachable u v :=
      c.reachable_of_mem_supp hu hv
    have huv : u = v := by
      by_contra hne
      exact (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
        hne hneighbor) hreach
    subst u
    exact (hiso w
      (((OrientableGenus.componentGraph_adj c v w).1 huw).2)).elim
  · intro hbot
    exact False.elim (by simpa using hbot)

/-- A nonplanar component cannot contain an isolated vertex. -/
theorem nonplanarComponent_not_mem_isolated {H : SimpleGraph V}
    [DecidableRel H.Adj] {c : H.ConnectedComponent}
    (hc : c ∈ OrientableGenus.nonplanarComponents H)
    {v : V} (hiso : ∀ u, ¬H.Adj v u) :
    v ∉ c.supp := by
  intro hv
  have hnonzero : OrientableGenus.genus
      (OrientableGenus.componentGraph c) ≠ 0 := by
    simpa [OrientableGenus.nonplanarComponents,
      OrientableGenus.IsPlanar] using
      (Finset.mem_filter.mp hc).2
  have hgraph : OrientableGenus.componentGraph c = ⊥ :=
    componentGraph_eq_bot_of_isolated c hv hiso
  apply hnonzero
  rw [hgraph]
  exact OrientableGenus.genus_bot

/-- A vertex on a deleted layer is isolated in the graph remainder. -/
theorem deleteLayers_isolated_of_mem (cuts : Finset Nat)
    {v : V} (hv : G.layer v ∈ cuts) :
    ∀ u, ¬(G.deleteLayers cuts).toSimpleGraph.Adj v u := by
  intro u hadj
  rcases hadj with hvu | huv
  · exact G.no_edge_from_cut_vertex cuts hv hvu
  · exact G.no_edge_to_cut_vertex cuts hv huv

/-- Every vertex of a nonplanar remainder component survives all deleted
layers. -/
theorem nonplanarComponent_survives (cuts : Finset Nat)
    {c : (G.deleteLayers cuts).toSimpleGraph.ConnectedComponent}
    (hc : c ∈ OrientableGenus.nonplanarComponents
      ((G.deleteLayers cuts).toSimpleGraph))
    {v : V} (hv : v ∈ c.supp) :
    G.layer v ∉ cuts := by
  intro hcut
  exact (nonplanarComponent_not_mem_isolated hc
    (G.deleteLayers_isolated_of_mem cuts hcut)) hv

/-- Finite supports of the actual nonplanar connected components of `H`. -/
noncomputable def activeComponentVerts (H : SimpleGraph V)
    [DecidableRel H.Adj] : Finset (Finset V) := by
  classical
  exact (OrientableGenus.nonplanarComponents H).image componentVerts

theorem mem_activeComponentVerts_iff (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : Finset V) :
    s ∈ activeComponentVerts H ↔
      ∃ c ∈ OrientableGenus.nonplanarComponents H,
        componentVerts c = s := by
  classical
  simp [activeComponentVerts]

/-- The concrete active set has at most `genus H` members. -/
theorem activeComponentVerts_card_le_genus (H : SimpleGraph V)
    [DecidableRel H.Adj] :
    (activeComponentVerts H).card ≤ OrientableGenus.genus H := by
  classical
  calc
    (activeComponentVerts H).card ≤
        (OrientableGenus.nonplanarComponents H).card := by
      exact Finset.card_image_le
    _ ≤ OrientableGenus.genus H :=
      OrientableGenus.nonplanarComponents_card_le_genus H

/-- Decode a support identifier to its unique nonplanar component when possible.
Outside the active set an arbitrary component is returned; no theorem uses that
fallback as an active component. -/
noncomputable def componentForSupport (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : Finset V) : H.ConnectedComponent := by
  classical
  if h : ∃ c ∈ OrientableGenus.nonplanarComponents H,
      componentVerts c = s then
    exact Classical.choose h
  else
    exact H.connectedComponentMk default

/-- Active identifiers decode back to their exact support. -/
theorem componentForSupport_verts (H : SimpleGraph V)
    [DecidableRel H.Adj] {s : Finset V}
    (hs : s ∈ activeComponentVerts H) :
    componentVerts (componentForSupport H s) = s := by
  classical
  have hex : ∃ c ∈ OrientableGenus.nonplanarComponents H,
      componentVerts c = s :=
    (mem_activeComponentVerts_iff H s).1 hs
  unfold componentForSupport
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

/-- An active identifier decodes to a genuinely nonplanar component. -/
theorem componentForSupport_mem_nonplanar (H : SimpleGraph V)
    [DecidableRel H.Adj] {s : Finset V}
    (hs : s ∈ activeComponentVerts H) :
    componentForSupport H s ∈
      OrientableGenus.nonplanarComponents H := by
  classical
  have hex : ∃ c ∈ OrientableGenus.nonplanarComponents H,
      componentVerts c = s :=
    (mem_activeComponentVerts_iff H s).1 hs
  unfold componentForSupport
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1

/-- The concrete finite connected set attached to one active remainder
component. -/
noncomputable def activeFiniteConnectedSet (cuts : Finset Nat)
    (s : Finset V) : G.FiniteConnectedSet :=
  componentFiniteConnectedSet (G.deleteLayers_toSimpleGraph_le cuts)
    (componentForSupport (G.deleteLayers cuts).toSimpleGraph s)

/-- On an active identifier the concrete connected set has exactly that
identifier as its vertex finset. -/
theorem activeFiniteConnectedSet_verts (cuts : Finset Nat)
    {s : Finset V}
    (hs : s ∈ activeComponentVerts
      ((G.deleteLayers cuts).toSimpleGraph)) :
    (activeFiniteConnectedSet (G := G) cuts s).verts = s := by
  classical
  rw [activeFiniteConnectedSet, componentFiniteConnectedSet_verts]
  exact componentForSupport_verts _ hs

/-- Every active connected set is bounded by the ambient vertex count. -/
theorem activeFiniteConnectedSet_card_le (cuts : Finset Nat)
    (s : Finset V) :
    (activeFiniteConnectedSet (G := G) cuts s).verts.card ≤
      Fintype.card V := by
  classical
  exact componentFiniteConnectedSet_card_le
    (G.deleteLayers_toSimpleGraph_le cuts)
    (componentForSupport (G.deleteLayers cuts).toSimpleGraph s)

end LayeredDigraph
end Allender
