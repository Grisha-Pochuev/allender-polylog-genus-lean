import Allender.FiniteComponent
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Canonical connected-component vertex sets

The separator process in the manuscript is defined from the actual connected
components of each graph remainder.  Earlier modules deliberately used an
abstract finite-component interface.  This file supplies the first concrete
bridge from mathlib's connected components to that interface.

For a component of any spanning subgraph of the original underlying graph, we:

* turn its finite support into a `Finset`;
* convert mathlib walks into the project's undirected layered walks;
* prove that the resulting vertex set is nonempty and connected;
* prove that distinct connected components have distinct support finsets.

No topological axiom is used here.
-/

namespace Allender
namespace LayeredDigraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : LayeredDigraph V}

/-- Convert a mathlib walk in a spanning subgraph of the underlying graph into
the project's undirected layered walk. -/
def UWalk.ofSimpleGraphWalk {H : SimpleGraph V}
    (hH : H ≤ G.toSimpleGraph) {u v : V} :
    H.Walk u v → G.UWalk u v
  | .nil => .nil u
  | .cons hadj tail =>
      .cons (hH hadj) (UWalk.ofSimpleGraphWalk hH tail)

/-- Every vertex of a converted component walk stays in that component. -/
theorem UWalk.ofSimpleGraphWalk_all_component {H : SimpleGraph V}
    (hH : H ≤ G.toSimpleGraph) (c : H.ConnectedComponent)
    {u v : V} (p : H.Walk u v) (hu : u ∈ c.supp) :
    (UWalk.ofSimpleGraphWalk hH p).All (fun x => x ∈ c.supp) := by
  induction p with
  | nil =>
      exact hu
  | @cons u v z hadj tail ih =>
      refine ⟨hu, ?_⟩
      exact ih (c.mem_supp_of_adj_mem_supp hu hadj)

/-- The finite support of a connected component. -/
noncomputable def componentVerts {H : SimpleGraph V}
    (c : H.ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset

@[simp] theorem mem_componentVerts {H : SimpleGraph V}
    (c : H.ConnectedComponent) (v : V) :
    v ∈ componentVerts c ↔ v ∈ c.supp := by
  classical
  simp [componentVerts]

/-- Component supports are nonempty as finsets. -/
theorem componentVerts_nonempty {H : SimpleGraph V}
    (c : H.ConnectedComponent) :
    (componentVerts c).Nonempty := by
  classical
  obtain ⟨v, hv⟩ := c.nonempty_supp
  exact ⟨v, (mem_componentVerts c v).2 hv⟩

/-- Distinct connected components have distinct finite supports. -/
theorem componentVerts_injective {H : SimpleGraph V} :
    Function.Injective (componentVerts :
      H.ConnectedComponent → Finset V) := by
  classical
  intro c d h
  apply SimpleGraph.ConnectedComponent.supp_injective
  ext v
  have hv := Finset.ext_iff.mp h v
  simpa only [mem_componentVerts] using hv

/-- A component of a spanning subgraph becomes a concrete finite connected set
in the original layered graph. -/
noncomputable def componentFiniteConnectedSet {H : SimpleGraph V}
    (hH : H ≤ G.toSimpleGraph) (c : H.ConnectedComponent) :
    G.FiniteConnectedSet := by
  classical
  refine
    { verts := componentVerts c
      nonempty := componentVerts_nonempty c
      connected := ?_ }
  intro u v hu hv
  have hu' : u ∈ c.supp := (mem_componentVerts c u).1 hu
  have hv' : v ∈ c.supp := (mem_componentVerts c v).1 hv
  let p : H.Walk u v := (c.reachable_of_mem_supp hu' hv').some
  refine ⟨UWalk.ofSimpleGraphWalk hH p, ?_⟩
  apply UWalk.all_mono
    (UWalk.ofSimpleGraphWalk_all_component hH c p hu')
  intro x hx
  exact (mem_componentVerts c x).2 hx

@[simp] theorem componentFiniteConnectedSet_verts {H : SimpleGraph V}
    (hH : H ≤ G.toSimpleGraph) (c : H.ConnectedComponent) :
    (componentFiniteConnectedSet hH c).verts = componentVerts c := rfl

/-- Every concrete component support has at most all ambient vertices. -/
theorem componentFiniteConnectedSet_card_le {H : SimpleGraph V}
    (hH : H ≤ G.toSimpleGraph) (c : H.ConnectedComponent) :
    (componentFiniteConnectedSet hH c).verts.card ≤ Fintype.card V := by
  classical
  rw [componentFiniteConnectedSet_verts]
  simpa using Finset.card_le_univ (componentVerts c)

end LayeredDigraph
end Allender
