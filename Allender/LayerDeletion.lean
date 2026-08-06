import Allender.SimpleGraph
import Mathlib.Data.Finset.Lattice

/-!
# Deleting whole layers

The separator proof repeatedly deletes every vertex whose layer index has been
selected.  We keep the ambient vertex type fixed and remove all incident edges;
deleted vertices consequently become isolated.  This makes graph inclusion
between rounds literal pointwise inclusion.
-/

namespace Allender
namespace LayeredDigraph

variable {V : Type*}

/-- Layered graph obtained by deleting all edges incident with a cut layer. -/
def deleteLayers (G : LayeredDigraph V) (cuts : Finset Nat) : LayeredDigraph V where
  edge := fun u v => G.edge u v ∧ G.Survives cuts u ∧ G.Survives cuts v
  layer := G.layer
  edge_next := by
    intro u v h
    exact G.edge_next h.1

@[simp] theorem deleteLayers_layer (G : LayeredDigraph V) (cuts : Finset Nat) (v : V) :
    (G.deleteLayers cuts).layer v = G.layer v := rfl

@[simp] theorem deleteLayers_edge_iff (G : LayeredDigraph V) (cuts : Finset Nat)
    (u v : V) :
    (G.deleteLayers cuts).edge u v ↔
      G.edge u v ∧ G.Survives cuts u ∧ G.Survives cuts v := Iff.rfl

/-- Deleting no layers leaves every edge unchanged. -/
theorem deleteLayers_empty (G : LayeredDigraph V) : G.deleteLayers ∅ = G := by
  cases G with
  | mk edge layer edge_next =>
      simp only [deleteLayers, Survives, Finset.notMem_empty, and_true]

/-- The undirected remainder is a subgraph of the original undirected graph. -/
theorem deleteLayers_toSimpleGraph_le (G : LayeredDigraph V) (cuts : Finset Nat) :
    (G.deleteLayers cuts).toSimpleGraph ≤ G.toSimpleGraph := by
  intro u v h
  rcases h with huv | hvu
  · exact Or.inl huv.1
  · exact Or.inr hvu.1

/-- Adding more cut layers can only delete more edges. -/
theorem deleteLayers_mono (G : LayeredDigraph V) {cuts cuts' : Finset Nat}
    (hcuts : cuts ⊆ cuts') :
    (G.deleteLayers cuts').toSimpleGraph ≤ (G.deleteLayers cuts).toSimpleGraph := by
  intro u v h
  rcases h with huv | hvu
  · left
    refine ⟨huv.1, ?_, ?_⟩
    · intro hu
      exact huv.2.1 (hcuts hu)
    · intro hv
      exact huv.2.2 (hcuts hv)
  · right
    refine ⟨hvu.1, ?_, ?_⟩
    · intro hv
      exact hvu.2.1 (hcuts hv)
    · intro hu
      exact hvu.2.2 (hcuts hu)

/-- Successive deletion is equivalent at edge level to deleting the union. -/
theorem deleteLayers_union_edge_iff (G : LayeredDigraph V)
    (first second : Finset Nat) (u v : V) :
    (G.deleteLayers (first ∪ second)).edge u v ↔
      ((G.deleteLayers first).deleteLayers second).edge u v := by
  simp [deleteLayers, Survives, not_or]

/-- A vertex on a cut layer is isolated in the remainder. -/
theorem no_edge_from_cut_vertex (G : LayeredDigraph V) (cuts : Finset Nat)
    {u v : V} (hu : G.layer u ∈ cuts) :
    ¬(G.deleteLayers cuts).edge u v := by
  intro h
  exact h.2.1 hu

/-- A vertex on a cut layer has no incoming edge in the remainder. -/
theorem no_edge_to_cut_vertex (G : LayeredDigraph V) (cuts : Finset Nat)
    {u v : V} (hv : G.layer v ∈ cuts) :
    ¬(G.deleteLayers cuts).edge u v := by
  intro h
  exact h.2.2 hv

end LayeredDigraph
end Allender
