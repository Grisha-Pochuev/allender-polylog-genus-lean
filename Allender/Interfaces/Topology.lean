import Allender.LayeredGraph
import Mathlib.Data.Nat.Log

/-!
# Topological interface

This is an explicit boundary, not a proof of graph genus theory.  A future module
must instantiate this interface using a formal definition of orientable genus and
prove `planarize_by_layers` from genuine topological lemmas.
-/

namespace Allender

/--
The exact topological deliverable needed by the candidate strategy for one finite
vertex type.  `planarAfterCut G cuts` must eventually mean that deleting all
vertices on the layers in `cuts` leaves a planar graph.
-/
structure TopologyInterface (V : Type*) [Fintype V] where
  genus : LayeredDigraph V → Nat
  planarAfterCut : LayeredDigraph V → Finset Nat → Prop
  planarize_by_layers :
    ∀ G : LayeredDigraph V,
      ∃ cuts : Finset Nat,
        cuts.card ≤ genus G * (Nat.log2 (Fintype.card V + 1) + 1) ∧
          planarAfterCut G cuts

/-- The layer-planarization statement, exposed as a proposition for documentation. -/
def LayerPlanarizationStatement (V : Type*) [Fintype V] : Prop :=
  Nonempty (TopologyInterface V)

end Allender
