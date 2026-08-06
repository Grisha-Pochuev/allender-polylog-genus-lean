import Allender.LayeredWalk
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-!
# Underlying undirected graph

Orientable genus in the manuscript is the genus of the undirected graph obtained
by forgetting circuit-edge directions. Layeredness guarantees that this graph
has no loops.
-/

namespace Allender
namespace LayeredDigraph

variable {V : Type*}

/-- Underlying undirected simple graph of a layered directed graph. -/
def toSimpleGraph (G : LayeredDigraph V) : SimpleGraph V where
  Adj := G.UAdj
  symm := ⟨fun _ _ h => by
    rcases h with huv | hvu
    · exact Or.inr huv
    · exact Or.inl hvu⟩
  loopless := ⟨fun v h => by
    rcases h with hvv | hvv
    · have := G.edge_next hvv
      omega
    · have := G.edge_next hvv
      omega⟩

@[simp] theorem toSimpleGraph_adj (G : LayeredDigraph V) (u v : V) :
    G.toSimpleGraph.Adj u v ↔ G.UAdj u v := Iff.rfl

end LayeredDigraph
end Allender
