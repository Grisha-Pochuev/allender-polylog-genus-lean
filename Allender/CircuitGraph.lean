import Allender.Circuit
import Allender.LayeredGraph
import Mathlib.Data.Fintype.Card

/-!
# Dependency graph of a layered circuit

Circuit genus is measured on the underlying undirected version of this directed
dependency graph.  Vertices are padded gate positions `(layer, position)` and
edges go from a parent position to a gate in the next layer.
-/

namespace Allender
namespace Circuit

/-- A gate-position vertex of a concrete circuit. -/
abbrev Vertex {n w : Nat} (C : Circuit n w) := Fin C.layers.length × Fin w

/-- The directed dependency graph of a layered circuit. -/
def layeredGraph {n w : Nat} (C : Circuit n w) : LayeredDigraph C.Vertex where
  edge := fun u v =>
    v.1.val = u.1.val + 1 ∧ u.2 ∈ (C.layers.get v.1).parents
  layer := fun v => v.1.val
  edge_next := by
    intro u v h
    exact h.1

/-- The dependency graph has exactly `number of layers × width` vertices. -/
theorem card_vertex {n w : Nat} (C : Circuit n w) :
    Fintype.card C.Vertex = C.layers.length * w := by
  simp [Vertex]

/-- Circuit size agrees with the number of padded graph vertices. -/
theorem size_eq_card_vertex {n w : Nat} (C : Circuit n w) :
    C.size = Fintype.card C.Vertex := by
  rw [C.card_vertex]
  rfl

end Circuit
end Allender
