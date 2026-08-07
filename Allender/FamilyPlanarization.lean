import Allender.GoodBlockBatch

/-!
# Choosing planarizing layers for an entire circuit family

This module lifts the checked layer-separator theorem from one concrete graph
to a nonuniform circuit family.  The choice is noncomputable, as is appropriate
for the nonuniform complexity class in the statement.
-/

namespace Allender

namespace CircuitFamily

/-- Every family member has at least one dependency-graph vertex.  This is the
nondegeneracy condition required by the current connected-component separator
construction. -/
def NonemptyVertices (F : CircuitFamily) : Prop :=
  ∀ n, Nonempty (F.circuit n).Vertex

/-- An explicit numerical genus bound for every member of a family. -/
def GenusBound (F : CircuitFamily) (g : Nat → Nat) : Prop :=
  ∀ n, OrientableGenus.genus (F.circuit n).layeredGraph.toSimpleGraph ≤ g n

end CircuitFamily

namespace Circuit

/-- Canonically choose the planarizing layer set delivered by the checked
separator theorem. -/
noncomputable def chosenPlanarizingCuts {n w g : Nat} (C : Circuit n w)
    [Nonempty C.Vertex]
    (hgenus : OrientableGenus.genus C.layeredGraph.toSimpleGraph ≤ g) :
    Finset Nat := by
  classical
  letI : DecidableRel C.layeredGraph.edge := by
    intro u v
    unfold Circuit.layeredGraph
    infer_instance
  exact Classical.choose (C.layeredGraph.exists_planarizing_layer_set hgenus)

theorem chosenPlanarizingCuts_card_le {n w g : Nat} (C : Circuit n w)
    [Nonempty C.Vertex]
    (hgenus : OrientableGenus.genus C.layeredGraph.toSimpleGraph ≤ g) :
    (C.chosenPlanarizingCuts hgenus).card ≤
      g * (Nat.log 2 C.size + 1) := by
  classical
  letI : DecidableRel C.layeredGraph.edge := by
    intro u v
    unfold Circuit.layeredGraph
    infer_instance
  simpa [chosenPlanarizingCuts, C.size_eq_card_vertex] using
    (Classical.choose_spec
      (C.layeredGraph.exists_planarizing_layer_set hgenus)).1

theorem chosenPlanarizingCuts_remainder_planar {n w g : Nat}
    (C : Circuit n w) [Nonempty C.Vertex]
    (hgenus : OrientableGenus.genus C.layeredGraph.toSimpleGraph ≤ g) :
    OrientableGenus.IsPlanar
      ((C.layeredGraph.deleteLayers
        (C.chosenPlanarizingCuts hgenus)).toSimpleGraph) := by
  classical
  letI : DecidableRel C.layeredGraph.edge := by
    intro u v
    unfold Circuit.layeredGraph
    infer_instance
  exact (Classical.choose_spec
    (C.layeredGraph.exists_planarizing_layer_set hgenus)).2

end Circuit

/-- Apply the checked separator construction at every input length. -/
noncomputable def CircuitFamily.planarized {F : CircuitFamily} {g : Nat → Nat}
    (hvertices : F.NonemptyVertices) (hgenus : F.GenusBound g) :
    PlanarizedFamily F where
  cuts := fun n => by
    letI : Nonempty (F.circuit n).Vertex := hvertices n
    exact (F.circuit n).chosenPlanarizingCuts (hgenus n)
  remainderPlanar := by
    intro n
    letI : Nonempty (F.circuit n).Vertex := hvertices n
    exact (F.circuit n).chosenPlanarizingCuts_remainder_planar (hgenus n)

/-- Quantitative bound retained by the family-level choice. -/
theorem CircuitFamily.planarized_cuts_card_le {F : CircuitFamily}
    {g : Nat → Nat} (hvertices : F.NonemptyVertices) (hgenus : F.GenusBound g)
    (n : Nat) :
    ((F.planarized hvertices hgenus).cuts n).card ≤
      g n * (Nat.log 2 (F.circuit n).size + 1) := by
  letI : Nonempty (F.circuit n).Vertex := hvertices n
  exact (F.circuit n).chosenPlanarizingCuts_card_le (hgenus n)

end Allender
