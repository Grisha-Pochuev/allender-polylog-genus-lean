import Allender.CircuitLayer
import Allender.RelationChain

/-!
# Circuit segments and boundary relations

A macroblock in the manuscript is a consecutive list of circuit layers together
with an incoming and outgoing width-`w` boundary state. This file formalizes
its exact deterministic semantics and proves that concatenating two segments is
relation composition through one shared boundary state.
-/

namespace Allender

/-- Evaluate consecutive circuit layers from an arbitrary boundary state. -/
def evalLayers {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) (initial : BitState w) : BitState w :=
  layers.foldl (fun previous layer => layer.eval x previous) initial

/-- Ordered semantic transition relations of a consecutive layer list. -/
def layerRelations {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) : List (Rel (BitState w)) :=
  layers.map fun layer => layer.transition x

/-- The boundary relation computed by a circuit segment. -/
def SegmentRelation {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) : Rel (BitState w) :=
  Rel.composeList (layerRelations layers x)

/-- Evaluation from an arbitrary initial state supplies a relation-chain witness. -/
theorem chain_from_initial {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) (initial : BitState w) :
    Rel.Chain initial (layerRelations layers x) (evalLayers layers x initial) := by
  unfold layerRelations evalLayers
  induction layers generalizing initial with
  | nil =>
      simp
      exact .nil initial
  | cons layer layers ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact .cons rfl (ih (layer.eval x initial))

/-- The relation of a segment is exactly its deterministic evaluation function. -/
theorem segmentRelation_iff_eval {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) (initial final : BitState w) :
    SegmentRelation layers x initial final ↔
      final = evalLayers layers x initial := by
  induction layers generalizing initial with
  | nil =>
      simp [SegmentRelation, layerRelations, evalLayers, Rel.composeList, Rel.id, eq_comm]
  | cons layer layers ih =>
      simp [SegmentRelation, layerRelations, evalLayers, Rel.composeList, Rel.comp, ih]

/-- Every concrete segment relation is functional. -/
theorem segmentRelation_functional {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) : Rel.Functional (SegmentRelation layers x) := by
  intro initial q r hq hr
  have hq' : q = evalLayers layers x initial :=
    (segmentRelation_iff_eval layers x initial q).mp hq
  have hr' : r = evalLayers layers x initial :=
    (segmentRelation_iff_eval layers x initial r).mp hr
  exact hq'.trans hr'.symm

/-- Evaluating concatenated layer lists equals sequential evaluation of the parts. -/
theorem evalLayers_append {n w : Nat} (first second : List (CircuitLayer n w))
    (x : BitState n) (initial : BitState w) :
    evalLayers (first ++ second) x initial =
      evalLayers second x (evalLayers first x initial) := by
  simp [evalLayers, List.foldl_append]

/-- Transition lists respect concatenation of circuit segments. -/
theorem layerRelations_append {n w : Nat}
    (first second : List (CircuitLayer n w)) (x : BitState n) :
    layerRelations (first ++ second) x =
      layerRelations first x ++ layerRelations second x := by
  simp [layerRelations]

/--
The boundary relation of two concatenated segments is their relational
composition through one shared intermediate state.
-/
theorem segmentRelation_append {n w : Nat}
    (first second : List (CircuitLayer n w)) (x : BitState n)
    (initial final : BitState w) :
    SegmentRelation (first ++ second) x initial final ↔
      ∃ middle, SegmentRelation first x initial middle ∧
        SegmentRelation second x middle final := by
  simp [SegmentRelation, layerRelations, Rel.composeList_append, Rel.comp]

end Allender
