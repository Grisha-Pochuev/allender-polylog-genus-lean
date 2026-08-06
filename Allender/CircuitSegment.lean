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

def evalLayers {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) (initial : BitState w) : BitState w :=
  layers.foldl (fun previous layer => layer.eval x previous) initial

def layerRelations {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) : List (Rel (BitState w)) :=
  layers.map fun layer => layer.transition x

def SegmentRelation {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) : Rel (BitState w) :=
  Rel.composeList (layerRelations layers x)

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

theorem segmentRelation_iff_eval {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) (initial final : BitState w) :
    SegmentRelation layers x initial final ↔
      final = evalLayers layers x initial := by
  induction layers generalizing initial with
  | nil =>
      change initial = final ↔ final = initial
      exact eq_comm
  | cons layer layers ih =>
      change
        (∃ middle,
          layer.transition x initial middle ∧
            SegmentRelation layers x middle final) ↔
          final = evalLayers layers x (layer.eval x initial)
      constructor
      · rintro ⟨middle, hhead, htail⟩
        have hmiddle : middle = layer.eval x initial := hhead
        subst middle
        exact (ih (layer.eval x initial)).mp htail
      · intro hfinal
        refine ⟨layer.eval x initial, rfl, ?_⟩
        exact (ih (layer.eval x initial)).mpr hfinal

theorem segmentRelation_functional {n w : Nat} (layers : List (CircuitLayer n w))
    (x : BitState n) : Rel.Functional (SegmentRelation layers x) := by
  intro initial q r hq hr
  have hq' : q = evalLayers layers x initial :=
    (segmentRelation_iff_eval layers x initial q).mp hq
  have hr' : r = evalLayers layers x initial :=
    (segmentRelation_iff_eval layers x initial r).mp hr
  exact hq'.trans hr'.symm

theorem evalLayers_append {n w : Nat} (first second : List (CircuitLayer n w))
    (x : BitState n) (initial : BitState w) :
    evalLayers (first ++ second) x initial =
      evalLayers second x (evalLayers first x initial) := by
  simp [evalLayers, List.foldl_append]

theorem layerRelations_append {n w : Nat}
    (first second : List (CircuitLayer n w)) (x : BitState n) :
    layerRelations (first ++ second) x =
      layerRelations first x ++ layerRelations second x := by
  simp [layerRelations]

theorem segmentRelation_append {n w : Nat}
    (first second : List (CircuitLayer n w)) (x : BitState n)
    (initial final : BitState w) :
    SegmentRelation (first ++ second) x initial final ↔
      ∃ middle, SegmentRelation first x initial middle ∧
        SegmentRelation second x middle final := by
  simp [SegmentRelation, layerRelations, Rel.composeList_append, Rel.comp]

end Allender
