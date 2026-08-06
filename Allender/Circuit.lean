import Allender.CircuitLayer
import Allender.RelationChain

/-!
# Layered constant-width circuits

A circuit is a list of width-`w` layers and one designated output coordinate.
Inputs may occur on arbitrary layers because they are gate constructors rather
than separate source vertices.
-/

namespace Allender

/-- A layered Boolean circuit of fixed width. -/
structure Circuit (n w : Nat) where
  layers : List (CircuitLayer n w)
  output : Fin w

namespace Circuit

/-- Evaluate all layers from the all-zero dummy boundary state. -/
def finalState {n w : Nat} (C : Circuit n w) (x : BitState n) : BitState w :=
  C.layers.foldl (fun previous layer => layer.eval x previous) (BitState.zero w)

/-- Boolean value at the designated output coordinate. -/
def eval {n w : Nat} (C : Circuit n w) (x : BitState n) : Bool :=
  C.finalState x C.output

/-- Gate-count size after padding every layer to width `w`. -/
def size {n w : Nat} (C : Circuit n w) : Nat := C.layers.length * w

/-- Ordered list of semantic layer relations. -/
def relations {n w : Nat} (C : Circuit n w) (x : BitState n) :
    List (Rel (BitState w)) :=
  C.layers.map fun layer => layer.transition x

/-- Folding the layer functions supplies an explicit relational witness chain. -/
theorem chain_from_zero_to_final {n w : Nat} (C : Circuit n w) (x : BitState n) :
    Rel.Chain (BitState.zero w) (C.relations x) (C.finalState x) := by
  unfold relations finalState
  generalize BitState.zero w = initial
  induction C.layers generalizing initial with
  | nil =>
      simp
      exact .nil initial
  | cons layer layers ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact .cons rfl (ih (layer.eval x initial))

/-- The composite layer relation sends the zero state to the circuit final state. -/
theorem composeList_zero_final {n w : Nat} (C : Circuit n w) (x : BitState n) :
    Rel.composeList (C.relations x) (BitState.zero w) (C.finalState x) :=
  Rel.chain_iff_composeList.mp (C.chain_from_zero_to_final x)

end Circuit
end Allender
