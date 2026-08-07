import Allender.Gate
import Allender.Relation

/-!
# Circuit layers

A layer has exactly `w` padded positions.  Its semantic action is a deterministic
relation on the fixed boundary state space `BitState w`.
-/

namespace Allender

/-- One full width-`w` layer. -/
abbrev CircuitLayer (n w : Nat) := Fin w → Gate n w

namespace CircuitLayer

/-- Evaluate a layer from the external input and previous boundary state. -/
def eval {n w : Nat} (layer : CircuitLayer n w) (x : BitState n)
    (previous : BitState w) : BitState w :=
  fun j => (layer j).eval x previous

/-- The deterministic transition relation induced by a layer. -/
def transition {n w : Nat} (layer : CircuitLayer n w) (x : BitState n) :
    Rel (BitState w) :=
  fun previous next => next = layer.eval x previous

/-- A layer transition is functional. -/
theorem transition_functional {n w : Nat} (layer : CircuitLayer n w)
    (x : BitState n) : Rel.Functional (layer.transition x) := by
  intro previous q r hq hr
  exact hq.trans hr.symm

end CircuitLayer
end Allender
