import Allender.FiniteState
import Mathlib.Data.Finset.Boolean

/-!
# Boolean gates

The source-circuit model from the manuscript uses AND, OR, input literals,
negated input literals, and constants.  AND and OR gates read only the
immediately preceding width-`w` state.
-/

namespace Allender

/-- A gate in an `n`-input circuit whose previous layer has width `w`. -/
inductive Gate (n w : Nat) where
  | input (index : Fin n) (negated : Bool)
  | constant (value : Bool)
  | andGate (inputs : Finset (Fin w))
  | orGate (inputs : Finset (Fin w))
  deriving DecidableEq

namespace Gate

/-- Positions in the preceding layer used by the gate. -/
def parents {n w : Nat} (g : Gate n w) : Finset (Fin w) :=
  match g with
  | .input _ _ => ∅
  | .constant _ => ∅
  | .andGate inputs => inputs
  | .orGate inputs => inputs

/-- Boolean evaluation of one gate. -/
def eval {n w : Nat} (g : Gate n w) (x : BitState n) (previous : BitState w) : Bool :=
  match g with
  | .input i false => x i
  | .input i true => !(x i)
  | .constant b => b
  | .andGate inputs => inputs.all fun i => previous i
  | .orGate inputs => inputs.any fun i => previous i

@[simp] theorem parents_input {n w : Nat} (i : Fin n) (negated : Bool) :
    (Gate.input i negated : Gate n w).parents = ∅ := rfl

@[simp] theorem parents_constant {n w : Nat} (b : Bool) :
    (Gate.constant b : Gate n w).parents = ∅ := rfl

@[simp] theorem eval_input_false {n w : Nat} (i : Fin n) (x : BitState n)
    (previous : BitState w) :
    (Gate.input i false : Gate n w).eval x previous = x i := rfl

@[simp] theorem eval_input_true {n w : Nat} (i : Fin n) (x : BitState n)
    (previous : BitState w) :
    (Gate.input i true : Gate n w).eval x previous = !(x i) := rfl

@[simp] theorem eval_constant {n w : Nat} (b : Bool) (x : BitState n)
    (previous : BitState w) :
    (Gate.constant b : Gate n w).eval x previous = b := rfl

end Gate
end Allender
