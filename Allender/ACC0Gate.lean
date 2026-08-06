import Allender.FiniteState
import Mathlib.Data.Finset.Basic

/-!
# Gates for `AC⁰[m]`

The target model uses unbounded-fan-in AND and OR, arbitrary NOT gates, and a
fixed modular counting gate. A `modGate` is true exactly when the number of true
predecessors is divisible by `m`.
-/

namespace Allender

/-- A gate in one fixed-width layer of an `AC⁰[m]` circuit. -/
inductive ACCGate (m n s : Nat) where
  | input (index : Fin n)
  | constant (value : Bool)
  | notGate (input : Fin s)
  | andGate (inputs : Finset (Fin s))
  | orGate (inputs : Finset (Fin s))
  | modGate (inputs : Finset (Fin s))
  deriving DecidableEq

namespace ACCGate

/-- Number of selected predecessor coordinates whose value is true. -/
def trueCount {s : Nat} (inputs : Finset (Fin s)) (previous : BitState s) : Nat :=
  (inputs.filter fun i => previous i = true).card

/-- Boolean semantics of one fixed-modulus gate. -/
def eval {m n s : Nat} (g : ACCGate m n s)
    (x : BitState n) (previous : BitState s) : Bool :=
  match g with
  | .input i => x i
  | .constant b => b
  | .notGate i => !(previous i)
  | .andGate inputs => decide (∀ i ∈ inputs, previous i = true)
  | .orGate inputs => decide (∃ i ∈ inputs, previous i = true)
  | .modGate inputs => decide (trueCount inputs previous % m = 0)

@[simp] theorem eval_input {m n s : Nat} (i : Fin n)
    (x : BitState n) (previous : BitState s) :
    (ACCGate.input i : ACCGate m n s).eval x previous = x i := rfl

@[simp] theorem eval_constant {m n s : Nat} (b : Bool)
    (x : BitState n) (previous : BitState s) :
    (ACCGate.constant b : ACCGate m n s).eval x previous = b := rfl

@[simp] theorem eval_not {m n s : Nat} (i : Fin s)
    (x : BitState n) (previous : BitState s) :
    (ACCGate.notGate i : ACCGate m n s).eval x previous = !(previous i) := rfl

end ACCGate
end Allender
