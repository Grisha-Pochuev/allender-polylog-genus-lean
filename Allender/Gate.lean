import Allender.FiniteState
import Mathlib.Data.Finset.Basic

/-!
# Bounded-fan-in source gates

This source model matches Hansen's constant-width planar circuits: fan-in two
AND/OR gates and fan-in one COPY gates. Input literals, negated literals, and
constants may occur on arbitrary layers, as in the candidate manuscript.
-/

namespace Allender

/-- A source gate in an `n`-input circuit whose previous layer has width `w`. -/
inductive Gate (n w : Nat) where
  | input (index : Fin n) (negated : Bool)
  | constant (value : Bool)
  | copyGate (source : Fin w)
  | andGate (left right : Fin w)
  | orGate (left right : Fin w)
  deriving DecidableEq

namespace Gate

/-- Positions in the preceding layer used by the gate. -/
def parents {n w : Nat} (g : Gate n w) : Finset (Fin w) :=
  match g with
  | .input _ _ => ∅
  | .constant _ => ∅
  | .copyGate source => {source}
  | .andGate left right => {left, right}
  | .orGate left right => {left, right}

/-- Boolean evaluation of one source gate. -/
def eval {n w : Nat} (g : Gate n w) (x : BitState n) (previous : BitState w) : Bool :=
  match g with
  | .input i false => x i
  | .input i true => !(x i)
  | .constant b => b
  | .copyGate source => previous source
  | .andGate left right => previous left && previous right
  | .orGate left right => previous left || previous right

@[simp] theorem parents_input {n w : Nat} (i : Fin n) (negated : Bool) :
    (Gate.input i negated : Gate n w).parents = ∅ := rfl

@[simp] theorem parents_constant {n w : Nat} (b : Bool) :
    (Gate.constant b : Gate n w).parents = ∅ := rfl

@[simp] theorem parents_copy {n w : Nat} (source : Fin w) :
    (Gate.copyGate source : Gate n w).parents = {source} := rfl

@[simp] theorem eval_input_false {n w : Nat} (i : Fin n) (x : BitState n)
    (previous : BitState w) :
    (Gate.input i false : Gate n w).eval x previous = x i := rfl

@[simp] theorem eval_input_true {n w : Nat} (i : Fin n) (x : BitState n)
    (previous : BitState w) :
    (Gate.input i true : Gate n w).eval x previous = !(x i) := rfl

@[simp] theorem eval_constant {n w : Nat} (b : Bool) (x : BitState n)
    (previous : BitState w) :
    (Gate.constant b : Gate n w).eval x previous = b := rfl

@[simp] theorem eval_copy {n w : Nat} (source : Fin w) (x : BitState n)
    (previous : BitState w) :
    (Gate.copyGate source : Gate n w).eval x previous = previous source := rfl

@[simp] theorem eval_and {n w : Nat} (left right : Fin w) (x : BitState n)
    (previous : BitState w) :
    (Gate.andGate left right : Gate n w).eval x previous =
      (previous left && previous right) := rfl

@[simp] theorem eval_or {n w : Nat} (left right : Fin w) (x : BitState n)
    (previous : BitState w) :
    (Gate.orGate left right : Gate n w).eval x previous =
      (previous left || previous right) := rfl

end Gate
end Allender
