import Allender.ACC0Gate

/-!
# Concrete `AC⁰[m]` circuits and `ACC⁰`

Every input length may use a different padded layer width, but all layers of one
circuit have that width. Constant depth and polynomial total padded size are
properties of a nonuniform family. The modulus is fixed for the whole family.
-/

namespace Allender

/-- One padded layer of an `AC⁰[m]` circuit. -/
abbrev ACmLayer (m n s : Nat) := Fin s → ACCGate m n s

namespace ACmLayer

/-- Evaluate all gates of one target-circuit layer. -/
def eval {m n s : Nat} (layer : ACmLayer m n s)
    (x : BitState n) (previous : BitState s) : BitState s :=
  fun i => (layer i).eval x previous

end ACmLayer

/-- A concrete padded, layered `AC⁰[m]` circuit. -/
structure ACmCircuit (m n s : Nat) where
  layers : List (ACmLayer m n s)
  output : Fin s

namespace ACmCircuit

/-- State after all target-circuit layers. -/
def finalState {m n s : Nat} (C : ACmCircuit m n s)
    (x : BitState n) : BitState s :=
  C.layers.foldl (fun previous layer => layer.eval x previous) (BitState.zero s)

/-- Output bit computed by the target circuit. -/
def eval {m n s : Nat} (C : ACmCircuit m n s) (x : BitState n) : Bool :=
  C.finalState x C.output

/-- Number of computational layers. -/
def depth {m n s : Nat} (C : ACmCircuit m n s) : Nat := C.layers.length

/-- Padded gate count. -/
def size {m n s : Nat} (C : ACmCircuit m n s) : Nat := C.layers.length * s

end ACmCircuit

/-- A Boolean language indexed by input length. -/
abbrev BooleanLanguage := (n : Nat) → BitState n → Prop

/-- A nonuniform family with one fixed modulus and variable polynomial width. -/
structure ACmFamily (m : Nat) where
  width : Nat → Nat
  circuit : (n : Nat) → ACmCircuit m n (width n)

namespace ACmFamily

/-- Language computed by a target family. -/
def language {m : Nat} (F : ACmFamily m) : BooleanLanguage :=
  fun n x => (F.circuit n).eval x = true

/-- One depth bound works for all input lengths. -/
def ConstantDepth {m : Nat} (F : ACmFamily m) : Prop :=
  ∃ D : Nat, ∀ n, (F.circuit n).depth ≤ D

/-- The total padded gate count is polynomially bounded. -/
def PolynomialSize {m : Nat} (F : ACmFamily m) : Prop :=
  ∃ k : Nat, ∀ n, (F.circuit n).size ≤ (n + 1) ^ k

/-- Exact recognition of a Boolean language. -/
def Recognizes {m : Nat} (F : ACmFamily m) (L : BooleanLanguage) : Prop :=
  ∀ n x, F.language n x ↔ L n x

end ACmFamily

/-- Membership in one fixed-modulus class `AC⁰[m]`. -/
def InACm (m : Nat) (L : BooleanLanguage) : Prop :=
  2 ≤ m ∧ ∃ F : ACmFamily m,
    F.ConstantDepth ∧ F.PolynomialSize ∧ F.Recognizes L

/-- Nonuniform `ACC⁰`: membership in `AC⁰[m]` for one fixed modulus `m ≥ 2`. -/
def InACC0 (L : BooleanLanguage) : Prop :=
  ∃ m : Nat, InACm m L

end Allender
