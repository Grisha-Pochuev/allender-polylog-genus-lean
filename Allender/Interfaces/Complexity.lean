import Allender.FiniteState
import Mathlib.Data.Nat.Log

/-!
# Quantitative complexity interfaces

This file deliberately stops short of defining full Boolean-circuit syntax.  It
records the growth conditions that the final formal statement must use.  The
pending circuit semantics are listed in `docs/proof-obligations.md`.
-/

namespace Allender

/-- A Boolean language, indexed by input length. -/
abbrev Language := ∀ n : Nat, BitState n → Prop

/-- Quantitative data attached to a circuit family. -/
structure FamilyProfile where
  /-- The common constant width. -/
  width : Nat
  /-- Number of gates/wires at input length `n`, according to the chosen size model. -/
  size : Nat → Nat
  /-- Minimum orientable genus of the circuit graph at input length `n`. -/
  genus : Nat → Nat

/-- A deliberately semantic placeholder for a Boolean circuit family. -/
structure CircuitFamily where
  profile : FamilyProfile
  accepts : ∀ n : Nat, BitState n → Bool

/-- The family recognizes exactly the language `L`. -/
def CircuitFamily.Recognizes (F : CircuitFamily) (L : Language) : Prop :=
  ∀ n x, F.accepts n x = true ↔ L n x

/-- Polynomial upper bound, with explicit multiplicative and degree constants. -/
def IsPolynomiallyBounded (f : Nat → Nat) : Prop :=
  ∃ C d : Nat, ∀ n, f n ≤ C * (n + 1) ^ d

/-- Polylogarithmic upper bound.  The shifts make the expression total at `n = 0`. -/
def IsPolylogarithmicallyBounded (f : Nat → Nat) : Prop :=
  ∃ C d : Nat, ∀ n, f n ≤ C * (Nat.log2 (n + 2) + 1) ^ d

/-- The quantitative hypotheses in Allender's question, before circuit syntax is added. -/
def FamilyProfile.IsAllenderSource (p : FamilyProfile) : Prop :=
  IsPolynomiallyBounded p.size ∧ IsPolylogarithmicallyBounded p.genus

end Allender
