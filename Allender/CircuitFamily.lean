import Allender.Circuit

/-!
# Nonuniform circuit families

Unlike the deleted placeholder model, a language here is defined from actual
circuits.  Width is fixed once for the whole family and the size bound is a
property of those circuits.
-/

namespace Allender

/-- A nonuniform family with one fixed width and one concrete circuit per input length. -/
structure CircuitFamily where
  width : Nat
  circuit : (n : Nat) → Circuit n width

namespace CircuitFamily

/-- The Boolean language computed by the family. -/
def language (F : CircuitFamily) (n : Nat) (x : BitState n) : Prop :=
  (F.circuit n).eval x = true

/-- Explicit polynomial gate-count bound. -/
def PolynomialSize (F : CircuitFamily) : Prop :=
  ∃ k : Nat, ∀ n, (F.circuit n).size ≤ (n + 1) ^ k

end CircuitFamily
end Allender
