import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Bool.Basic

/-!
# Fixed-width Boolean states

A constant-width Boolean circuit has only finitely many possible layer states.  This
file fixes the basic representation used by the later relation semantics.
-/

namespace Allender

/-- A Boolean state of width `w`. -/
abbrev BitState (w : Nat) := Fin w → Bool

instance (w : Nat) : Fintype (BitState w) := inferInstance
instance (w : Nat) : DecidableEq (BitState w) := inferInstance

namespace BitState

/-- The all-zero state. -/
def zero (w : Nat) : BitState w := fun _ => false

/-- Replace one coordinate of a state. -/
def update {w : Nat} (s : BitState w) (i : Fin w) (b : Bool) : BitState w :=
  Function.update s i b

@[simp] theorem zero_apply {w : Nat} (i : Fin w) : zero w i = false := rfl

@[simp] theorem update_same {w : Nat} (s : BitState w) (i : Fin w) (b : Bool) :
    update s i b i = b := by
  simp [update]

@[simp] theorem update_ne {w : Nat} (s : BitState w) {i j : Fin w} (h : j ≠ i)
    (b : Bool) : update s i b j = s j := by
  simp [update, h]

/-- Pointwise equality is equality of states. -/
theorem ext {w : Nat} {s t : BitState w} (h : ∀ i, s i = t i) : s = t :=
  funext h

/-- There are exactly `2^w` Boolean states of width `w`. -/
theorem card (w : Nat) : Fintype.card (BitState w) = 2 ^ w := by
  simp [BitState, Fintype.card_pi]

end BitState
end Allender
