import Allender.FiniteState

/-!
# Binary relations and sequential composition

A width-`w` circuit segment is represented semantically by a relation on the finite
state space `BitState w`.  These lemmas are independent of circuit syntax and will
be reused by every later simulation theorem.
-/

namespace Allender

/-- A binary relation on `α`. -/
abbrev Rel (α : Type*) := α → α → Prop

namespace Rel

/-- Identity relation. -/
def id : Rel α := fun a b => a = b

/-- Sequential composition: first `R`, then `S`. -/
def comp (R S : Rel α) : Rel α := fun a c => ∃ b, R a b ∧ S b c

/-- Extensional equality of relations. -/
theorem ext {R S : Rel α} (h : ∀ a b, R a b ↔ S a b) : R = S := by
  funext a b
  exact propext (h a b)

@[simp] theorem id_comp (R : Rel α) : comp id R = R := by
  apply ext
  intro a b
  constructor
  · rintro ⟨m, rfl, h⟩
    exact h
  · intro h
    exact ⟨a, rfl, h⟩

@[simp] theorem comp_id (R : Rel α) : comp R id = R := by
  apply ext
  intro a b
  constructor
  · rintro ⟨m, h, rfl⟩
    exact h
  · intro h
    exact ⟨b, h, rfl⟩

/-- Relation composition is associative. -/
theorem comp_assoc (R S T : Rel α) : comp (comp R S) T = comp R (comp S T) := by
  apply ext
  intro a d
  constructor
  · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, c, hbc, hcd⟩
  · rintro ⟨b, hab, c, hbc, hcd⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

/-- Sequential semantics of a list of relations. -/
def composeList : List (Rel α) → Rel α
  | [] => id
  | R :: Rs => comp R (composeList Rs)

@[simp] theorem composeList_nil : composeList ([] : List (Rel α)) = id := rfl

@[simp] theorem composeList_cons (R : Rel α) (Rs : List (Rel α)) :
    composeList (R :: Rs) = comp R (composeList Rs) := rfl

/-- Splitting a sequence does not change its relational semantics. -/
theorem composeList_append (Rs Ss : List (Rel α)) :
    composeList (Rs ++ Ss) = comp (composeList Rs) (composeList Ss) := by
  induction Rs with
  | nil => simp
  | cons R Rs ih =>
      simp [ih, comp_assoc]

/-- A relation is functional if every input has at most one output. -/
def Functional (R : Rel α) : Prop :=
  ∀ a b c, R a b → R a c → b = c

/-- Sequential composition preserves functionality. -/
theorem Functional.comp {R S : Rel α} (hR : Functional R) (hS : Functional S) :
    Functional (comp R S) := by
  intro a c d hac had
  rcases hac with ⟨b, hab, hbc⟩
  rcases had with ⟨b', hab', hb'd⟩
  have hbb' : b = b' := hR a b b' hab hab'
  subst b'
  exact hS b c d hbc hb'd

end Rel
end Allender
