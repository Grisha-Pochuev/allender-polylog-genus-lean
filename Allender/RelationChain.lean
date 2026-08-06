import Allender.Relation

/-!
# Explicit intermediate-state semantics

The formula used in the paper expands a composite relation as a disjunction over
all intermediate state sequences, with one conjunction of relation entries per
sequence. `RelChain` is the proposition-level version of that expansion.
-/

namespace Allender
namespace Rel

/-- A witness sequence connecting `a` to `z` through an ordered list of relations. -/
inductive Chain : α → List (Rel α) → α → Prop
  | nil (a : α) : Chain a [] a
  | cons {a b z : α} {R : Rel α} {Rs : List (Rel α)}
      (head : R a b) (tail : Chain b Rs z) : Chain a (R :: Rs) z

/-- `Chain` is exactly the sequential relational composition defined by `composeList`. -/
theorem chain_iff_composeList {a z : α} {Rs : List (Rel α)} :
    Chain a Rs z ↔ composeList Rs a z := by
  induction Rs generalizing a with
  | nil =>
      constructor
      · intro h
        cases h
        rfl
      · intro h
        change a = z at h
        subst z
        exact .nil a
  | cons R Rs ih =>
      constructor
      · intro h
        cases h with
        | cons hhead htail =>
            exact ⟨_, hhead, ih.mp htail⟩
      · rintro ⟨b, hab, htail⟩
        exact .cons hab (ih.mpr htail)

/-- Concatenating two witness chains gives a witness for the concatenated relation list. -/
theorem Chain.append {a b c : α} {Rs Ss : List (Rel α)}
    (h₁ : Chain a Rs b) (h₂ : Chain b Ss c) : Chain a (Rs ++ Ss) c := by
  apply chain_iff_composeList.mpr
  rw [composeList_append]
  exact ⟨b, chain_iff_composeList.mp h₁, chain_iff_composeList.mp h₂⟩

end Rel
end Allender
