import Allender.CircuitSegment

/-!
# Initial and accepting boundary predicates

Section 5 of the manuscript separates the first true circuit state, the ordered
macroblock transition relations, and the accepting output test. This file
formalizes the constant-width Boolean predicates at the two ends and proves the
acceptance decomposition for a nonempty layer sequence.
-/

namespace Allender

/-- The real state produced by the first layer from the zero dummy boundary. -/
def InitialStatePredicate {n w : Nat} (first : CircuitLayer n w)
    (x : BitState n) (state : BitState w) : Prop :=
  state = first.eval x (BitState.zero w)

/-- A boundary state is accepting when the designated output coordinate is true. -/
def AcceptingState {w : Nat} (output : Fin w) (state : BitState w) : Prop :=
  state output = true

/-- The initial-state predicate is exactly the first layer transition from zero. -/
theorem initialState_iff_transition {n w : Nat} (first : CircuitLayer n w)
    (x : BitState n) (state : BitState w) :
    InitialStatePredicate first x state ↔
      first.transition x (BitState.zero w) state := Iff.rfl

/--
For a nonempty layer list, acceptance is equivalent to choosing the true first
state and a final state connected by the remaining segment relation.
-/
theorem accept_cons_iff_exists_boundary_states {n w : Nat}
    (first : CircuitLayer n w) (rest : List (CircuitLayer n w))
    (output : Fin w) (x : BitState n) :
    evalLayers (first :: rest) x (BitState.zero w) output = true ↔
      ∃ initial final,
        InitialStatePredicate first x initial ∧
          SegmentRelation rest x initial final ∧
            AcceptingState output final := by
  constructor
  · intro h
    let initial := first.eval x (BitState.zero w)
    let final := evalLayers rest x initial
    refine ⟨initial, final, rfl, ?_, ?_⟩
    · exact (segmentRelation_iff_eval rest x initial final).2 rfl
    · simpa [AcceptingState, evalLayers, initial, final] using h
  · rintro ⟨initial, final, hinitial, hsegment, haccept⟩
    have hfinal : final = evalLayers rest x initial :=
      (segmentRelation_iff_eval rest x initial final).1 hsegment
    rw [hfinal] at haccept
    simpa [InitialStatePredicate, AcceptingState, evalLayers, hinitial] using haccept

end Allender
