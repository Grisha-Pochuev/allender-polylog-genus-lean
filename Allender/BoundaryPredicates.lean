import Allender.CircuitSegment

/-!
# Initial and accepting boundary predicates

Section 5 of the manuscript separates the first true circuit state, the ordered
macroblock transition relations, and the accepting output test. This file
formalizes the constant-width Boolean predicates at the two ends and proves the
acceptance decomposition for a nonempty layer sequence.
-/

namespace Allender

def InitialStatePredicate {n w : Nat} (first : CircuitLayer n w)
    (x : BitState n) (state : BitState w) : Prop :=
  state = first.eval x (BitState.zero w)

def AcceptingState {w : Nat} (output : Fin w) (state : BitState w) : Prop :=
  state output = true

theorem initialState_iff_transition {n w : Nat} (first : CircuitLayer n w)
    (x : BitState n) (state : BitState w) :
    InitialStatePredicate first x state ↔
      first.transition x (BitState.zero w) state := Iff.rfl

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
    change initial = first.eval x (BitState.zero w) at hinitial
    change final output = true at haccept
    have hfinal : final = evalLayers rest x initial :=
      (segmentRelation_iff_eval rest x initial final).1 hsegment
    rw [hfinal] at haccept
    change evalLayers rest x (first.eval x (BitState.zero w)) output = true
    rw [← hinitial]
    exact haccept

end Allender
