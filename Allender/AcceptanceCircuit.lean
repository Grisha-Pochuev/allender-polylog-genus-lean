import Allender.MacroblockCompositionCircuit

/-!
# End-to-end target circuit semantics

The first source layer, the composed canonical macroblocks, and the final
output test are joined here into one concrete target circuit.  This is the
semantic end-to-end theorem; uniform depth and polynomial-size bounds are
proved separately at the family level.
-/

namespace Allender

namespace CircuitLayer

/-- Direct target circuit for the first-layer boundary predicate. -/
def initialBoundaryCircuit {n w : Nat} (m : Nat)
    (first : CircuitLayer n w) (state : BitState w) :
    PackedACmCircuit m n :=
  first.relationCircuit m (BitState.zero w) state

theorem initialBoundaryCircuit_eval_iff {n w : Nat} (m : Nat)
    (first : CircuitLayer n w) (state : BitState w) (x : BitState n) :
    (first.initialBoundaryCircuit m state).circuit.eval x = true ↔
      InitialStatePredicate first x state := by
  rw [initialBoundaryCircuit, relationCircuit_eval_iff,
    segmentRelation_iff_eval]
  rfl

end CircuitLayer

namespace Circuit

/-- Acceptance decomposition specialized to an arbitrary circuit whose layer
list is known to be nonempty. -/
theorem accept_iff_macroblockRelations_of_ne_nil {n w : Nat}
    (C : Circuit n w) (hne : C.layers ≠ []) (cuts : Finset Nat)
    (x : BitState n) :
    C.eval x = true ↔
      ∃ initial final,
        InitialStatePredicate (C.layers.head hne) x initial ∧
          Rel.composeList (C.macroblockRelations cuts x) initial final ∧
            AcceptingState C.output final := by
  rcases C with ⟨layers, output⟩
  cases layers with
  | nil => contradiction
  | cons first rest =>
      simpa using accept_cons_iff_macroblockRelations
        first rest output cuts x

end Circuit

namespace PlanarizedFamily

/-- Check one selected pair of first/last boundary states. -/
noncomputable def acceptingPairCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (hne : (F.circuit n).layers ≠ [])
    (initial final : BitState F.width) : PackedACmCircuit m n :=
  PackedACmCircuit.conjoinParallel
    [((F.circuit n).layers.head hne).initialBoundaryCircuit m initial,
      P.composedMacroblockCircuit A hn initial final,
      PackedACmCircuit.constant m n (final (F.circuit n).output)]

theorem acceptingPairCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (hne : (F.circuit n).layers ≠ [])
    (initial final : BitState F.width) (x : BitState n) :
    (P.acceptingPairCircuit A hn hne initial final).circuit.eval x = true ↔
      InitialStatePredicate ((F.circuit n).layers.head hne) x initial ∧
      Rel.composeList ((F.circuit n).macroblockRelations (P.cuts n) x)
        initial final ∧
      AcceptingState (F.circuit n).output final := by
  rw [acceptingPairCircuit,
    PackedACmCircuit.conjoinParallel_eval_eq_true_iff]
  constructor
  · intro hall
    have hinitial := hall
      (((F.circuit n).layers.head hne).initialBoundaryCircuit m initial)
      (by simp)
    have hblocks := hall (P.composedMacroblockCircuit A hn initial final)
      (by simp)
    have haccept := hall
      (PackedACmCircuit.constant m n (final (F.circuit n).output))
      (by simp)
    rw [CircuitLayer.initialBoundaryCircuit_eval_iff] at hinitial
    rw [P.composedMacroblockCircuit_eval_iff
      A hsim hn initial final x] at hblocks
    exact ⟨hinitial, hblocks, by simpa [AcceptingState] using haccept⟩
  · rintro ⟨hinitial, hblocks, haccept⟩ C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with hC | hC | hC
    · subst C
      exact (CircuitLayer.initialBoundaryCircuit_eval_iff
        m _ initial x).2 hinitial
    · subst C
      exact (P.composedMacroblockCircuit_eval_iff
        A hsim hn initial final x).2 hblocks
    · subst C
      simpa [AcceptingState] using haccept

/-- Disjoin all pairs of constant-width boundary states. -/
noncomputable def acceptanceCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (hne : (F.circuit n).layers ≠ []) : PackedACmCircuit m n :=
  PackedACmCircuit.disjoinParallel
    ((Finset.univ : Finset (BitState F.width × BitState F.width)).toList.map
      fun states => P.acceptingPairCircuit A hn hne states.1 states.2)

/-- Exact end-to-end semantic correctness of the constructed target circuit. -/
theorem acceptanceCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (hne : (F.circuit n).layers ≠ [])
    (x : BitState n) :
    (P.acceptanceCircuit A hn hne).circuit.eval x = true ↔
      (F.circuit n).eval x = true := by
  rw [acceptanceCircuit,
    PackedACmCircuit.disjoinParallel_eval_eq_true_iff]
  rw [(F.circuit n).accept_iff_macroblockRelations_of_ne_nil
    hne (P.cuts n) x]
  constructor
  · rintro ⟨C, hCmem, hC⟩
    rw [List.mem_map] at hCmem
    rcases hCmem with ⟨states, _hstatesMem, rfl⟩
    have hstates := hC
    rw [P.acceptingPairCircuit_eval_iff A hsim hn hne
      states.1 states.2 x] at hstates
    exact ⟨states.1, states.2, hstates⟩
  · rintro ⟨initial, final, hstates⟩
    refine ⟨P.acceptingPairCircuit A hn hne initial final, ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨(initial, final), by simp, rfl⟩
    · exact (P.acceptingPairCircuit_eval_iff A hsim hn hne
          initial final x).2 hstates

end PlanarizedFamily
end Allender
