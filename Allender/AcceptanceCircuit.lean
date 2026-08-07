import Allender.MacroblockCompositionCircuit
import Allender.MacroblockCompositionRounds

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

/-- Acceptance checker using the multi-round macroblock composite. -/
noncomputable def roundedAcceptingPairCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (hne : (F.circuit n).layers ≠ [])
    (L rounds : Nat) (initial final : BitState F.width) :
    PackedACmCircuit m n :=
  PackedACmCircuit.conjoinParallel
    [((F.circuit n).layers.head hne).initialBoundaryCircuit m initial,
      (P.roundedComposedMacroblockCircuit A hsim hn L rounds
        initial final).normalize,
      PackedACmCircuit.constant m n (final (F.circuit n).output)]

theorem roundedAcceptingPairCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (hne : (F.circuit n).layers ≠ [])
    (L : Nat) (hL : 0 < L) (rounds : Nat)
    (initial final : BitState F.width) (x : BitState n) :
    (P.roundedAcceptingPairCircuit A hsim hn hne L rounds
      initial final).circuit.eval x = true ↔
      InitialStatePredicate ((F.circuit n).layers.head hne) x initial ∧
      Rel.composeList ((F.circuit n).macroblockRelations (P.cuts n) x)
        initial final ∧
      AcceptingState (F.circuit n).output final := by
  rw [roundedAcceptingPairCircuit,
    PackedACmCircuit.conjoinParallel_eval_eq_true_iff]
  constructor
  · intro hall
    have hinitial := hall
      (((F.circuit n).layers.head hne).initialBoundaryCircuit m initial)
      (by simp)
    have hblocks := hall
      (P.roundedComposedMacroblockCircuit A hsim hn L rounds
        initial final).normalize
      (by simp)
    have haccept := hall
      (PackedACmCircuit.constant m n (final (F.circuit n).output))
      (by simp)
    rw [CircuitLayer.initialBoundaryCircuit_eval_iff] at hinitial
    rw [PackedACmCircuit.normalize_eval,
      P.roundedComposedMacroblockCircuit_eval_iff A hsim hn L hL rounds
      initial final x] at hblocks
    exact ⟨hinitial, hblocks, by simpa [AcceptingState] using haccept⟩
  · rintro ⟨hinitial, hblocks, haccept⟩ C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with hC | hC | hC
    · subst C
      exact (CircuitLayer.initialBoundaryCircuit_eval_iff
        m _ initial x).2 hinitial
    · subst C
      rw [PackedACmCircuit.normalize_eval]
      exact (P.roundedComposedMacroblockCircuit_eval_iff A hsim hn L hL
        rounds initial final x).2 hblocks
    · subst C
      simpa [AcceptingState] using haccept

/-- Disjoin all constant-width endpoint pairs after multi-round composition. -/
noncomputable def roundedAcceptanceCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (hne : (F.circuit n).layers ≠ [])
    (L rounds : Nat) : PackedACmCircuit m n :=
  PackedACmCircuit.disjoinParallel
    ((Finset.univ : Finset (BitState F.width × BitState F.width)).toList.map
      fun states => P.roundedAcceptingPairCircuit A hsim hn hne L rounds
        states.1 states.2)

/-- Exact end-to-end semantics of the multi-round construction. -/
theorem roundedAcceptanceCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (hne : (F.circuit n).layers ≠ [])
    (L : Nat) (hL : 0 < L) (rounds : Nat) (x : BitState n) :
    (P.roundedAcceptanceCircuit A hsim hn hne L rounds).circuit.eval x = true ↔
      (F.circuit n).eval x = true := by
  rw [roundedAcceptanceCircuit,
    PackedACmCircuit.disjoinParallel_eval_eq_true_iff]
  rw [(F.circuit n).accept_iff_macroblockRelations_of_ne_nil
    hne (P.cuts n) x]
  constructor
  · rintro ⟨C, hCmem, hC⟩
    rw [List.mem_map] at hCmem
    rcases hCmem with ⟨states, _hstatesMem, rfl⟩
    rw [P.roundedAcceptingPairCircuit_eval_iff A hsim hn hne L hL rounds
      states.1 states.2 x] at hC
    exact ⟨states.1, states.2, hC⟩
  · rintro ⟨initial, final, hstates⟩
    refine ⟨P.roundedAcceptingPairCircuit A hsim hn hne L rounds
      initial final, ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨(initial, final), by simp, rfl⟩
    · exact (P.roundedAcceptingPairCircuit_eval_iff A hsim hn hne L hL
        rounds initial final x).2 hstates

/-- Uniform depth of one endpoint-pair checker. -/
theorem roundedAcceptingPairCircuit_depth_le
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (hne : (F.circuit n).layers ≠ [])
    (L : Nat) (hL : 0 < L) (rounds D : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D)
    (initial final : BitState F.width) :
    (P.roundedAcceptingPairCircuit A hsim hn hne L rounds
      initial final).circuit.depth ≤ D + 11 + 5 * rounds := by
  unfold roundedAcceptingPairCircuit
  have hcomponents : ∀ C ∈
      [((F.circuit n).layers.head hne).initialBoundaryCircuit m initial,
        (P.roundedComposedMacroblockCircuit A hsim hn L rounds
          initial final).normalize,
        PackedACmCircuit.constant m n (final (F.circuit n).output)],
      C.circuit.depth ≤ D + 10 + 5 * rounds := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl
    · exact (((F.circuit n).layers.head hne).relationCircuit_depth_le
        m (BitState.zero F.width) initial).trans (by omega)
    · exact (PackedACmCircuit.normalize_depth_le _).trans
        ((Nat.add_le_add_right
          (P.roundedComposedMacroblockCircuit_depth_le A hsim hn L hL
            rounds D hdepth initial final) 1).trans (by omega))
    · simp [PackedACmCircuit.constant, ACmCircuit.depth]
      omega
  exact (PackedACmCircuit.conjoinParallel_depth_le _
    (D + 10 + 5 * rounds) hcomponents).trans (by omega)

/-- The full endpoint disjunction still has constant depth. -/
theorem roundedAcceptanceCircuit_depth_le
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (hne : (F.circuit n).layers ≠ [])
    (L : Nat) (hL : 0 < L) (rounds D : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D) :
    (P.roundedAcceptanceCircuit A hsim hn hne L rounds).circuit.depth ≤
      D + 14 + 5 * rounds := by
  unfold roundedAcceptanceCircuit
  have hcomponents : ∀ C ∈
      ((Finset.univ : Finset (BitState F.width × BitState F.width)).toList.map
        fun states => P.roundedAcceptingPairCircuit A hsim hn hne L rounds
          states.1 states.2),
      C.circuit.depth ≤ D + 11 + 5 * rounds := by
    intro C hC
    rw [List.mem_map] at hC
    rcases hC with ⟨states, _hstates, rfl⟩
    exact P.roundedAcceptingPairCircuit_depth_le A hsim hn hne L hL
      rounds D hdepth states.1 states.2
  exact (PackedACmCircuit.disjoinParallel_depth_le _
    (D + 11 + 5 * rounds) hcomponents).trans (by omega)

/-- Width of one endpoint-pair checker, expressed through a bound for the
final rounded relation entry. -/
theorem roundedAcceptingPairCircuit_width_le
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (hne : (F.circuit n).layers ≠ [])
    (L rounds B : Nat) (initial final : BitState F.width)
    (hcomposed :
      (P.roundedComposedMacroblockCircuit A hsim hn L rounds
        initial final).circuit.size ≤ B) :
    (P.roundedAcceptingPairCircuit A hsim hn hne L rounds
      initial final).width ≤ F.width + B + 4 := by
  unfold roundedAcceptingPairCircuit
  have hinitial :
      (((F.circuit n).layers.head hne).initialBoundaryCircuit m initial).width ≤
        F.width + 1 :=
    ((F.circuit n).layers.head hne).relationCircuit_width_le
      m (BitState.zero F.width) initial
  have hmiddle :
      (P.roundedComposedMacroblockCircuit A hsim hn L rounds
        initial final).normalize.width ≤ B + 1 :=
    (PackedACmCircuit.normalize_width_le _).trans
      (Nat.add_le_add_right hcomposed 1)
  calc
    (PackedACmCircuit.conjoinParallel
        [((F.circuit n).layers.head hne).initialBoundaryCircuit m initial,
          (P.roundedComposedMacroblockCircuit A hsim hn L rounds
            initial final).normalize,
          PackedACmCircuit.constant m n
            (final (F.circuit n).output)]).width
        ≤ (((F.circuit n).layers.head hne).initialBoundaryCircuit m initial).width +
          (P.roundedComposedMacroblockCircuit A hsim hn L rounds
            initial final).normalize.width + 2 := by
          have := PackedACmCircuit.conjoinParallel_width_le
            [((F.circuit n).layers.head hne).initialBoundaryCircuit m initial,
              (P.roundedComposedMacroblockCircuit A hsim hn L rounds
                initial final).normalize,
              PackedACmCircuit.constant m n
                (final (F.circuit n).output)]
          have hs := this
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            Nat.add_zero, PackedACmCircuit.constant] at hs
          exact hs.trans (by omega)
    _ ≤ F.width + B + 4 := by omega

private theorem sum_width_le_length_mul
    (circuits : List (PackedACmCircuit m n)) (W : Nat)
    (hwidth : ∀ C ∈ circuits, C.width ≤ W) :
    (circuits.map PackedACmCircuit.width).sum ≤ circuits.length * W := by
  induction circuits with
  | nil => simp
  | cons first rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        first.width + (rest.map PackedACmCircuit.width).sum ≤
            W + rest.length * W :=
          Nat.add_le_add (hwidth first (by simp))
            (ih (fun C hC => hwidth C (by simp [hC])))
        _ = (rest.length + 1) * W := by ring

/-- Explicit padded-width bound for the full endpoint disjunction. -/
theorem roundedAcceptanceCircuit_width_le
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (hne : (F.circuit n).layers ≠ [])
    (L rounds B : Nat)
    (hcomposed : ∀ initial final : BitState F.width,
      (P.roundedComposedMacroblockCircuit A hsim hn L rounds
        initial final).circuit.size ≤ B) :
    (P.roundedAcceptanceCircuit A hsim hn hne L rounds).width ≤
      (Fintype.card (BitState F.width × BitState F.width)) *
        (F.width + B + 4) + 1 := by
  let circuits :=
    (Finset.univ : Finset (BitState F.width × BitState F.width)).toList.map
      fun states => P.roundedAcceptingPairCircuit A hsim hn hne L rounds
        states.1 states.2
  have hpairs : ∀ C ∈ circuits, C.width ≤ F.width + B + 4 := by
    intro C hC
    simp only [circuits, List.mem_map] at hC
    rcases hC with ⟨states, _hstates, rfl⟩
    exact P.roundedAcceptingPairCircuit_width_le A hsim hn hne L rounds B
      states.1 states.2 (hcomposed states.1 states.2)
  unfold roundedAcceptanceCircuit
  change (PackedACmCircuit.disjoinParallel circuits).width ≤ _
  calc
    (PackedACmCircuit.disjoinParallel circuits).width ≤
        (circuits.map PackedACmCircuit.width).sum + 1 :=
      PackedACmCircuit.disjoinParallel_width_le circuits
    _ ≤ circuits.length * (F.width + B + 4) + 1 :=
      Nat.add_le_add_right (sum_width_le_length_mul circuits _ hpairs) 1
    _ = Fintype.card (BitState F.width × BitState F.width) *
        (F.width + B + 4) + 1 := by simp [circuits]

/-- End-to-end gate-count bound after the canonical macroblock count has been
absorbed by the chosen rounds. -/
theorem roundedAcceptanceCircuit_size_le
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (hne : (F.circuit n).layers ≠ [])
    (L : Nat) (hL : 0 < L) (rounds D S : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D)
    (hsize : ∀ t, (A.circuit n t).size ≤ S)
    (hcount :
      (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).length ≤
        L ^ rounds) :
    let B := RealizedRelation.nextSizeBound (BitState F.width) 1
      (D + 4 + 5 * rounds)
      (RealizedRelation.roundsSizeBound (BitState F.width) L rounds
        (D + 4) (macroblockRelationSizeBound F.width D S))
    (P.roundedAcceptanceCircuit A hsim hn hne L rounds).circuit.size ≤
      (D + 14 + 5 * rounds) *
        (Fintype.card (BitState F.width × BitState F.width) *
          (F.width + B + 4) + 1) := by
  dsimp only
  apply Nat.mul_le_mul
  · exact P.roundedAcceptanceCircuit_depth_le A hsim hn hne L hL
      rounds D hdepth
  · apply P.roundedAcceptanceCircuit_width_le A hsim hn hne
    intro initial final
    exact P.roundedComposedMacroblockCircuit_size_le A hsim hn L hL
      rounds D S hdepth hsize hcount initial final

end PlanarizedFamily
end Allender
