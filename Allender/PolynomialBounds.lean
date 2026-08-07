import Allender.RelationCompositionRounds
import Allender.StateEnumeration
import Allender.MacroblockRelationCircuits

/-!
# Elementary polynomial-bound calculus

The final family estimates are nonuniform and only need positive input
lengths; length zero is handled by a fixed constant circuit.  This file keeps
all exponent absorption explicit and verifies that the multi-round numerical
recurrence remains polynomial.
-/

namespace Allender

private theorem nat_le_two_pow (c : Nat) : c ≤ 2 ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
      calc
        c + 1 ≤ 2 ^ c + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ c + 2 ^ c :=
          Nat.add_le_add_left (Nat.one_le_pow _ _ (by omega)) _
        _ = 2 ^ (c + 1) := by ring

/-- A numerical function is polynomially bounded on positive input lengths. -/
def PositivePolynomialBound (f : Nat → Nat) : Prop :=
  ∃ k, ∀ n, 1 ≤ n → f n ≤ (n + 1) ^ k

namespace PositivePolynomialBound

theorem constant (c : Nat) : PositivePolynomialBound (fun _ => c) := by
  refine ⟨c, ?_⟩
  intro n hn
  exact (nat_le_two_pow c).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ n + 1) c)

theorem mono {f g : Nat → Nat} (hg : PositivePolynomialBound g)
    (hfg : ∀ n, 1 ≤ n → f n ≤ g n) : PositivePolynomialBound f := by
  rcases hg with ⟨k, hk⟩
  exact ⟨k, fun n hn => (hfg n hn).trans (hk n hn)⟩

theorem add {f g : Nat → Nat} (hf : PositivePolynomialBound f)
    (hg : PositivePolynomialBound g) :
    PositivePolynomialBound (fun n => f n + g n) := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  refine ⟨a + b + 1, ?_⟩
  intro n hn
  let N := n + 1
  have hN : 2 ≤ N := by omega
  have hfa : f n ≤ N ^ (a + b) :=
    (ha n hn).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hgb : g n ≤ N ^ (a + b) :=
    (hb n hn).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    f n + g n ≤ 2 * N ^ (a + b) := by omega
    _ ≤ N * N ^ (a + b) := Nat.mul_le_mul_right _ hN
    _ = N ^ (a + b + 1) := by ring

theorem mul {f g : Nat → Nat} (hf : PositivePolynomialBound f)
    (hg : PositivePolynomialBound g) :
    PositivePolynomialBound (fun n => f n * g n) := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  intro n hn
  calc
    f n * g n ≤ (n + 1) ^ a * (n + 1) ^ b :=
      Nat.mul_le_mul (ha n hn) (hb n hn)
    _ = (n + 1) ^ (a + b) := by rw [← pow_add]

theorem pow {f : Nat → Nat} (hf : PositivePolynomialBound f) (r : Nat) :
    PositivePolynomialBound (fun n => (f n) ^ r) := by
  rcases hf with ⟨a, ha⟩
  refine ⟨a * r, ?_⟩
  intro n hn
  exact (Nat.pow_le_pow_left (ha n hn) r).trans_eq (by rw [pow_mul])

theorem inputPower (k : Nat) :
    PositivePolynomialBound (fun n => (n + 1) ^ k) :=
  ⟨k, fun _ _ => le_rfl⟩

end PositivePolynomialBound

/-- The positive logarithmic block length used by the reduction. -/
def logarithmicBlockLength (C n : Nat) : Nat :=
  C * (Nat.log 2 (n + 2) + 1)

theorem logarithmicBlockLength_pos (C n : Nat) (hC : 0 < C) :
    0 < logarithmicBlockLength C n := by
  unfold logarithmicBlockLength
  positivity

/-- A logarithmic block length is itself polynomially bounded. -/
theorem logarithmicBlockLength_polynomial (C : Nat) :
    PositivePolynomialBound (logarithmicBlockLength C) := by
  apply PositivePolynomialBound.mul
  · exact PositivePolynomialBound.constant C
  · refine ⟨2, ?_⟩
    intro n hn
    calc
      Nat.log 2 (n + 2) + 1 ≤ n + 2 := by
        have := Nat.log_lt_self 2 (by omega : n + 2 ≠ 0)
        omega
      _ ≤ (n + 1) ^ 2 := by nlinarith

/-- Enumerating all fixed-width trajectories through a constant multiple of
`log n` positions is polynomial. -/
theorem bitState_trajectory_polynomial (w C : Nat) :
    PositivePolynomialBound (fun n =>
      (Fintype.card (BitState w)) ^ (logarithmicBlockLength C n + 1)) := by
  let q := 2 ^ w
  refine ⟨q + (q + 2 * w) * C, ?_⟩
  intro n hn
  let N := n + 1
  let ell := Nat.log 2 (n + 2) + 1
  have hN : 2 ≤ N := by omega
  have hn2 : n + 2 ≤ N ^ 2 := by
    dsimp [N]
    nlinarith
  have hq : q ≤ N ^ q :=
    (nat_le_two_pow q).trans (Nat.pow_le_pow_left hN q)
  have hlog : q ^ Nat.log 2 (n + 2) ≤ (n + 2) ^ w := by
    simpa [q, BitState.card] using card_stateAssignments_log_le w n
  have hell : q ^ ell ≤ N ^ (q + 2 * w) := by
    calc
      q ^ ell = q ^ Nat.log 2 (n + 2) * q := by
        simp [ell, pow_succ]
      _ ≤ (n + 2) ^ w * q := Nat.mul_le_mul_right q hlog
      _ ≤ (N ^ 2) ^ w * N ^ q :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hn2 w) hq
      _ = N ^ (q + 2 * w) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
  simp only [BitState.card, logarithmicBlockLength]
  change q ^ (C * ell + 1) ≤ N ^ (q + (q + 2 * w) * C)
  calc
    q ^ (C * ell + 1) = q * (q ^ ell) ^ C := by
      rw [pow_add, pow_one, Nat.mul_comm C ell, pow_mul, Nat.mul_comm]
    _ ≤ N ^ q * (N ^ (q + 2 * w)) ^ C :=
      Nat.mul_le_mul hq (Nat.pow_le_pow_left hell C)
    _ = N ^ (q + (q + 2 * w) * C) := by
      rw [← pow_mul, ← pow_add]

/-- One relation-composition size step preserves polynomial boundedness. -/
theorem nextSizeBound_polynomial (w C D : Nat) {S : Nat → Nat}
    (hS : PositivePolynomialBound S) :
    PositivePolynomialBound (fun n =>
      RealizedRelation.nextSizeBound (BitState w)
        (logarithmicBlockLength C n) D (S n)) := by
  unfold RealizedRelation.nextSizeBound
  apply PositivePolynomialBound.mul
  · exact PositivePolynomialBound.constant (D + 5)
  · apply PositivePolynomialBound.add
    · apply PositivePolynomialBound.mul
      · exact bitState_trajectory_polynomial w C
      · apply PositivePolynomialBound.add
        · exact PositivePolynomialBound.mul
            (logarithmicBlockLength_polynomial C)
            (PositivePolynomialBound.add hS
              (PositivePolynomialBound.constant 1))
        · exact PositivePolynomialBound.constant 3
    · exact PositivePolynomialBound.constant 1

/-- Any fixed number of logarithmic blocking rounds preserves a polynomial
gate-count bound. -/
theorem roundsSizeBound_polynomial (w C rounds D : Nat) {S : Nat → Nat}
    (hS : PositivePolynomialBound S) :
    PositivePolynomialBound (fun n =>
      RealizedRelation.roundsSizeBound (BitState w)
        (logarithmicBlockLength C n) rounds D (S n)) := by
  induction rounds generalizing D S with
  | zero => simpa [RealizedRelation.roundsSizeBound] using hS
  | succ rounds ih =>
      rw [show (fun n => RealizedRelation.roundsSizeBound (BitState w)
          (logarithmicBlockLength C n) (rounds + 1) D (S n)) =
        (fun n => RealizedRelation.roundsSizeBound (BitState w)
          (logarithmicBlockLength C n) rounds (D + 5)
          (RealizedRelation.nextSizeBound (BitState w)
            (logarithmicBlockLength C n) D (S n))) by
          funext n
          rfl]
      exact ih (D + 5) (nextSizeBound_polynomial w C D hS)

/-- The common good/bad macroblock relation size bound is polynomial whenever
the simultaneous Hansen entry size is polynomial. -/
theorem macroblockRelationSizeBound_polynomial (w D : Nat) {S : Nat → Nat}
    (hS : PositivePolynomialBound S) :
    PositivePolynomialBound (fun n =>
      PlanarizedFamily.macroblockRelationSizeBound w D (S n)) := by
  unfold PlanarizedFamily.macroblockRelationSizeBound
  apply PositivePolynomialBound.add
  · apply PositivePolynomialBound.mul
    · exact PositivePolynomialBound.constant (D + 3)
    · apply PositivePolynomialBound.add
      · exact PositivePolynomialBound.mul
          (PositivePolynomialBound.constant w)
          (PositivePolynomialBound.add hS
            (PositivePolynomialBound.constant 1))
      · exact PositivePolynomialBound.constant 1
  · exact PositivePolynomialBound.constant (4 * (w + 1))

/-- Numerical bound for the last at-most-one-relation collapse. -/
def finalRoundedRelationSizeBound (w C rounds D K n : Nat) : Nat :=
  RealizedRelation.nextSizeBound (BitState w) 1
    (D + 4 + 5 * rounds)
    (RealizedRelation.roundsSizeBound (BitState w)
      (logarithmicBlockLength C n) rounds (D + 4)
      (PlanarizedFamily.macroblockRelationSizeBound w D ((n + 1) ^ K)))

theorem finalRoundedRelationSizeBound_polynomial (w C rounds D K : Nat) :
    PositivePolynomialBound (finalRoundedRelationSizeBound w C rounds D K) := by
  have hmacro : PositivePolynomialBound
      (fun n => PlanarizedFamily.macroblockRelationSizeBound w D
        ((n + 1) ^ K)) :=
    macroblockRelationSizeBound_polynomial w D
      (PositivePolynomialBound.inputPower K)
  have hrounds : PositivePolynomialBound (fun n =>
      RealizedRelation.roundsSizeBound (BitState w)
        (logarithmicBlockLength C n) rounds (D + 4)
        (PlanarizedFamily.macroblockRelationSizeBound w D ((n + 1) ^ K))) :=
    roundsSizeBound_polynomial w C rounds (D + 4) hmacro
  unfold finalRoundedRelationSizeBound RealizedRelation.nextSizeBound
  apply PositivePolynomialBound.mul
  · exact PositivePolynomialBound.constant (D + 4 + 5 * rounds + 5)
  · apply PositivePolynomialBound.add
    · apply PositivePolynomialBound.mul
      · exact PositivePolynomialBound.constant
          ((Fintype.card (BitState w)) ^ (1 + 1))
      · apply PositivePolynomialBound.add
        · simpa only [one_mul] using
            (PositivePolynomialBound.add hrounds
              (PositivePolynomialBound.constant 1))
        · exact PositivePolynomialBound.constant 3
    · exact PositivePolynomialBound.constant 1

/-- The explicit end-to-end acceptance bound is polynomial. -/
def finalAcceptanceSizeBound (w C rounds D K n : Nat) : Nat :=
  (D + 14 + 5 * rounds) *
    (Fintype.card (BitState w × BitState w) *
      (w + finalRoundedRelationSizeBound w C rounds D K n + 4) + 1)

theorem finalAcceptanceSizeBound_polynomial (w C rounds D K : Nat) :
    PositivePolynomialBound (finalAcceptanceSizeBound w C rounds D K) := by
  unfold finalAcceptanceSizeBound
  apply PositivePolynomialBound.mul
  · exact PositivePolynomialBound.constant (D + 14 + 5 * rounds)
  · apply PositivePolynomialBound.add
    · apply PositivePolynomialBound.mul
      · exact PositivePolynomialBound.constant
          (Fintype.card (BitState w × BitState w))
      · apply PositivePolynomialBound.add
        · apply PositivePolynomialBound.add
          · exact PositivePolynomialBound.constant w
          · exact finalRoundedRelationSizeBound_polynomial w C rounds D K
        · exact PositivePolynomialBound.constant 4
    · exact PositivePolynomialBound.constant 1

end Allender
