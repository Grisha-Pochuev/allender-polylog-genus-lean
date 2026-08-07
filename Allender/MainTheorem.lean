import Allender.AcceptanceCircuit
import Allender.FamilyPlanarization
import Allender.PolynomialBounds

/-!
# The polylogarithmic-genus reduction

This file assembles the quantitative hypotheses of the Allender problem.  The
first step is the numerical bridge from polynomial source size and
polylogarithmic genus to a constant number of logarithmic blocking rounds.
-/

namespace Allender

namespace CircuitFamily

/-- Every represented source circuit has a genuine output layer.  Ordinary
circuits have an output gate; this excludes only the degenerate empty-list
encoding available in the low-level `Circuit` structure. -/
def NonemptyLayers (F : CircuitFamily) : Prop :=
  ∀ n, (F.circuit n).layers ≠ []

/-- The orientable genus is bounded by a fixed power of the binary logarithm. -/
def PolylogGenus (F : CircuitFamily) : Prop :=
  ∃ A c : Nat, ∀ n,
    OrientableGenus.genus (F.circuit n).layeredGraph.toSimpleGraph ≤
      A * (Nat.log 2 (n + 2) + 1) ^ c

theorem width_pos (F : CircuitFamily) : 0 < F.width :=
  by have := (F.circuit 0).output.isLt; omega

theorem nonemptyVertices_of_nonemptyLayers (F : CircuitFamily)
    (hne : F.NonemptyLayers) : F.NonemptyVertices := by
  intro n
  exact ⟨⟨⟨0, List.length_pos_of_ne_nil (hne n)⟩,
    (F.circuit n).output⟩⟩

end CircuitFamily

/-- A polynomial source-size bound makes its binary logarithm at most a fixed
multiple of `log n`. -/
theorem log_size_add_one_le {F : CircuitFamily} {k n : Nat}
    (hsize : (F.circuit n).size ≤ (n + 1) ^ k) :
    Nat.log 2 (F.circuit n).size + 1 ≤
      (k + 1) * (Nat.log 2 (n + 2) + 1) := by
  let ell := Nat.log 2 (n + 2) + 1
  have hell : 1 ≤ ell := by simp [ell]
  by_cases hk : k = 0
  · subst k
    have hsone : (F.circuit n).size ≤ 1 := by simpa using hsize
    have hlog : Nat.log 2 (F.circuit n).size ≤ 0 := by
      simpa using Nat.log_mono_right (b := 2) hsone
    simp only [Nat.zero_add, Nat.one_mul]
    omega
  · have hbase : n + 1 < 2 ^ ell := by
      have htop := Nat.lt_pow_succ_log_self Nat.one_lt_two (n + 2)
      exact (by omega : n + 1 ≤ n + 2).trans_lt (by simpa [ell] using htop)
    have hp : (n + 1) ^ k < (2 ^ ell) ^ k :=
      Nat.pow_lt_pow_left hbase hk
    have hsource : (F.circuit n).size < 2 ^ (ell * k) := by
      calc
        (F.circuit n).size ≤ (n + 1) ^ k := hsize
        _ < (2 ^ ell) ^ k := hp
        _ = 2 ^ (ell * k) := by rw [pow_mul]
    have hlog : Nat.log 2 (F.circuit n).size < ell * k :=
      Nat.log_lt_of_lt_pow' (Nat.mul_ne_zero (by omega) hk) hsource
    have hfirst : Nat.log 2 (F.circuit n).size + 1 ≤ ell * k := by omega
    calc
      Nat.log 2 (F.circuit n).size + 1 ≤ ell * k := hfirst
      _ ≤ (k + 1) * ell := by
        rw [Nat.mul_comm ell k]
        exact Nat.mul_le_mul_right ell (Nat.le_succ k)

/-- Concrete logarithmic block parameters which absorb the entire canonical
macroblock list. -/
def macroblockCoefficient (A k : Nat) : Nat := 4 * A * (k + 1) + 1

theorem macroblockCoefficient_pos (A k : Nat) :
    0 < macroblockCoefficient A k := by
  unfold macroblockCoefficient
  omega

/-- The canonical macroblock count fits in a constant number `c+1` of
logarithmic blocking rounds. -/
theorem canonical_macroblock_count_le {F : CircuitFamily} {A c k n : Nat}
    (hgenus : F.GenusBound
      (fun j => A * (Nat.log 2 (j + 2) + 1) ^ c))
    (hsize : (F.circuit n).size ≤ (n + 1) ^ k) :
    let P := F.planarizedTotal hgenus
    (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).length ≤
      (logarithmicBlockLength (macroblockCoefficient A k) n) ^ (c + 1) := by
  let ell := Nat.log 2 (n + 2) + 1
  let g : Nat → Nat := fun j => A * (Nat.log 2 (j + 2) + 1) ^ c
  have hgb : F.GenusBound g := by
    simpa only [CircuitFamily.GenusBound, g] using hgenus
  let P := F.planarizedTotal hgb
  have hcuts : (P.cuts n).card ≤
      A * ell ^ c * (Nat.log 2 (F.circuit n).size + 1) := by
    simpa [P, g, ell] using F.planarizedTotal_cuts_card_le hgb n
  have hlog := log_size_add_one_le (F := F) hsize
  have hblocks := macroblockTags_length_le_of_cuts
    (F.circuit n).layers.tail.length (P.cuts n)
  have hell : 1 ≤ ell := by simp [ell]
  have hellpow : 1 ≤ ell ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
  let C := macroblockCoefficient A k
  have hC : 1 ≤ C := by simp [C, macroblockCoefficient]
  have hCpow : C ≤ C ^ (c + 1) := by
    have := Nat.pow_le_pow_right hC (show 1 ≤ c + 1 by omega)
    simpa using this
  calc
    (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).length
        ≤ 4 * (P.cuts n).card + 1 := hblocks
    _ ≤ 4 * (A * ell ^ c * ((k + 1) * ell)) + 1 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 4
        (hcuts.trans (Nat.mul_le_mul_left (A * ell ^ c) hlog))) 1
    _ = (4 * A * (k + 1)) * ell ^ (c + 1) + 1 := by ring
    _ ≤ C * ell ^ (c + 1) := by
      dsimp [C, macroblockCoefficient]
      nlinarith
    _ ≤ C ^ (c + 1) * ell ^ (c + 1) :=
      Nat.mul_le_mul_right (ell ^ (c + 1)) hCpow
    _ = (logarithmicBlockLength C n) ^ (c + 1) := by
      simp [logarithmicBlockLength, C, ell, mul_pow]

namespace PlanarizedFamily

/-- The final target circuit at every input length. Empty-layer source
circuits compute false and are handled directly; length zero is handled by
the unique constant matching its source circuit. -/
noncomputable def finalPackedCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    (C rounds : Nat) (n : Nat) : PackedACmCircuit m n := by
  by_cases hnil : (F.circuit n).layers = []
  · exact PackedACmCircuit.constant m n false
  · by_cases hn : n = 0
    · subst n
      exact PackedACmCircuit.constant m 0
        ((F.circuit 0).eval (BitState.zero 0))
    · exact P.roundedAcceptanceCircuit A hsim
        (Nat.one_le_iff_ne_zero.mpr hn) hnil
        (logarithmicBlockLength C n) rounds

/-- Package the per-length circuits into one fixed-modulus family. -/
noncomputable def finalFamily (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    (C rounds : Nat) : ACmFamily m where
  width := fun n => (P.finalPackedCircuit A hsim C rounds n).width
  circuit := fun n => (P.finalPackedCircuit A hsim C rounds n).circuit

theorem finalPackedCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    (C rounds : Nat) (hC : 0 < C) (n : Nat) (x : BitState n) :
    (P.finalPackedCircuit A hsim C rounds n).circuit.eval x = true ↔
      (F.circuit n).eval x = true := by
  by_cases hnil : (F.circuit n).layers = []
  · rw [finalPackedCircuit]
    dsimp only
    rw [dif_pos hnil]
    simp [Circuit.eval, Circuit.finalState, hnil, BitState.zero]
  · by_cases hn : n = 0
    · subst n
      have hx : x = BitState.zero 0 := by
        funext i
        exact Fin.elim0 i
      subst x
      rw [finalPackedCircuit]
      dsimp only
      rw [dif_neg hnil]
      simp
    · rw [finalPackedCircuit]
      dsimp only
      rw [dif_neg hnil, dif_neg hn]
      exact P.roundedAcceptanceCircuit_eval_iff A hsim
        (Nat.one_le_iff_ne_zero.mpr hn) hnil
        (logarithmicBlockLength C n)
        (logarithmicBlockLength_pos C n hC) rounds x

theorem finalFamily_recognizes (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    (C rounds : Nat) (hC : 0 < C) :
    (P.finalFamily A hsim C rounds).Recognizes F.language := by
  intro n x
  exact P.finalPackedCircuit_eval_iff A hsim C rounds hC n x

theorem finalFamily_constantDepth (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    (C rounds D : Nat) (hC : 0 < C)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D) :
    (P.finalFamily A hsim C rounds).ConstantDepth := by
  refine ⟨D + 14 + 5 * rounds, ?_⟩
  intro n
  change (P.finalPackedCircuit A hsim C rounds n).circuit.depth ≤ _
  by_cases hnil : (F.circuit n).layers = []
  · rw [finalPackedCircuit]
    dsimp only
    rw [dif_pos hnil]
    simp [PackedACmCircuit.constant, ACmCircuit.depth]
    omega
  · by_cases hn : n = 0
    · subst n
      rw [finalPackedCircuit]
      dsimp only
      rw [dif_neg hnil]
      simp [PackedACmCircuit.constant, ACmCircuit.depth]
      omega
    · rw [finalPackedCircuit]
      dsimp only
      rw [dif_neg hnil, dif_neg hn]
      exact P.roundedAcceptanceCircuit_depth_le A hsim
        (Nat.one_le_iff_ne_zero.mpr hn) hnil
        (logarithmicBlockLength C n)
        (logarithmicBlockLength_pos C n hC) rounds D hdepth

theorem finalFamily_polynomialSize (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    (C rounds D K : Nat) (hC : 0 < C)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D)
    (hsize : ∀ n t, (A.circuit n t).size ≤ (n + 1) ^ K)
    (hcount : ∀ n, 1 ≤ n →
      (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).length ≤
        (logarithmicBlockLength C n) ^ rounds) :
    (P.finalFamily A hsim C rounds).PolynomialSize := by
  rcases finalAcceptanceSizeBound_polynomial F.width C rounds D K with
    ⟨q, hq⟩
  refine ⟨q, ?_⟩
  intro n
  change (P.finalPackedCircuit A hsim C rounds n).circuit.size ≤ _
  by_cases hnil : (F.circuit n).layers = []
  · rw [finalPackedCircuit]
    dsimp only
    rw [dif_pos hnil]
    simp [PackedACmCircuit.constant, ACmCircuit.size]
    exact Nat.one_le_pow q (n + 1) (by omega)
  · by_cases hn : n = 0
    · subst n
      rw [finalPackedCircuit]
      dsimp only
      rw [dif_neg hnil]
      simp [PackedACmCircuit.constant, ACmCircuit.size]
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have htarget := P.roundedAcceptanceCircuit_size_le A hsim hnpos
        hnil (logarithmicBlockLength C n)
        (logarithmicBlockLength_pos C n hC) rounds D ((n + 1) ^ K)
        hdepth (hsize n) (hcount n hnpos)
      have hnumeric :
          (P.roundedAcceptanceCircuit A hsim hnpos hnil
            (logarithmicBlockLength C n) rounds).circuit.size ≤
            finalAcceptanceSizeBound F.width C rounds D K n := by
        simpa [finalAcceptanceSizeBound, finalRoundedRelationSizeBound] using
          htarget
      rw [finalPackedCircuit]
      dsimp only
      rw [dif_neg hnil, dif_neg hn]
      exact hnumeric.trans (hq n hnpos)

end PlanarizedFamily

/-- Main reduction theorem in the concrete circuit model: every fixed-width,
polynomial-size family of layered circuits with polylogarithmic
orientable genus is recognized by one fixed-modulus nonuniform `ACC⁰` family.

The theorem depends on the five explicitly audited orientable-genus facts and
the separately stated Hansen simulation theorem; no proof placeholder or
additional reduction hypothesis is used. -/
theorem allender_polylog_genus_in_ACC0 (F : CircuitFamily)
    (hsourceSize : F.PolynomialSize)
    (hsourceGenus : F.PolylogGenus) : InACC0 F.language := by
  rcases hsourceSize with ⟨k, hk⟩
  rcases hsourceGenus with ⟨a, c, hgenus⟩
  let g : Nat → Nat := fun n => a * (Nat.log 2 (n + 2) + 1) ^ c
  have hgb : F.GenusBound g := by
    intro n
    exact hgenus n
  let P := F.planarizedTotal hgb
  have hpoly : F.PolynomialSize := ⟨k, hk⟩
  rcases P.exists_common_modulus_goodCircuitBatch F.width_pos hpoly with
    ⟨m, hm, A, hAdepth, hAsize, hsim⟩
  rcases hAdepth with ⟨D, hD⟩
  rcases hAsize with ⟨K, hK⟩
  let C := macroblockCoefficient a k
  have hC : 0 < C := macroblockCoefficient_pos a k
  have hcount : ∀ n, 1 ≤ n →
      (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).length ≤
        (logarithmicBlockLength C n) ^ (c + 1) := by
    intro n _hn
    simpa [P, C, g] using
      (canonical_macroblock_count_le (F := F) (A := a) (c := c)
        (k := k) (n := n) hgb (hk n))
  refine ⟨m, hm, P.finalFamily A hsim C (c + 1), ?_, ?_, ?_⟩
  · exact P.finalFamily_constantDepth A hsim C (c + 1) D hC hD
  · exact P.finalFamily_polynomialSize A hsim C (c + 1) D K hC
      hD hK hcount
  · exact P.finalFamily_recognizes A hsim C (c + 1) hC

end Allender
