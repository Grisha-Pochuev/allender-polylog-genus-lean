import Allender.Hansen
import Allender.InputPadding
import Allender.Padding

/-!
# One Hansen family for a polynomial batch of planar circuits

Hansen's theorem cannot be applied independently to every macroblock: `ACC⁰`
is a union over moduli, so separate applications need not return one common
modulus.  This module implements the padding argument from Section 6 of the
candidate proof.  A polynomially indexed batch of fixed-width planar circuits
is encoded into one ordinary planar `CircuitFamily`, to which the single named
Hansen theorem can be applied once.
-/

namespace Allender

/-- A finite batch of width-`w` source circuits for every input length. -/
structure CircuitBatch (w : Nat) where
  count : Nat → Nat
  circuit : (n : Nat) → Fin (count n) → Circuit n w

namespace CircuitBatch

/-- Every circuit in the batch is planar. -/
def Planar {w : Nat} (B : CircuitBatch w) : Prop :=
  ∀ n t, OrientableGenus.IsPlanar (B.circuit n t).layeredGraph.toSimpleGraph

/-- One polynomial bounds the size of every circuit in every batch. -/
def PolynomialSize {w : Nat} (B : CircuitBatch w) : Prop :=
  ∃ k : Nat, ∀ n t, (B.circuit n t).size ≤ (n + 1) ^ k

/-- There are polynomially many indexed circuits at each positive input
length.  Length zero has no entries, which removes the unique degenerate
collision in the padding code `n^(d+2)+t`. -/
def PolynomialCount {w : Nat} (B : CircuitBatch w) (d : Nat) : Prop :=
  B.count 0 = 0 ∧ ∀ n, 1 ≤ n → B.count n ≤ (n + 1) ^ d

/-- A decoded entry at padded length `N`, including exactly the range facts
needed for uniqueness of the code. -/
structure EncodedEntry {w : Nat} (B : CircuitBatch w) (d N : Nat) where
  inputLength : Nat
  positive : 1 ≤ inputLength
  index : Fin (B.count inputLength)
  index_lt_power : index.val < (inputLength + 1) ^ d
  encoded : paddedLength d inputLength index.val = N

namespace EncodedEntry

/-- The original input length is at most its padded code. -/
theorem inputLength_le {w : Nat} {B : CircuitBatch w} {d N : Nat}
    (e : EncodedEntry B d N) : e.inputLength ≤ N := by
  calc
    e.inputLength ≤ paddedLength d e.inputLength e.index.val := by
      unfold paddedLength
      apply Nat.le_add_right_of_le
      have hpow : e.inputLength ≤ (e.inputLength + 1) ^ (d + 2) := by
        have hbase : e.inputLength ≤ e.inputLength + 1 := by omega
        exact hbase.trans (Nat.le_pow (a := e.inputLength + 1) (by omega))
      simpa using hpow
    _ = N := e.encoded

/-- The padding code has at most one valid decoded batch entry. -/
theorem unique {w : Nat} {B : CircuitBatch w} {d N : Nat}
    (a b : EncodedEntry B d N) : a = b := by
  have hcode : paddedLength d a.inputLength a.index.val =
      paddedLength d b.inputLength b.index.val :=
    a.encoded.trans b.encoded.symm
  have hpair := paddedLength_injective_on_ranges
    a.positive b.positive a.index_lt_power b.index_lt_power hcode
  cases a with
  | mk an ahn ai ahi aenc =>
      cases b with
      | mk bn bhn bi bhi benc =>
          simp only at hpair
          cases hpair.1
          have hindex : ai = bi := Fin.ext hpair.2
          cases hindex
          rfl

end EncodedEntry

/-- Noncomputably decode a padded length.  Nonuniformity is intentional in the
open problem and in Hansen's theorem. -/
noncomputable def encodedEntry? {w : Nat} (B : CircuitBatch w) (d N : Nat) :
    Option (EncodedEntry B d N) := by
  classical
  exact if h : Nonempty (EncodedEntry B d N) then
    some (Classical.choice h)
  else none

/-- Any valid entry is the unique result of the decoder. -/
theorem encodedEntry?_eq_some {w : Nat} {B : CircuitBatch w} {d N : Nat}
    (e : EncodedEntry B d N) : B.encodedEntry? d N = some e := by
  classical
  unfold encodedEntry?
  split
  · congr 1
    exact EncodedEntry.unique _ _
  · rename_i hnone
    exact (hnone ⟨e⟩).elim

/-- Build the valid entry corresponding to a concrete batch index. -/
def encodedEntryOfIndex {w : Nat} {B : CircuitBatch w} {d n : Nat}
    (hcount : B.PolynomialCount d) (hn : 1 ≤ n)
    (t : Fin (B.count n)) : EncodedEntry B d (paddedLength d n t.val) where
  inputLength := n
  positive := hn
  index := t
  index_lt_power := t.isLt.trans_le (hcount.2 n hn)
  encoded := rfl

/-- Empty-layer source circuit used at padded lengths that encode no batch
entry.  It computes zero and has no dependency-graph vertices. -/
def zeroCircuit (n w : Nat) (hw : 0 < w) : Circuit n w where
  layers := []
  output := ⟨0, hw⟩

@[simp] theorem zeroCircuit_size (n w : Nat) (hw : 0 < w) :
    (zeroCircuit n w hw).size = 0 := by
  simp [zeroCircuit, Circuit.size]

/-- The fallback circuit is planar because its graph is edgeless. -/
theorem zeroCircuit_isPlanar (n w : Nat) (hw : 0 < w) :
    OrientableGenus.IsPlanar
      (zeroCircuit n w hw).layeredGraph.toSimpleGraph := by
  unfold OrientableGenus.IsPlanar
  rw [show (zeroCircuit n w hw).layeredGraph.toSimpleGraph = ⊥ by
    ext u v
    exact Fin.elim0 u.1]
  exact OrientableGenus.genus_bot

/-- The single family obtained by decoding valid padded lengths and using a
zero circuit everywhere else. -/
noncomputable def paddedFamily {w : Nat} (B : CircuitBatch w) (d : Nat)
    (hw : 0 < w) : CircuitFamily where
  width := w
  circuit := fun N =>
    match B.encodedEntry? d N with
    | some e => (B.circuit e.inputLength e.index).padInput e.inputLength_le
    | none => zeroCircuit N w hw

/-- At every valid code, the single family contains exactly the corresponding
batch circuit with unused suffix inputs added. -/
theorem paddedFamily_circuit_at_code {w : Nat} (B : CircuitBatch w) (d : Nat)
    (hw : 0 < w) (hcount : B.PolynomialCount d) {n : Nat} (hn : 1 ≤ n)
    (t : Fin (B.count n)) :
    (B.paddedFamily d hw).circuit (paddedLength d n t.val) =
      (B.circuit n t).padInput
        (encodedEntryOfIndex hcount hn t).inputLength_le := by
  simp only [paddedFamily]
  rw [encodedEntry?_eq_some (encodedEntryOfIndex hcount hn t)]
  rfl

/-- Hence the padded family agrees semantically with the selected batch
circuit on zero-extended inputs. -/
theorem paddedFamily_eval_at_code {w : Nat} (B : CircuitBatch w) (d : Nat)
    (hw : 0 < w) (hcount : B.PolynomialCount d) {n : Nat} (hn : 1 ≤ n)
    (t : Fin (B.count n)) (x : BitState n) :
    ((B.paddedFamily d hw).circuit (paddedLength d n t.val)).eval
        (BitState.zeroExtend
          (encodedEntryOfIndex hcount hn t).inputLength_le x) =
      (B.circuit n t).eval x := by
  rw [paddedFamily_circuit_at_code B d hw hcount hn t]
  exact Circuit.padInput_eval_zeroExtend _ _ _

/-- If every batch circuit is planar, so is the single padded family. -/
theorem paddedFamily_planar {w : Nat} (B : CircuitBatch w) (d : Nat)
    (hw : 0 < w) (hplanar : B.Planar) : (B.paddedFamily d hw).Planar := by
  intro N
  change OrientableGenus.IsPlanar
    (match B.encodedEntry? d N with
      | some e => (B.circuit e.inputLength e.index).padInput e.inputLength_le
      | none => zeroCircuit N w hw).layeredGraph.toSimpleGraph
  cases hdecode : B.encodedEntry? d N with
  | none => exact zeroCircuit_isPlanar N w hw
  | some e =>
      exact Circuit.padInput_isPlanar _ e.inputLength_le
        (hplanar e.inputLength e.index)

/-- A polynomial size bound for the batch remains a polynomial bound in the
padded input length. -/
theorem paddedFamily_polynomialSize {w : Nat} (B : CircuitBatch w) (d : Nat)
    (hw : 0 < w) (hsize : B.PolynomialSize) :
    (B.paddedFamily d hw).PolynomialSize := by
  rcases hsize with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro N
  change (match B.encodedEntry? d N with
    | some e => (B.circuit e.inputLength e.index).padInput e.inputLength_le
    | none => zeroCircuit N w hw).size ≤ (N + 1) ^ k
  cases hdecode : B.encodedEntry? d N with
  | none => simp [zeroCircuit_size]
  | some e =>
      simp only
      rw [Circuit.padInput, Circuit.mapInput_size]
      exact (hk e.inputLength e.index).trans
        (Nat.pow_le_pow_left (Nat.add_le_add_right e.inputLength_le 1) k)

/-- Simultaneous Hansen theorem in the exact form needed by the reduction:
one application to the padded family yields one fixed-modulus `ACC⁰`
simulation for all encoded planar circuits. -/
theorem paddedFamily_inACC0 {w d : Nat} (B : CircuitBatch w) (hw : 0 < w)
    (hplanar : B.Planar) (hsize : B.PolynomialSize) :
    InACC0 (B.paddedFamily d hw).language :=
  Hansen.planar_constantWidth_polySize_to_ACC0
    (B.paddedFamily d hw)
    (B.paddedFamily_planar d hw hplanar)
    (B.paddedFamily_polynomialSize d hw hsize)

/-- A genuine batch of target circuits, all using the same modulus.  The
width may depend on both the input length and the batch index, as is standard
for nonuniform polynomial-size circuits. -/
structure ACmBatch {w : Nat} (B : CircuitBatch w) (m : Nat) where
  width : (n : Nat) → Fin (B.count n) → Nat
  circuit : (n : Nat) → (t : Fin (B.count n)) →
    ACmCircuit m n (width n t)

namespace ACmBatch

/-- One depth bound works simultaneously for every circuit in the batch. -/
def ConstantDepth {w m : Nat} {B : CircuitBatch w} (A : B.ACmBatch m) : Prop :=
  ∃ D : Nat, ∀ n t, (A.circuit n t).depth ≤ D

/-- One polynomial bounds every target circuit in terms of the original,
unpadded input length. -/
def PolynomialSize {w m : Nat} {B : CircuitBatch w} (A : B.ACmBatch m) : Prop :=
  ∃ k : Nat, ∀ n t, (A.circuit n t).size ≤ (n + 1) ^ k

/-- The target batch computes exactly the same Boolean function as the source
batch, not merely the same accepted language after padding. -/
def Simulates {w m : Nat} {B : CircuitBatch w} (A : B.ACmBatch m) : Prop :=
  ∀ n t x, (A.circuit n t).eval x = (B.circuit n t).eval x

end ACmBatch

/-- A batch index cannot exist at input length zero when the padding ranges
obey `PolynomialCount`. -/
theorem inputLength_positive_of_index {w d n : Nat} {B : CircuitBatch w}
    (hcount : B.PolynomialCount d) (t : Fin (B.count n)) : 1 ≤ n := by
  cases n with
  | zero => simpa [hcount.1] using t.isLt
  | succ n => omega

/-- The padded code is polynomially bounded by its original input length.
This is the arithmetic fact needed to transport Hansen's size bound back from
the padded family to the original batch. -/
theorem paddedLength_add_one_le_pow {d n t : Nat} (hn : 1 ≤ n)
    (ht : t < (n + 1) ^ d) :
    paddedLength d n t + 1 ≤ (n + 1) ^ (2 * (d + 3)) := by
  let A := (n + 1) ^ (d + 2)
  have hmain : (n + 1) ^ (d + 2) ≤ A := le_rfl
  have hindex : t + 1 ≤ A := by
    have ht' : t + 1 ≤ (n + 1) ^ d := Nat.succ_le_iff.mpr ht
    have hexponent : (n + 1) ^ d ≤ A :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact ht'.trans hexponent
  calc
    paddedLength d n t + 1 = (n + 1) ^ (d + 2) + (t + 1) := by
      unfold paddedLength
      omega
    _ ≤ A + A := Nat.add_le_add hmain hindex
    _ ≤ (n + 1) * A := by nlinarith
    _ = (n + 1) ^ (d + 3) := by
      dsimp [A]
      ring
    _ ≤ (n + 1) ^ (2 * (d + 3)) :=
      Nat.pow_le_pow_right (by omega) (by omega)

/-- Restrict Hansen's padded target family back to the original batch input
lengths. -/
noncomputable def targetBatch {w d m : Nat} (B : CircuitBatch w)
    (hcount : B.PolynomialCount d) (F : ACmFamily m) : B.ACmBatch m where
  width := fun n t => F.width (paddedLength d n t.val)
  circuit := fun n t =>
    (F.circuit (paddedLength d n t.val)).restrictInput
      (encodedEntryOfIndex hcount (inputLength_positive_of_index hcount t) t).inputLength_le

/-- Restricting the common Hansen family preserves its uniform depth bound. -/
theorem targetBatch_constantDepth {w d m : Nat} (B : CircuitBatch w)
    (hcount : B.PolynomialCount d) (F : ACmFamily m)
    (hdepth : F.ConstantDepth) : (B.targetBatch hcount F).ConstantDepth := by
  rcases hdepth with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro n t
  simpa [targetBatch] using hD (paddedLength d n t.val)

/-- Hansen's polynomial bound at padded length gives one polynomial bound for
all restricted target circuits at their original lengths. -/
theorem targetBatch_polynomialSize {w d m : Nat} (B : CircuitBatch w)
    (hcount : B.PolynomialCount d) (F : ACmFamily m)
    (hsize : F.PolynomialSize) : (B.targetBatch hcount F).PolynomialSize := by
  rcases hsize with ⟨k, hk⟩
  refine ⟨(2 * (d + 3)) * k, ?_⟩
  intro n t
  let N := paddedLength d n t.val
  have hn : 1 ≤ n := inputLength_positive_of_index hcount t
  have ht : t.val < (n + 1) ^ d := t.isLt.trans_le (hcount.2 n hn)
  have hN : N + 1 ≤ (n + 1) ^ (2 * (d + 3)) :=
    paddedLength_add_one_le_pow hn ht
  calc
    ((B.targetBatch hcount F).circuit n t).size =
        (F.circuit N).size := by simp [targetBatch, N]
    _ ≤ (N + 1) ^ k := hk N
    _ ≤ ((n + 1) ^ (2 * (d + 3))) ^ k := Nat.pow_le_pow_left hN k
    _ = (n + 1) ^ ((2 * (d + 3)) * k) := by
      simp only [← pow_mul]

/-- Exact recognition of the padded language yields equality of Boolean
outputs after the unused suffix is fixed to zero. -/
theorem targetBatch_simulates {w d m : Nat} (B : CircuitBatch w) (hw : 0 < w)
    (hcount : B.PolynomialCount d) (F : ACmFamily m)
    (hrecognizes : F.Recognizes (B.paddedFamily d hw).language) :
    (B.targetBatch hcount F).Simulates := by
  intro n t x
  let hn : 1 ≤ n := inputLength_positive_of_index hcount t
  let hle := (encodedEntryOfIndex hcount hn t).inputLength_le
  have hr := hrecognizes (paddedLength d n t.val) (BitState.zeroExtend hle x)
  change ((F.circuit (paddedLength d n t.val)).eval
      (BitState.zeroExtend hle x) = true ↔
    ((B.paddedFamily d hw).circuit (paddedLength d n t.val)).eval
      (BitState.zeroExtend hle x) = true) at hr
  rw [paddedFamily_eval_at_code B d hw hcount hn t x] at hr
  simp only [targetBatch, ACmCircuit.restrictInput_eval]
  rw [Bool.eq_iff_iff]
  exact hr

/-- Fully unpacked simultaneous Hansen consequence: there is one modulus and
one concrete target batch with common depth and polynomial-size bounds that
computes every source circuit exactly. -/
theorem exists_common_modulus_targetBatch {w d : Nat} (B : CircuitBatch w)
    (hw : 0 < w) (hcount : B.PolynomialCount d) (hplanar : B.Planar)
    (hsize : B.PolynomialSize) :
    ∃ m : Nat, 2 ≤ m ∧ ∃ A : B.ACmBatch m,
      A.ConstantDepth ∧ A.PolynomialSize ∧ A.Simulates := by
  rcases B.paddedFamily_inACC0 hw hplanar hsize with
    ⟨m, hm, F, hdepth, hpoly, hrecognizes⟩
  refine ⟨m, hm, B.targetBatch hcount F, ?_, ?_, ?_⟩
  · exact B.targetBatch_constantDepth hcount F hdepth
  · exact B.targetBatch_polynomialSize hcount F hpoly
  · exact B.targetBatch_simulates hw hcount F hrecognizes

end CircuitBatch
end Allender
