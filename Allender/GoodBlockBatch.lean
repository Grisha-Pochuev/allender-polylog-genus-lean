import Allender.FixedBoundaryCircuit
import Allender.SimultaneousHansen

/-!
# The polynomial batch of all good macroblock entries

For every input length this module enumerates every good canonical macroblock,
every incoming width-`w` state, and every output coordinate.  The resulting
ordinary source circuits are precisely the circuits to which simultaneous
Hansen padding is applied.
-/

namespace Allender

namespace Circuit

/-- The actual list of good blocks in the canonical partition. -/
def goodMacroblocks {n w : Nat} (C : Circuit n w) (cuts : Finset Nat) :
    List (List TransitionTag) :=
  (macroblockTags C.layers.tail.length cuts).filter goodMacroblockBool

theorem mem_goodMacroblocks {n w : Nat} {C : Circuit n w}
    {cuts : Finset Nat} {block : List TransitionTag}
    (h : block ∈ C.goodMacroblocks cuts) :
    block ∈ macroblockTags C.layers.tail.length cuts ∧
      GoodMacroblock block := by
  have hfilter := List.mem_filter.mp h
  exact ⟨hfilter.1, (goodMacroblockBool_eq_true block).1 hfilter.2⟩

/-- Every good block is an interval inside the transition sequence, hence has
at most as many tags as the circuit has noninitial layers. -/
theorem goodMacroblock_length_le {n w : Nat} {C : Circuit n w}
    {cuts : Finset Nat} {block : List TransitionTag}
    (h : block ∈ C.goodMacroblocks cuts) :
    block.length ≤ C.layers.tail.length := by
  have hblock := (C.mem_goodMacroblocks h).1
  have hinfix := List.infix_of_mem_flatten hblock
  rw [flatten_macroblockTags] at hinfix
  exact hinfix.length_le.trans_eq (by simp [transitionTags])

/-- A list of nonempty lists has no more blocks than flattened elements. -/
theorem list_length_le_flatten_length_of_nil_not_mem
    {blocks : List (List α)} (hnil : [] ∉ blocks) :
    blocks.length ≤ blocks.flatten.length := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
      have hblock : block ≠ [] := by
        intro h
        apply hnil
        simp [h]
      have hblocks : [] ∉ blocks := by
        intro h
        exact hnil (by simp [h])
      have hpos : 1 ≤ block.length := by
        cases block with
        | nil => exact (hblock rfl).elim
        | cons head tail => simp
      have htail := ih hblocks
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

/-- There are no more good blocks than circuit transitions. -/
theorem goodMacroblocks_length_le {n w : Nat} (C : Circuit n w)
    (cuts : Finset Nat) :
    (C.goodMacroblocks cuts).length ≤ C.layers.tail.length := by
  calc
    (C.goodMacroblocks cuts).length ≤
        (macroblockTags C.layers.tail.length cuts).length :=
      List.length_filter_le _ _
    _ ≤ (macroblockTags C.layers.tail.length cuts).flatten.length :=
      list_length_le_flatten_length_of_nil_not_mem
        (nil_not_mem_macroblockTags _ _)
    _ = C.layers.tail.length := by simp

end Circuit

/-- A circuit family together with one concrete planarizing cut set at every
input length.  The next theorem constructs such data from the genus bound;
this structure only packages the chosen witnesses. -/
structure PlanarizedFamily (F : CircuitFamily) where
  cuts : Nat → Finset Nat
  remainderPlanar : ∀ n, OrientableGenus.IsPlanar
    ((F.circuit n).layeredGraph.deleteLayers (cuts n)).toSimpleGraph

namespace PlanarizedFamily

/-- One enumerated good-block query: block number, incoming state, and output
coordinate. -/
abbrev GoodEntry (P : PlanarizedFamily F) (n : Nat) :=
  Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length ×
    BitState F.width × Fin F.width

/-- There are no batch entries at zero (needed for injective padding); at
positive lengths the count is exactly the finite cardinality of all queries. -/
noncomputable def goodBatchCount (P : PlanarizedFamily F) (n : Nat) : Nat :=
  if n = 0 then 0 else Fintype.card (P.GoodEntry n)

/-- Decode a concrete finite batch index. -/
noncomputable def goodEntryOfIndex (P : PlanarizedFamily F) {n : Nat}
    (t : Fin (P.goodBatchCount n)) : P.GoodEntry n := by
  classical
  by_cases hn : n = 0
  · subst n
    simpa [goodBatchCount] using t.isLt
  · exact (Fintype.equivFin (P.GoodEntry n)).symm
      (Fin.cast (by simp [goodBatchCount, hn]) t)

/-- Encode a concrete good-block query at a positive input length. -/
noncomputable def goodIndexOfEntry (P : PlanarizedFamily F) {n : Nat}
    (hn : 1 ≤ n) (e : P.GoodEntry n) : Fin (P.goodBatchCount n) := by
  classical
  have hnzero : n ≠ 0 := by omega
  have hcount : Fintype.card (P.GoodEntry n) = P.goodBatchCount n := by
    rw [goodBatchCount, if_neg hnzero]
  exact Fin.cast hcount
    (Fintype.equivFin (P.GoodEntry n) e)

@[simp] theorem goodEntryOfIndex_goodIndexOfEntry (P : PlanarizedFamily F)
    {n : Nat} (hn : 1 ≤ n) (e : P.GoodEntry n) :
    P.goodEntryOfIndex (P.goodIndexOfEntry hn e) = e := by
  classical
  unfold goodEntryOfIndex
  split
  · rename_i hzero
    omega
  · unfold goodIndexOfEntry
    simp

/-- The concrete source batch containing every output bit of every good block
at every fixed incoming state. -/
noncomputable def goodCircuitBatch (P : PlanarizedFamily F) :
    CircuitBatch F.width where
  count := P.goodBatchCount
  circuit := fun n t =>
    let e := P.goodEntryOfIndex t
    let block := ((F.circuit n).goodMacroblocks (P.cuts n)).get e.1
    (F.circuit n).fixedBoundaryMacroblockCircuit
      block e.2.1 e.2.2

/-- Decoding an index always selects a genuine good macroblock. -/
theorem decodedBlock_mem (P : PlanarizedFamily F) {n : Nat}
    (t : Fin (P.goodBatchCount n)) :
    ((F.circuit n).goodMacroblocks (P.cuts n)).get
        (P.goodEntryOfIndex t).1 ∈
      (F.circuit n).goodMacroblocks (P.cuts n) :=
  List.get_mem _ _

/-- Every circuit in the enumerated batch is planar. -/
theorem goodCircuitBatch_planar (P : PlanarizedFamily F) :
    P.goodCircuitBatch.Planar := by
  intro n t
  let e := P.goodEntryOfIndex t
  let block := ((F.circuit n).goodMacroblocks (P.cuts n)).get e.1
  have hgoodMem : block ∈ (F.circuit n).goodMacroblocks (P.cuts n) :=
    P.decodedBlock_mem t
  have hdata := (F.circuit n).mem_goodMacroblocks hgoodMem
  simpa [goodCircuitBatch, e, block] using
    (F.circuit n).fixedBoundaryMacroblockCircuit_isPlanar
      (P.cuts n) (P.remainderPlanar n) hdata.1 hdata.2 e.2.1 e.2.2

/-- Elementary fixed-constant absorption used in the batch size/count bounds. -/
theorem self_le_two_pow (c : Nat) : c ≤ 2 ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
      calc
        c + 1 ≤ 2 ^ c + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ c + 2 ^ c := Nat.add_le_add_left (Nat.one_le_pow _ _ (by omega)) _
        _ = 2 ^ (c + 1) := by ring

/-- A fixed additive constant can be absorbed into one larger polynomial
exponent at every positive input length. -/
theorem add_const_le_pow {n a c k : Nat} (hn : 1 ≤ n)
    (ha : a ≤ (n + 1) ^ k) :
    a + c ≤ (n + 1) ^ (k + c + 1) := by
  let A := (n + 1) ^ k
  let K := (n + 1) ^ c
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
  have hK : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
  have hc : c ≤ K := (self_le_two_pow c).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ n + 1) c)
  calc
    a + c ≤ A + K := Nat.add_le_add ha hc
    _ ≤ 2 * (A * K) := by nlinarith
    _ ≤ (n + 1) * (A * K) := Nat.mul_le_mul_right _ (by omega)
    _ = (n + 1) ^ (k + c + 1) := by
      dsimp [A, K]
      ring

/-- Polynomial size of the original family gives a common polynomial size
bound for every enumerated fixed-boundary circuit. -/
theorem goodCircuitBatch_polynomialSize (P : PlanarizedFamily F)
    (hsize : F.PolynomialSize) : P.goodCircuitBatch.PolynomialSize := by
  rcases hsize with ⟨k, hk⟩
  refine ⟨k + F.width + 1, ?_⟩
  intro n t
  have hn : 1 ≤ n := by
    by_contra hpositive
    have hnzero : n = 0 := by omega
    subst n
    have hempty := t.isLt
    simp [goodCircuitBatch, goodBatchCount] at hempty
  let e := P.goodEntryOfIndex t
  let block := ((F.circuit n).goodMacroblocks (P.cuts n)).get e.1
  have hblock : block.length ≤ (F.circuit n).layers.tail.length :=
    (F.circuit n).goodMacroblock_length_le (P.decodedBlock_mem t)
  have hcircuit :
      (P.goodCircuitBatch.circuit n t).size ≤ (F.circuit n).size + F.width := by
    rw [show P.goodCircuitBatch.circuit n t =
        (F.circuit n).fixedBoundaryMacroblockCircuit block e.2.1 e.2.2 by rfl]
    rw [Circuit.fixedBoundaryMacroblockCircuit_size]
    change (block.length + 1) * F.width ≤
      (F.circuit n).size + F.width
    unfold Circuit.size
    have htail : (F.circuit n).layers.tail.length ≤
        (F.circuit n).layers.length := by simp
    calc
      (block.length + 1) * F.width ≤
          ((F.circuit n).layers.tail.length + 1) * F.width :=
        Nat.mul_le_mul_right F.width (Nat.add_le_add_right hblock 1)
      _ ≤ ((F.circuit n).layers.length + 1) * F.width :=
        Nat.mul_le_mul_right F.width (Nat.add_le_add_right htail 1)
      _ = (F.circuit n).layers.length * F.width + F.width := by ring
  exact hcircuit.trans (add_const_le_pow hn (hk n))

/-- The good-block query batch has polynomially many entries.  The constant
factor is exactly the number of boundary-state/output pairs. -/
theorem goodCircuitBatch_polynomialCount (P : PlanarizedFamily F)
    (hw : 0 < F.width) (hsize : F.PolynomialSize) :
    ∃ d : Nat, P.goodCircuitBatch.PolynomialCount d := by
  rcases hsize with ⟨k, hk⟩
  let c := (2 ^ F.width) * F.width
  refine ⟨k + c, ?_, ?_⟩
  · simp [goodCircuitBatch, goodBatchCount]
  · intro n hn
    have hnzero : n ≠ 0 := by omega
    have hblocks :
        ((F.circuit n).goodMacroblocks (P.cuts n)).length ≤
          (F.circuit n).size := by
      have htail := (F.circuit n).goodMacroblocks_length_le (P.cuts n)
      have hlayers : (F.circuit n).layers.tail.length ≤
          (F.circuit n).layers.length := by simp
      have hwidth : (F.circuit n).layers.length ≤
          (F.circuit n).layers.length * F.width := by
        exact Nat.le_mul_of_pos_right _ hw
      exact htail.trans (hlayers.trans hwidth)
    have hc : c ≤ (n + 1) ^ c :=
      (self_le_two_pow c).trans
        (Nat.pow_le_pow_left (by omega : 2 ≤ n + 1) c)
    change P.goodBatchCount n ≤ (n + 1) ^ (k + c)
    have hcard : P.goodBatchCount n =
        ((F.circuit n).goodMacroblocks (P.cuts n)).length * c := by
      simp [goodBatchCount, hnzero, GoodEntry, c, BitState.card,
        Fintype.card_prod]
    rw [hcard]
    calc
      ((F.circuit n).goodMacroblocks (P.cuts n)).length * c ≤
          (F.circuit n).size * c := Nat.mul_le_mul_right c hblocks
      _ ≤ (n + 1) ^ k * (n + 1) ^ c :=
        Nat.mul_le_mul (hk n) hc
      _ = (n + 1) ^ (k + c) := by rw [pow_add]

/-- The complete good-block consequence of the single Hansen application:
all good blocks, boundary states, and output coordinates are simulated by
target circuits with one common modulus, depth bound, and size polynomial. -/
theorem exists_common_modulus_goodCircuitBatch (P : PlanarizedFamily F)
    (hw : 0 < F.width) (hsize : F.PolynomialSize) :
    ∃ m : Nat, 2 ≤ m ∧ ∃ A : P.goodCircuitBatch.ACmBatch m,
      A.ConstantDepth ∧ A.PolynomialSize ∧ A.Simulates := by
  rcases P.goodCircuitBatch_polynomialCount hw hsize with ⟨d, hcount⟩
  exact P.goodCircuitBatch.exists_common_modulus_targetBatch hw hcount
    P.goodCircuitBatch_planar (P.goodCircuitBatch_polynomialSize hsize)

end PlanarizedFamily
end Allender
