import Allender.ACC0Closure
import Allender.GoodBlockBatch

/-!
# Target circuits for complete good-macroblock relation entries

The simultaneous Hansen batch supplies one target circuit for each output bit.
Here those bits are negated when necessary and conjoined, producing the exact
predicate that a fixed incoming boundary state is sent to a fixed outgoing
boundary state.
-/

namespace Allender
namespace PlanarizedFamily

/-- Package the target circuit for one output coordinate of one good block. -/
noncomputable def goodOutputCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial : BitState F.width) (output : Fin F.width) :
    PackedACmCircuit m n := by
  let entry : P.GoodEntry n := (block, initial, output)
  let index := P.goodIndexOfEntry hn entry
  exact ⟨A.width n index, A.circuit n index⟩

/-- The packed output circuit computes exactly the corresponding coordinate
of the concrete macroblock transition. -/
theorem goodOutputCircuit_eval (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial : BitState F.width) (output : Fin F.width) (x : BitState n) :
    (P.goodOutputCircuit A hn block initial output).circuit.eval x =
      evalLayers
        ((F.circuit n).macroblockLayers
          (((F.circuit n).goodMacroblocks (P.cuts n)).get block))
        x initial output := by
  let entry : P.GoodEntry n := (block, initial, output)
  let index := P.goodIndexOfEntry hn entry
  have h := hsim n index x
  change (A.circuit n index).eval x =
    ((F.circuit n).fixedBoundaryMacroblockCircuit
      (((F.circuit n).goodMacroblocks (P.cuts n)).get
        (P.goodEntryOfIndex index).1)
      (P.goodEntryOfIndex index).2.1
      (P.goodEntryOfIndex index).2.2).eval x at h
  rw [show P.goodEntryOfIndex index = entry by
    exact P.goodEntryOfIndex_goodIndexOfEntry hn entry] at h
  rw [Circuit.fixedBoundaryMacroblockCircuit_eval] at h
  change (A.circuit n index).eval x = _
  simpa [goodOutputCircuit, entry, index] using h

/-- Select the positive or negated output-bit circuit according to the desired
outgoing boundary state. -/
noncomputable def goodRequiredBitCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (j : Fin F.width) :
    PackedACmCircuit m n :=
  if final j then P.goodOutputCircuit A hn block initial j
  else (P.goodOutputCircuit A hn block initial j).not

/-- Conjoin all required output coordinates. -/
noncomputable def goodRelationCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) : PackedACmCircuit m n :=
  PackedACmCircuit.conjoin
    (List.ofFn fun j => P.goodRequiredBitCircuit A hn block initial final j)

/-- Exact correctness of the complete relation-entry circuit. -/
theorem goodRelationCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n)
    (block : Fin ((F.circuit n).goodMacroblocks (P.cuts n)).length)
    (initial final : BitState F.width) (x : BitState n) :
    (P.goodRelationCircuit A hn block initial final).circuit.eval x = true ↔
      SegmentRelation
        ((F.circuit n).macroblockLayers
          (((F.circuit n).goodMacroblocks (P.cuts n)).get block))
        x initial final := by
  rw [segmentRelation_iff_eval]
  rw [goodRelationCircuit, PackedACmCircuit.conjoin_eval_eq_true_iff]
  rw [List.forall_mem_ofFn_iff]
  let result := evalLayers
    ((F.circuit n).macroblockLayers
      (((F.circuit n).goodMacroblocks (P.cuts n)).get block)) x initial
  constructor
  · intro hall
    funext j
    cases hfinal : final j with
    | false =>
        have hj :
            (P.goodOutputCircuit A hn block initial j).circuit.eval x = false := by
          have := hall j
          change (if final j = true then
              P.goodOutputCircuit A hn block initial j
            else (P.goodOutputCircuit A hn block initial j).not).circuit.eval x = true at this
          rw [if_neg (by simp [hfinal])] at this
          rw [PackedACmCircuit.not_eval_eq_true_iff] at this
          exact this
        rw [P.goodOutputCircuit_eval A hsim hn block initial j x] at hj
        simpa [result, hfinal] using hj.symm
    | true =>
        have hj :
            (P.goodOutputCircuit A hn block initial j).circuit.eval x = true := by
          have := hall j
          change (if final j = true then
              P.goodOutputCircuit A hn block initial j
            else (P.goodOutputCircuit A hn block initial j).not).circuit.eval x = true at this
          rw [if_pos hfinal] at this
          exact this
        rw [P.goodOutputCircuit_eval A hsim hn block initial j x] at hj
        simpa [result, hfinal] using hj.symm
  · intro heq j
    have hj := congrFun heq j
    cases hfinal : final j with
    | false =>
        have hresult : result j = false := by
          simpa [result, hfinal] using hj.symm
        change (if final j = true then
            P.goodOutputCircuit A hn block initial j
          else (P.goodOutputCircuit A hn block initial j).not).circuit.eval x = true
        rw [if_neg (by simp [hfinal])]
        rw [PackedACmCircuit.not_eval_eq_true_iff]
        rw [P.goodOutputCircuit_eval A hsim hn block initial j x]
        simpa [result] using hresult
    | true =>
        have hresult : result j = true := by
          simpa [result, hfinal] using hj.symm
        change (if final j = true then
            P.goodOutputCircuit A hn block initial j
          else (P.goodOutputCircuit A hn block initial j).not).circuit.eval x = true
        rw [if_pos hfinal]
        rw [P.goodOutputCircuit_eval A hsim hn block initial j x]
        simpa [result] using hresult

end PlanarizedFamily
end Allender
