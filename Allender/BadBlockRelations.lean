import Allender.ACC0Closure
import Allender.MacroblockCircuit

/-!
# Direct target circuits for singleton (bad) macroblocks

A bad canonical macroblock contains exactly one source transition.  Once its
incoming state is fixed, every source gate is either an input literal or a
Boolean constant.  The constructions below translate those gates directly
to tiny `AC⁰[m]` circuits.
-/

namespace Allender

namespace Gate

/-- Direct target circuit for a source gate with fixed predecessor state. -/
def fixedPreviousCircuit {n w : Nat} (m : Nat) (g : Gate n w)
    (previous : BitState w) : PackedACmCircuit m n :=
  match g with
  | .input i false => PackedACmCircuit.input m n i
  | .input i true => (PackedACmCircuit.input m n i).not
  | .constant value => PackedACmCircuit.constant m n value
  | .copyGate source => PackedACmCircuit.constant m n (previous source)
  | .andGate left right =>
      PackedACmCircuit.constant m n (previous left && previous right)
  | .orGate left right =>
      PackedACmCircuit.constant m n (previous left || previous right)

@[simp] theorem fixedPreviousCircuit_eval {n w : Nat} (m : Nat)
    (g : Gate n w) (previous : BitState w) (x : BitState n) :
    (g.fixedPreviousCircuit m previous).circuit.eval x = g.eval x previous := by
  cases g with
  | input i negated =>
      cases negated with
      | false => simp [fixedPreviousCircuit, Gate.eval]
      | true =>
          change (PackedACmCircuit.input m n i).not.circuit.eval x = !x i
          rw [PackedACmCircuit.not_eval, PackedACmCircuit.input_eval]
  | constant value => simp [fixedPreviousCircuit, Gate.eval]
  | copyGate source => simp [fixedPreviousCircuit, Gate.eval]
  | andGate left right => simp [fixedPreviousCircuit, Gate.eval]
  | orGate left right => simp [fixedPreviousCircuit, Gate.eval]

end Gate

namespace CircuitLayer

/-- Require one output coordinate of a fixed-predecessor layer to match the
given final state. -/
def requiredBitCircuit {n w : Nat} (m : Nat) (layer : CircuitLayer n w)
    (initial final : BitState w) (j : Fin w) : PackedACmCircuit m n :=
  if final j then (layer j).fixedPreviousCircuit m initial
  else ((layer j).fixedPreviousCircuit m initial).not

/-- Complete relation-entry circuit for one source layer. -/
def relationCircuit {n w : Nat} (m : Nat) (layer : CircuitLayer n w)
    (initial final : BitState w) : PackedACmCircuit m n :=
  PackedACmCircuit.conjoin
    (List.ofFn fun j => layer.requiredBitCircuit m initial final j)

theorem relationCircuit_eval_iff {n w : Nat} (m : Nat)
    (layer : CircuitLayer n w) (initial final : BitState w)
    (x : BitState n) :
    (layer.relationCircuit m initial final).circuit.eval x = true ↔
      SegmentRelation [layer] x initial final := by
  rw [segmentRelation_iff_eval]
  simp only [evalLayers, List.foldl_cons, List.foldl_nil]
  rw [relationCircuit, PackedACmCircuit.conjoin_eval_eq_true_iff,
    List.forall_mem_ofFn_iff]
  constructor
  · intro hall
    funext j
    cases hfinal : final j with
    | false =>
        have hj := hall j
        change (if final j = true then (layer j).fixedPreviousCircuit m initial
          else ((layer j).fixedPreviousCircuit m initial).not).circuit.eval x = true at hj
        rw [if_neg (by simp [hfinal])] at hj
        have hvalue : (layer j).eval x initial = false := by
          rw [PackedACmCircuit.not_eval_eq_true_iff] at hj
          simpa using hj
        simpa [CircuitLayer.eval, hfinal] using hvalue.symm
    | true =>
        have hj := hall j
        change (if final j = true then (layer j).fixedPreviousCircuit m initial
          else ((layer j).fixedPreviousCircuit m initial).not).circuit.eval x = true at hj
        rw [if_pos hfinal] at hj
        rw [Gate.fixedPreviousCircuit_eval] at hj
        simpa [CircuitLayer.eval, hfinal] using hj.symm
  · intro heq j
    have hj := congrFun heq j
    cases hfinal : final j with
    | false =>
        change (if final j = true then (layer j).fixedPreviousCircuit m initial
          else ((layer j).fixedPreviousCircuit m initial).not).circuit.eval x = true
        rw [if_neg (by simp [hfinal])]
        rw [PackedACmCircuit.not_eval_eq_true_iff,
          Gate.fixedPreviousCircuit_eval]
        simpa [CircuitLayer.eval, hfinal] using hj.symm
    | true =>
        change (if final j = true then (layer j).fixedPreviousCircuit m initial
          else ((layer j).fixedPreviousCircuit m initial).not).circuit.eval x = true
        rw [if_pos hfinal, Gate.fixedPreviousCircuit_eval]
        simpa [CircuitLayer.eval, hfinal] using hj.symm

end CircuitLayer
end Allender
