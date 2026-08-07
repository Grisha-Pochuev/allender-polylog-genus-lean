import Allender.ACC0Circuit
import Allender.BlockCircuit

/-!
# Concrete Boolean closure operations for `AC⁰[m]` circuits

This module wires target circuits in parallel and adds an unbounded-fan-in
Boolean gate.  The construction is explicit at the gate/layer level; no
closure property of `ACC⁰` is postulated.
-/

namespace Allender

namespace ACCGate

/-- Injectively rename predecessor coordinates. -/
def mapPrevious {m n s S : Nat} (f : Fin s ↪ Fin S) :
    ACCGate m n s → ACCGate m n S
  | .input i => .input i
  | .constant b => .constant b
  | .notGate i => .notGate (f i)
  | .andGate inputs => .andGate (inputs.map f)
  | .orGate inputs => .orGate (inputs.map f)
  | .modGate inputs => .modGate (inputs.map f)

@[simp] theorem mapPrevious_eval {m n s S : Nat} (f : Fin s ↪ Fin S)
    (g : ACCGate m n s) (x : BitState n) (previous : BitState S) :
    (g.mapPrevious f).eval x previous =
      g.eval x (fun i => previous (f i)) := by
  cases g <;>
    simp [mapPrevious, eval, trueCount, Finset.filter_map,
      Function.comp_def]

end ACCGate

namespace ACmLayer

/-- A layer that copies every predecessor coordinate using singleton AND
gates. -/
def copy {m n s : Nat} : ACmLayer m n s :=
  fun i => .andGate {i}

@[simp] theorem copy_eval {m n s : Nat} (x : BitState n)
    (previous : BitState s) : (copy : ACmLayer m n s).eval x previous = previous := by
  funext i
  simp [copy, ACmLayer.eval, ACCGate.eval]

/-- Run two layers in disjoint coordinate intervals. -/
def parallel {m n s t : Nat} (left : ACmLayer m n s)
    (right : ACmLayer m n t) : ACmLayer m n (s + t) :=
  Fin.addCases
    (fun i => (left i).mapPrevious (Fin.castAddEmb t))
    (fun j => (right j).mapPrevious (Fin.natAddEmb s))

@[simp] theorem parallel_eval {m n s t : Nat} (left : ACmLayer m n s)
    (right : ACmLayer m n t) (x : BitState n)
    (p : BitState s) (q : BitState t) :
    (parallel left right).eval x (BitState.append p q) =
      BitState.append (left.eval x p) (right.eval x q) := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [parallel, ACmLayer.eval]
  · intro j
    simp [parallel, ACmLayer.eval]

end ACmLayer

namespace ACmCircuit

/-- Append `r` identity layers. -/
def extendDepth {m n s : Nat} (C : ACmCircuit m n s) (r : Nat) :
    ACmCircuit m n s where
  layers := C.layers ++ List.replicate r ACmLayer.copy
  output := C.output

@[simp] theorem extendDepth_depth {m n s : Nat} (C : ACmCircuit m n s)
    (r : Nat) : (C.extendDepth r).depth = C.depth + r := by
  simp [extendDepth, depth]

private theorem foldl_copy_replicate {m n s : Nat} (r : Nat)
    (x : BitState n) (state : BitState s) :
    (List.replicate r (ACmLayer.copy : ACmLayer m n s)).foldl
      (fun previous layer => layer.eval x previous) state = state := by
  induction r with
  | zero => simp
  | succ r ih => simp [List.replicate_succ, ih]

@[simp] theorem extendDepth_eval {m n s : Nat} (C : ACmCircuit m n s)
    (r : Nat) (x : BitState n) : (C.extendDepth r).eval x = C.eval x := by
  unfold eval finalState extendDepth
  rw [List.foldl_append, foldl_copy_replicate]

@[simp] theorem extendDepth_finalState {m n s : Nat} (C : ACmCircuit m n s)
    (r : Nat) (x : BitState n) :
    (C.extendDepth r).finalState x = C.finalState x := by
  unfold finalState extendDepth
  rw [List.foldl_append, foldl_copy_replicate]

/-- Pad a circuit with identity layers to a requested larger depth. -/
def padDepth {m n s : Nat} (C : ACmCircuit m n s) (D : Nat) :
    ACmCircuit m n s := C.extendDepth (D - C.depth)

@[simp] theorem padDepth_depth {m n s : Nat} (C : ACmCircuit m n s)
    {D : Nat} (h : C.depth ≤ D) : (C.padDepth D).depth = D := by
  simp [padDepth, Nat.add_sub_of_le h]

@[simp] theorem padDepth_eval {m n s : Nat} (C : ACmCircuit m n s)
    (D : Nat) (x : BitState n) : (C.padDepth D).eval x = C.eval x := by
  simp [padDepth]

@[simp] theorem padDepth_finalState {m n s : Nat} (C : ACmCircuit m n s)
    (D : Nat) (x : BitState n) :
    (C.padDepth D).finalState x = C.finalState x := by
  simp [padDepth]

private theorem foldl_parallel {m n s t : Nat}
    (left : List (ACmLayer m n s)) (right : List (ACmLayer m n t))
    (hlength : left.length = right.length) (x : BitState n)
    (p : BitState s) (q : BitState t) :
    (List.zipWith ACmLayer.parallel left right).foldl
        (fun previous layer => layer.eval x previous) (BitState.append p q) =
      BitState.append
        (left.foldl (fun previous layer => layer.eval x previous) p)
        (right.foldl (fun previous layer => layer.eval x previous) q) := by
  induction left generalizing right p q with
  | nil =>
      cases right with
      | nil => simp
      | cons r right => simp at hlength
  | cons l left ih =>
      cases right with
      | nil => simp at hlength
      | cons r right =>
          have hlength' : left.length = right.length := Nat.succ.inj hlength
          simp only [List.zipWith_cons_cons, List.foldl_cons,
            ACmLayer.parallel_eval]
          exact ih right hlength' (l.eval x p) (r.eval x q)

/-- Run two target circuits in parallel at their common maximum depth. -/
def parallelLayers {m n s t : Nat} (C : ACmCircuit m n s)
    (D : ACmCircuit m n t) : List (ACmLayer m n (s + t)) :=
  let depth := max C.depth D.depth
  List.zipWith ACmLayer.parallel
    (C.padDepth depth).layers (D.padDepth depth).layers

theorem parallelLayers_length {m n s t : Nat} (C : ACmCircuit m n s)
    (D : ACmCircuit m n t) :
    (C.parallelLayers D).length = max C.depth D.depth := by
  rw [parallelLayers, List.length_zipWith]
  change min (C.padDepth (max C.depth D.depth)).depth
    (D.padDepth (max C.depth D.depth)).depth = _
  rw [padDepth_depth C (Nat.le_max_left _ _),
    padDepth_depth D (Nat.le_max_right _ _)]
  simp

theorem foldl_parallelLayers {m n s t : Nat} (C : ACmCircuit m n s)
    (D : ACmCircuit m n t) (x : BitState n) :
    (C.parallelLayers D).foldl
        (fun previous layer => layer.eval x previous)
        (BitState.zero (s + t)) =
      BitState.append (C.finalState x) (D.finalState x) := by
  have hzero : BitState.zero (s + t) =
      BitState.append (BitState.zero s) (BitState.zero t) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [BitState.zero]
  rw [hzero]
  unfold parallelLayers
  rw [foldl_parallel]
  · change BitState.append
        ((C.padDepth (max C.depth D.depth)).finalState x)
        ((D.padDepth (max C.depth D.depth)).finalState x) = _
    simp
  · change (C.padDepth (max C.depth D.depth)).depth =
      (D.padDepth (max C.depth D.depth)).depth
    rw [padDepth_depth C (Nat.le_max_left _ _),
      padDepth_depth D (Nat.le_max_right _ _)]

/-- Parallel circuit retaining the left designated output; its full final
state contains both component final states. -/
def parallelCircuit {m n s t : Nat} (C : ACmCircuit m n s)
    (D : ACmCircuit m n t) : ACmCircuit m n (s + t) where
  layers := C.parallelLayers D
  output := Fin.castAdd t C.output

@[simp] theorem parallelCircuit_depth {m n s t : Nat}
    (C : ACmCircuit m n s) (D : ACmCircuit m n t) :
    (C.parallelCircuit D).depth = max C.depth D.depth := by
  exact parallelLayers_length C D

@[simp] theorem parallelCircuit_finalState {m n s t : Nat}
    (C : ACmCircuit m n s) (D : ACmCircuit m n t) (x : BitState n) :
    (C.parallelCircuit D).finalState x =
      BitState.append (C.finalState x) (D.finalState x) := by
  exact C.foldl_parallelLayers D x

/-- Final layer computing the conjunction of the two selected parallel
outputs in the left output coordinate. -/
def parallelAndLayer {m n s t : Nat} (left : Fin s) (right : Fin t) :
    ACmLayer m n (s + t) :=
  fun k => if k = Fin.castAdd t left then
    .andGate {Fin.castAdd t left, Fin.natAdd s right}
  else .constant false

/-- Concrete conjunction of two target circuits. -/
def andCircuit {m n s t : Nat} (C : ACmCircuit m n s)
    (D : ACmCircuit m n t) : ACmCircuit m n (s + t) where
  layers := C.parallelLayers D ++ [parallelAndLayer C.output D.output]
  output := Fin.castAdd t C.output

@[simp] theorem andCircuit_depth {m n s t : Nat} (C : ACmCircuit m n s)
    (D : ACmCircuit m n t) :
    (C.andCircuit D).depth = max C.depth D.depth + 1 := by
  simp [andCircuit, depth, parallelLayers_length]

/-- Exact Boolean semantics of the concrete conjunction wiring. -/
theorem andCircuit_eval_eq_true_iff {m n s t : Nat} (C : ACmCircuit m n s)
    (D : ACmCircuit m n t) (x : BitState n) :
    (C.andCircuit D).eval x = true ↔
      C.eval x = true ∧ D.eval x = true := by
  unfold eval finalState andCircuit
  rw [List.foldl_append, foldl_parallelLayers]
  simp [parallelAndLayer, ACmLayer.eval, ACCGate.eval, BitState.append,
    ACmCircuit.eval, ACmCircuit.finalState]

/-- Final layer negating one selected output. -/
def outputNotLayer {m n s : Nat} (output : Fin s) : ACmLayer m n s :=
  fun k => if k = output then .notGate output else .constant false

/-- Concrete negation of a target circuit. -/
def notCircuit {m n s : Nat} (C : ACmCircuit m n s) : ACmCircuit m n s where
  layers := C.layers ++ [outputNotLayer C.output]
  output := C.output

@[simp] theorem notCircuit_depth {m n s : Nat} (C : ACmCircuit m n s) :
    C.notCircuit.depth = C.depth + 1 := by
  simp [notCircuit, depth]

@[simp] theorem notCircuit_eval {m n s : Nat} (C : ACmCircuit m n s)
    (x : BitState n) : C.notCircuit.eval x = !(C.eval x) := by
  unfold eval finalState notCircuit
  rw [List.foldl_append]
  simp [outputNotLayer, ACmLayer.eval, ACCGate.eval, ACmCircuit.eval,
    ACmCircuit.finalState]

end ACmCircuit

/-- Existentially packaged layer width for finite Boolean combinations of
target circuits. -/
structure PackedACmCircuit (m n : Nat) where
  width : Nat
  circuit : ACmCircuit m n width

namespace PackedACmCircuit

/-- One-layer Boolean constant. -/
def constant (m n : Nat) (value : Bool) : PackedACmCircuit m n where
  width := 1
  circuit :=
    { layers := [fun _ => ACCGate.constant value]
      output := ⟨0, by omega⟩ }

@[simp] theorem constant_eval (m n : Nat) (value : Bool) (x : BitState n) :
    (constant m n value).circuit.eval x = value := by
  simp [constant, ACmCircuit.eval, ACmCircuit.finalState, ACmLayer.eval,
    ACCGate.eval]

/-- Replace a zero-depth packed circuit by the one-layer constant-false
circuit.  A zero-depth circuit starts from the all-zero state, hence always
outputs false.  This normalization prevents an unconstrained padded width
from being hidden by the product definition `size = depth * width`. -/
def normalize (C : PackedACmCircuit m n) : PackedACmCircuit m n :=
  if C.circuit.depth = 0 then constant m n false else C

@[simp] theorem normalize_eval (C : PackedACmCircuit m n)
    (x : BitState n) : C.normalize.circuit.eval x = C.circuit.eval x := by
  by_cases hzero : C.circuit.depth = 0
  · have hnorm : C.normalize = constant m n false := if_pos hzero
    rw [hnorm, constant_eval]
    have hlen : C.circuit.layers.length = 0 := hzero
    have hlayers : C.circuit.layers = [] := by
      exact List.length_eq_zero_iff.mp hlen
    simp [hlayers, ACmCircuit.depth, ACmCircuit.eval,
      ACmCircuit.finalState, BitState.zero]
  · have hnorm : C.normalize = C := if_neg hzero
    rw [hnorm]

/-- Normalization costs at most one layer. -/
theorem normalize_depth_le (C : PackedACmCircuit m n) :
    C.normalize.circuit.depth ≤ C.circuit.depth + 1 := by
  by_cases hzero : C.circuit.depth = 0
  · have hnorm : C.normalize = constant m n false := if_pos hzero
    rw [hnorm]
    simp [constant, ACmCircuit.depth]
  · have hnorm : C.normalize = C := if_neg hzero
    rw [hnorm]
    omega

/-- After normalization, padded width is controlled by the original padded
gate count (plus one for the zero-depth case). -/
theorem normalize_width_le (C : PackedACmCircuit m n) :
    C.normalize.width ≤ C.circuit.size + 1 := by
  by_cases hzero : C.circuit.depth = 0
  · have hnorm : C.normalize = constant m n false := if_pos hzero
    rw [hnorm]
    simp [constant]
  · have hnorm : C.normalize = C := if_neg hzero
    rw [hnorm]
    have hdepth : 1 ≤ C.circuit.depth :=
      Nat.one_le_iff_ne_zero.mpr hzero
    change C.width ≤ C.circuit.depth * C.width + 1
    nlinarith

/-- One-layer positive input literal. -/
def input (m n : Nat) (i : Fin n) : PackedACmCircuit m n where
  width := 1
  circuit :=
    { layers := [fun _ => ACCGate.input i]
      output := ⟨0, by omega⟩ }

@[simp] theorem input_eval (m n : Nat) (i : Fin n) (x : BitState n) :
    (input m n i).circuit.eval x = x i := by
  simp [input, ACmCircuit.eval, ACmCircuit.finalState, ACmLayer.eval,
    ACCGate.eval]

/-- Constant-true packed circuit, used as the empty conjunction. -/
def trueCircuit (m n : Nat) : PackedACmCircuit m n where
  width := 1
  circuit :=
    { layers := [fun _ => ACCGate.constant true]
      output := ⟨0, by omega⟩ }

@[simp] theorem trueCircuit_eval (m n : Nat) (x : BitState n) :
    (trueCircuit m n).circuit.eval x = true := by
  simp [trueCircuit, ACmCircuit.eval, ACmCircuit.finalState, ACmLayer.eval,
    ACCGate.eval]

/-- Packed binary conjunction. -/
def and (C D : PackedACmCircuit m n) : PackedACmCircuit m n where
  width := C.width + D.width
  circuit := C.circuit.andCircuit D.circuit

@[simp] theorem and_eval_eq_true_iff (C D : PackedACmCircuit m n)
    (x : BitState n) :
    (C.and D).circuit.eval x = true ↔
      C.circuit.eval x = true ∧ D.circuit.eval x = true :=
  ACmCircuit.andCircuit_eval_eq_true_iff _ _ _

/-- Packed negation. -/
def not (C : PackedACmCircuit m n) : PackedACmCircuit m n where
  width := C.width
  circuit := C.circuit.notCircuit

@[simp] theorem not_depth (C : PackedACmCircuit m n) :
    C.not.circuit.depth = C.circuit.depth + 1 :=
  ACmCircuit.notCircuit_depth _

@[simp] theorem not_width (C : PackedACmCircuit m n) :
    C.not.width = C.width := rfl

@[simp] theorem not_eval (C : PackedACmCircuit m n) (x : BitState n) :
    C.not.circuit.eval x = !(C.circuit.eval x) := by
  simp [not]

@[simp] theorem not_eval_eq_true_iff (C : PackedACmCircuit m n)
    (x : BitState n) :
    C.not.circuit.eval x = true ↔ C.circuit.eval x = false := by
  simp [not]

theorem not_eval_eq_false_iff (C : PackedACmCircuit m n)
    (x : BitState n) :
    C.not.circuit.eval x = false ↔ C.circuit.eval x = true := by
  rw [not_eval]
  cases C.circuit.eval x <;> simp

/-- Conjoin a finite list by explicit repeated parallel wiring. -/
def conjoin : List (PackedACmCircuit m n) → PackedACmCircuit m n
  | [] => trueCircuit m n
  | C :: circuits => C.and (conjoin circuits)

/-- Exact semantics of the finite conjunction construction. -/
theorem conjoin_eval_eq_true_iff
    (circuits : List (PackedACmCircuit m n)) (x : BitState n) :
    (conjoin circuits).circuit.eval x = true ↔
      ∀ C ∈ circuits, C.circuit.eval x = true := by
  induction circuits with
  | nil => simp [conjoin]
  | cons C circuits ih =>
      simp [conjoin, ih]

/-- One parallel circuit together with every component output coordinate. -/
structure OutputPack (m n : Nat) where
  width : Nat
  circuit : ACmCircuit m n width
  outputs : List (Fin width)

namespace OutputPack

/-- A one-component parallel pack. -/
def singleton (C : PackedACmCircuit m n) : OutputPack m n where
  width := C.width
  circuit := C.circuit
  outputs := [C.circuit.output]

/-- Put two packs in disjoint coordinate intervals. -/
def parallel (P Q : OutputPack m n) : OutputPack m n where
  width := P.width + Q.width
  circuit := P.circuit.parallelCircuit Q.circuit
  outputs := P.outputs.map (Fin.castAdd Q.width) ++
    Q.outputs.map (Fin.natAdd P.width)

@[simp] theorem singleton_depth (C : PackedACmCircuit m n) :
    (singleton C).circuit.depth = C.circuit.depth := rfl

@[simp] theorem parallel_depth (P Q : OutputPack m n) :
    (P.parallel Q).circuit.depth =
      max P.circuit.depth Q.circuit.depth := by
  exact ACmCircuit.parallelCircuit_depth _ _

@[simp] theorem singleton_width (C : PackedACmCircuit m n) :
    (singleton C).width = C.width := rfl

@[simp] theorem parallel_width (P Q : OutputPack m n) :
    (P.parallel Q).width = P.width + Q.width := rfl

/-- All recorded component outputs are true in the final state. -/
def AllTrue (P : OutputPack m n) (x : BitState n) : Prop :=
  ∀ i ∈ P.outputs, P.circuit.finalState x i = true

@[simp] theorem singleton_allTrue_iff (C : PackedACmCircuit m n)
    (x : BitState n) : (singleton C).AllTrue x ↔ C.circuit.eval x = true := by
  unfold AllTrue
  constructor
  · intro h
    apply h C.circuit.output
    change C.circuit.output ∈ [C.circuit.output]
    simp
  · intro h i hi
    change i ∈ [C.circuit.output] at hi
    have hi' : i = C.circuit.output := List.eq_of_mem_singleton hi
    subst i
    exact h

@[simp] theorem parallel_allTrue_iff (P Q : OutputPack m n)
    (x : BitState n) :
    (P.parallel Q).AllTrue x ↔ P.AllTrue x ∧ Q.AllTrue x := by
  unfold AllTrue
  rw [show (P.parallel Q).circuit.finalState x =
      BitState.append (P.circuit.finalState x) (Q.circuit.finalState x) by
    exact ACmCircuit.parallelCircuit_finalState _ _ _]
  constructor
  · intro hall
    constructor
    · intro i hi
      have hmem : Fin.castAdd Q.width i ∈ (P.parallel Q).outputs := by
        change Fin.castAdd Q.width i ∈
          P.outputs.map (Fin.castAdd Q.width) ++
            Q.outputs.map (Fin.natAdd P.width)
        simp [hi]
      have h := hall (Fin.castAdd Q.width i) hmem
      simpa using h
    · intro i hi
      have hmem : Fin.natAdd P.width i ∈ (P.parallel Q).outputs := by
        change Fin.natAdd P.width i ∈
          P.outputs.map (Fin.castAdd Q.width) ++
            Q.outputs.map (Fin.natAdd P.width)
        simp [hi]
      have h := hall (Fin.natAdd P.width i) hmem
      simpa using h
  · rintro ⟨hleft, hright⟩ i hi
    revert hi
    refine Fin.addCases ?_ ?_ i
    · intro j
      intro hi
      have hj : j ∈ P.outputs := by
        change Fin.castAdd Q.width j ∈
          P.outputs.map (Fin.castAdd Q.width) ++
            Q.outputs.map (Fin.natAdd P.width) at hi
        rw [List.mem_append] at hi
        rcases hi with hi | hi
        · rcases List.mem_map.mp hi with ⟨a, ha, hai⟩
          have haeq : a = j := by
            apply Fin.ext
            exact congrArg (fun z : Fin (P.width + Q.width) => z.val) hai
          simpa [haeq] using ha
        · rcases List.mem_map.mp hi with ⟨a, _ha, hai⟩
          have hv := congrArg Fin.val hai
          simp at hv
          omega
      simpa using hleft j hj
    · intro j
      intro hi
      have hj : j ∈ Q.outputs := by
        change Fin.natAdd P.width j ∈
          P.outputs.map (Fin.castAdd Q.width) ++
            Q.outputs.map (Fin.natAdd P.width) at hi
        rw [List.mem_append] at hi
        rcases hi with hi | hi
        · rcases List.mem_map.mp hi with ⟨a, _ha, hai⟩
          have hv := congrArg Fin.val hai
          simp at hv
          omega
        · rcases List.mem_map.mp hi with ⟨a, ha, hai⟩
          have haeq : a = j := by
            apply Fin.ext
            simpa using congrArg Fin.val hai
          simpa [haeq] using ha
      simpa using hright j hj

/-- Parallelize a nonempty list of packed circuits. -/
def ofNonemptyList : PackedACmCircuit m n → List (PackedACmCircuit m n) →
    OutputPack m n
  | first, [] => singleton first
  | first, next :: rest => (singleton first).parallel (ofNonemptyList next rest)

/-- Parallelization preserves a common component depth bound. -/
theorem ofNonemptyList_depth_le (first : PackedACmCircuit m n)
    (rest : List (PackedACmCircuit m n)) (D : Nat)
    (hdepth : ∀ C ∈ first :: rest, C.circuit.depth ≤ D) :
    (ofNonemptyList first rest).circuit.depth ≤ D := by
  induction rest generalizing first with
  | nil => simpa [ofNonemptyList, singleton] using
      hdepth first (by simp)
  | cons next rest ih =>
      rw [ofNonemptyList, parallel_depth]
      apply max_le
      · exact hdepth first (by simp)
      · apply ih next
        intro C hC
        exact hdepth C (by simp [hC])

/-- The packed width is exactly the sum of component widths. -/
theorem ofNonemptyList_width (first : PackedACmCircuit m n)
    (rest : List (PackedACmCircuit m n)) :
    (ofNonemptyList first rest).width =
      ((first :: rest).map PackedACmCircuit.width).sum := by
  induction rest generalizing first with
  | nil => simp [ofNonemptyList]
  | cons next rest ih =>
      simp [ofNonemptyList, ih]

theorem ofNonemptyList_allTrue_iff (first : PackedACmCircuit m n)
    (rest : List (PackedACmCircuit m n)) (x : BitState n) :
    (ofNonemptyList first rest).AllTrue x ↔
      ∀ C ∈ first :: rest, C.circuit.eval x = true := by
  induction rest generalizing first with
  | nil => simp [ofNonemptyList]
  | cons next rest ih =>
      simp [ofNonemptyList, ih]

/-- One unbounded AND layer over every recorded component output. -/
def conjunctionLayer (P : OutputPack m n) : ACmLayer m n P.width :=
  fun k => if k = P.circuit.output then
    .andGate P.outputs.toFinset
  else .constant false

/-- Collapse a parallel pack to one Boolean output with a single layer. -/
def conjunction (P : OutputPack m n) : PackedACmCircuit m n where
  width := P.width
  circuit :=
    { layers := P.circuit.layers ++ [P.conjunctionLayer]
      output := P.circuit.output }

@[simp] theorem conjunction_depth (P : OutputPack m n) :
    P.conjunction.circuit.depth = P.circuit.depth + 1 := by
  simp [conjunction, ACmCircuit.depth]

@[simp] theorem conjunction_width (P : OutputPack m n) :
    P.conjunction.width = P.width := rfl

theorem conjunction_eval_eq_true_iff (P : OutputPack m n) (x : BitState n) :
    P.conjunction.circuit.eval x = true ↔ P.AllTrue x := by
  unfold AllTrue
  unfold conjunction ACmCircuit.eval ACmCircuit.finalState
  rw [List.foldl_append]
  simp [conjunctionLayer, ACmLayer.eval, ACCGate.eval, AllTrue]

end OutputPack

/-- A finite conjunction using true parallel evaluation followed by one
unbounded AND layer.  Its added depth is independent of list length. -/
def conjoinParallel : List (PackedACmCircuit m n) → PackedACmCircuit m n
  | [] => trueCircuit m n
  | first :: rest => (OutputPack.ofNonemptyList first rest).conjunction

theorem conjoinParallel_eval_eq_true_iff
    (circuits : List (PackedACmCircuit m n)) (x : BitState n) :
    (conjoinParallel circuits).circuit.eval x = true ↔
      ∀ C ∈ circuits, C.circuit.eval x = true := by
  cases circuits with
  | nil => simp [conjoinParallel]
  | cons first rest =>
      rw [conjoinParallel, OutputPack.conjunction_eval_eq_true_iff,
        OutputPack.ofNonemptyList_allTrue_iff]

/-- A parallel conjunction adds one layer to the common component bound. -/
theorem conjoinParallel_depth_le
    (circuits : List (PackedACmCircuit m n)) (D : Nat)
    (hdepth : ∀ C ∈ circuits, C.circuit.depth ≤ D) :
    (conjoinParallel circuits).circuit.depth ≤ D + 1 := by
  cases circuits with
  | nil => simp [conjoinParallel, trueCircuit, ACmCircuit.depth]
  | cons first rest =>
      rw [conjoinParallel, OutputPack.conjunction_depth]
      exact Nat.add_le_add_right
        (OutputPack.ofNonemptyList_depth_le first rest D hdepth) 1

/-- The conjunction width is bounded by the sum of component widths, with a
single coordinate used for the empty conjunction. -/
theorem conjoinParallel_width_le
    (circuits : List (PackedACmCircuit m n)) :
    (conjoinParallel circuits).width ≤
      (circuits.map PackedACmCircuit.width).sum + 1 := by
  cases circuits with
  | nil => simp [conjoinParallel, trueCircuit]
  | cons first rest =>
      rw [conjoinParallel, OutputPack.conjunction_width,
        OutputPack.ofNonemptyList_width]
      omega

/-- A finite disjunction obtained from the concrete parallel conjunction by
De Morgan duality.  The construction adds two Boolean layers, independently
of the number of disjuncts. -/
def disjoinParallel (circuits : List (PackedACmCircuit m n)) :
    PackedACmCircuit m n :=
  (conjoinParallel (circuits.map PackedACmCircuit.not)).not

/-- Exact semantics of the parallel finite disjunction. -/
theorem disjoinParallel_eval_eq_true_iff
    (circuits : List (PackedACmCircuit m n)) (x : BitState n) :
    (disjoinParallel circuits).circuit.eval x = true ↔
      ∃ C ∈ circuits, C.circuit.eval x = true := by
  classical
  rw [disjoinParallel, not_eval_eq_true_iff]
  rw [show (conjoinParallel (circuits.map PackedACmCircuit.not)).circuit.eval x = false ↔
      ¬(conjoinParallel (circuits.map PackedACmCircuit.not)).circuit.eval x = true by
    generalize (conjoinParallel
      (circuits.map PackedACmCircuit.not)).circuit.eval x = value
    cases value <;> simp]
  rw [conjoinParallel_eval_eq_true_iff]
  simp
  constructor
  · rintro ⟨C, hC, hfalse⟩
    exact ⟨C, hC, (not_eval_eq_false_iff C x).mp hfalse⟩
  · rintro ⟨C, hC, htrue⟩
    exact ⟨C, hC, (not_eval_eq_false_iff C x).mpr htrue⟩

/-- The De Morgan implementation of parallel disjunction adds at most three
layers, independently of the number of disjuncts. -/
theorem disjoinParallel_depth_le
    (circuits : List (PackedACmCircuit m n)) (D : Nat)
    (hdepth : ∀ C ∈ circuits, C.circuit.depth ≤ D) :
    (disjoinParallel circuits).circuit.depth ≤ D + 3 := by
  rw [disjoinParallel]
  rw [not_depth]
  have hcomponents : ∀ C ∈ circuits.map PackedACmCircuit.not,
      C.circuit.depth ≤ D + 1 := by
    intro C hC
    rcases List.mem_map.mp hC with ⟨source, hsource, rfl⟩
    rw [not_depth]
    exact Nat.add_le_add_right (hdepth source hsource) 1
  exact Nat.add_le_add_right
    (conjoinParallel_depth_le _ (D + 1) hcomponents) 1

/-- Disjunction preserves the same additive width bound as conjunction. -/
theorem disjoinParallel_width_le
    (circuits : List (PackedACmCircuit m n)) :
    (disjoinParallel circuits).width ≤
      (circuits.map PackedACmCircuit.width).sum + 1 := by
  rw [disjoinParallel]
  change (conjoinParallel (circuits.map PackedACmCircuit.not)).width ≤ _
  calc
    _ ≤ (((circuits.map PackedACmCircuit.not).map
          PackedACmCircuit.width).sum + 1) :=
      conjoinParallel_width_le _
    _ = (circuits.map PackedACmCircuit.width).sum + 1 := by
      simp [List.map_map, Function.comp_def]

end PackedACmCircuit

end Allender
