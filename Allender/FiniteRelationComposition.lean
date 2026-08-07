import Allender.ACC0Closure
import Allender.RelationChain

/-!
# Constant-depth composition of finite-state relation circuits

For a fixed finite state space, sequential relation composition can be
expanded into a disjunction over all boundary-state trajectories.  Each
trajectory is checked by one parallel unbounded conjunction, and all
trajectories are combined by one parallel unbounded disjunction.  This file
implements that expansion as concrete `AC⁰[m]` wiring.
-/

namespace Allender

/-- A matrix of target circuits, one for every entry of a binary relation. -/
abbrev PackedRelationCircuit (m n : Nat) (α : Type*) :=
  α → α → PackedACmCircuit m n

namespace PackedRelationCircuit

/-- Entrywise semantic correctness of a relation-circuit matrix. -/
def Realizes (M : PackedRelationCircuit m n α) (R : Rel α)
    (x : BitState n) : Prop :=
  ∀ a b, (M a b).circuit.eval x = true ↔ R a b

/-- First boundary index of a path with `length` edges. -/
def firstIndex (length : Nat) : Fin (length + 1) :=
  ⟨0, Nat.zero_lt_succ length⟩

/-- A `Fin`-indexed sequence of boundary states is exactly the inductive
relational chain used by the semantic development. -/
theorem exists_fin_path_iff_chain (relations : List (Rel α))
    (initial final : α) :
    (∃ states : Fin (relations.length + 1) → α,
      states (firstIndex relations.length) = initial ∧
      states (Fin.last relations.length) = final ∧
      ∀ i : Fin relations.length,
        relations.get i (states i.castSucc) (states i.succ)) ↔
      Rel.Chain initial relations final := by
  induction relations generalizing initial final with
  | nil =>
      constructor
      · rintro ⟨states, hfirst, hlast, _⟩
        have h : initial = final := by
          calc
            initial = states (firstIndex 0) := hfirst.symm
            _ = states (Fin.last 0) := by
              congr 1
            _ = final := hlast
        simpa [h] using Rel.Chain.nil initial
      · intro h
        cases h
        refine ⟨fun _ => initial, rfl, rfl, ?_⟩
        intro i
        exact Fin.elim0 i
  | cons R relations ih =>
      constructor
      · rintro ⟨states, hfirst, hlast, hedges⟩
        let middle := states ⟨1, by simp⟩
        have hhead : R initial middle := by
          have h := hedges ⟨0, by simp⟩
          have hzero : states ⟨0, by simp⟩ = initial := by
            simpa [firstIndex] using hfirst
          rw [← hzero]
          simpa [middle] using h
        have htail : Rel.Chain middle relations final := by
          rw [← ih]
          refine ⟨fun i => states i.succ, ?_, ?_, ?_⟩
          · simpa [firstIndex, middle]
          · simpa using hlast
          · intro i
            have h := hedges i.succ
            simpa using h
        exact Rel.Chain.cons hhead htail
      · intro hchain
        cases hchain with
        | cons hhead htail =>
            rw [← ih] at htail
            rcases htail with ⟨tailStates, htailFirst, htailLast, htailEdges⟩
            let states : Fin (relations.length + 2) → α :=
              Fin.cases initial tailStates
            refine ⟨states, ?_, ?_, ?_⟩
            · rfl
            · have hlastIndex :
                  Fin.last (relations.length + 1) =
                    (Fin.last relations.length).succ := by
                apply Fin.ext
                rfl
              change states (Fin.last (relations.length + 1)) = final
              rw [hlastIndex]
              change tailStates (Fin.last relations.length) = final
              exact htailLast
            · intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · change R initial (tailStates (firstIndex relations.length))
                rw [htailFirst]
                exact hhead
              · simpa [states] using htailEdges j

/-- Circuits checking all consecutive entries along one proposed path. -/
def edgeCircuits (matrices : List (PackedRelationCircuit m n α))
    (states : Fin (matrices.length + 1) → α) :
    List (PackedACmCircuit m n) :=
  List.ofFn fun i : Fin matrices.length =>
    matrices.get i (states i.castSucc) (states i.succ)

/-- Check endpoints and every edge of one proposed state trajectory. -/
def pathCircuit [DecidableEq α]
    (matrices : List (PackedRelationCircuit m n α))
    (initial final : α) (states : Fin (matrices.length + 1) → α) :
    PackedACmCircuit m n :=
  PackedACmCircuit.conjoinParallel
    ([PackedACmCircuit.constant m n
        (decide (states (firstIndex matrices.length) = initial)),
      PackedACmCircuit.constant m n
        (decide (states (Fin.last matrices.length) = final))] ++
      edgeCircuits matrices states)

/-- Exact semantics of one path checker. -/
theorem pathCircuit_eval_iff [DecidableEq α]
    (matrices : List (PackedRelationCircuit m n α))
    (initial final : α) (states : Fin (matrices.length + 1) → α)
    (x : BitState n) :
    (pathCircuit matrices initial final states).circuit.eval x = true ↔
      states (firstIndex matrices.length) = initial ∧
      states (Fin.last matrices.length) = final ∧
      ∀ i : Fin matrices.length,
        (matrices.get i (states i.castSucc)
          (states i.succ)).circuit.eval x = true := by
  rw [pathCircuit, PackedACmCircuit.conjoinParallel_eval_eq_true_iff]
  simp [edgeCircuits]

/-- Explicit finite disjunction over every state trajectory. -/
noncomputable def composeCircuit [Fintype α] [DecidableEq α]
    (matrices : List (PackedRelationCircuit m n α))
    (initial final : α) : PackedACmCircuit m n :=
  PackedACmCircuit.disjoinParallel
    ((Finset.univ : Finset (Fin (matrices.length + 1) → α)).toList.map
      (pathCircuit matrices initial final))

/-- The concrete composed circuit accepts exactly when a complete trajectory
with the requested endpoints exists. -/
theorem composeCircuit_eval_iff [Fintype α] [DecidableEq α]
    (matrices : List (PackedRelationCircuit m n α))
    (initial final : α) (x : BitState n) :
    (composeCircuit matrices initial final).circuit.eval x = true ↔
      ∃ states : Fin (matrices.length + 1) → α,
        states (firstIndex matrices.length) = initial ∧
        states (Fin.last matrices.length) = final ∧
        ∀ i : Fin matrices.length,
          (matrices.get i (states i.castSucc)
            (states i.succ)).circuit.eval x = true := by
  classical
  rw [composeCircuit, PackedACmCircuit.disjoinParallel_eval_eq_true_iff]
  simp [pathCircuit_eval_iff]

/-- `Fin`-indexed path semantics for a fixed number of relations. -/
def FinPath {k : Nat} (relations : Fin k → Rel α)
    (initial final : α) : Prop :=
  ∃ states : Fin (k + 1) → α,
    states (firstIndex k) = initial ∧
    states (Fin.last k) = final ∧
    ∀ i, relations i (states i.castSucc) (states i.succ)

/-- The indexed path semantics is exactly the ordinary list-based chain. -/
theorem finPath_iff_chain_ofFn {k : Nat} (relations : Fin k → Rel α)
    (initial final : α) :
    FinPath relations initial final ↔
      Rel.Chain initial (List.ofFn relations) final := by
  induction k generalizing initial final with
  | zero =>
      rw [List.ofFn_zero]
      constructor
      · rintro ⟨states, hfirst, hlast, _⟩
        have h : initial = final := by
          calc
            initial = states (firstIndex 0) := hfirst.symm
            _ = states (Fin.last 0) := by congr 1
            _ = final := hlast
        simpa [h] using Rel.Chain.nil initial
      · intro h
        cases h
        exact ⟨fun _ => initial, rfl, rfl, fun i => Fin.elim0 i⟩
  | succ k ih =>
      rw [List.ofFn_succ]
      constructor
      · rintro ⟨states, hfirst, hlast, hedges⟩
        let middle := states ⟨1, by simp⟩
        have hzero : states ⟨0, by simp⟩ = initial := by
          simpa [firstIndex] using hfirst
        have hhead : relations ⟨0, by simp⟩ initial middle := by
          rw [← hzero]
          simpa [middle] using hedges ⟨0, by simp⟩
        have htail : Rel.Chain middle
            (List.ofFn fun i : Fin k => relations i.succ) final := by
          rw [← ih]
          exact ⟨fun i => states i.succ,
            by simpa [firstIndex, middle],
            by simpa using hlast,
            fun i => by simpa using hedges i.succ⟩
        exact Rel.Chain.cons hhead htail
      · intro hchain
        cases hchain with
        | cons hhead htail =>
            rw [← ih] at htail
            rcases htail with
              ⟨tailStates, htailFirst, htailLast, htailEdges⟩
            let states : Fin (k + 2) → α := Fin.cases initial tailStates
            refine ⟨states, rfl, ?_, ?_⟩
            · have hlastIndex : Fin.last (k + 1) = (Fin.last k).succ := by
                apply Fin.ext
                rfl
              rw [hlastIndex]
              change tailStates (Fin.last k) = final
              exact htailLast
            · intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · change relations ⟨0, by simp⟩ initial
                  (tailStates (firstIndex k))
                rw [htailFirst]
                exact hhead
              · simpa [states] using htailEdges j

/-- Circuits checking all edges of one indexed trajectory. -/
def finEdgeCircuits {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (states : Fin (k + 1) → α) : List (PackedACmCircuit m n) :=
  List.ofFn fun i =>
    (matrices i (states i.castSucc) (states i.succ)).normalize

/-- Concrete checker for one indexed trajectory and its endpoints. -/
def finPathCircuit [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (states : Fin (k + 1) → α) :
    PackedACmCircuit m n :=
  PackedACmCircuit.conjoinParallel
    ([PackedACmCircuit.constant m n
        (decide (states (firstIndex k) = initial)),
      PackedACmCircuit.constant m n
        (decide (states (Fin.last k) = final))] ++
      finEdgeCircuits matrices states)

theorem finPathCircuit_eval_iff [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (states : Fin (k + 1) → α)
    (x : BitState n) :
    (finPathCircuit matrices initial final states).circuit.eval x = true ↔
      states (firstIndex k) = initial ∧
      states (Fin.last k) = final ∧
      ∀ i, (matrices i (states i.castSucc)
        (states i.succ)).circuit.eval x = true := by
  rw [finPathCircuit,
    PackedACmCircuit.conjoinParallel_eval_eq_true_iff]
  simp [finEdgeCircuits]

/-- Indexed form of the composition circuit.  The common length is carried
by the type, so circuit matrices and semantic relations cannot be misaligned. -/
noncomputable def composeFinCircuit [Fintype α] [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) : PackedACmCircuit m n :=
  PackedACmCircuit.disjoinParallel
    ((Finset.univ : Finset (Fin (k + 1) → α)).toList.map
      (finPathCircuit matrices initial final))

theorem composeFinCircuit_eval_iff [Fintype α] [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (x : BitState n) :
    (composeFinCircuit matrices initial final).circuit.eval x = true ↔
      ∃ states : Fin (k + 1) → α,
        states (firstIndex k) = initial ∧
        states (Fin.last k) = final ∧
        ∀ i, (matrices i (states i.castSucc)
          (states i.succ)).circuit.eval x = true := by
  classical
  rw [composeFinCircuit,
    PackedACmCircuit.disjoinParallel_eval_eq_true_iff]
  simp [finPathCircuit_eval_iff]

/-- If every indexed matrix realizes its indexed relation, the concrete
trajectory expansion realizes their ordinary sequential composition. -/
theorem composeFinCircuit_eval_iff_composeList
    [Fintype α] [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (relations : Fin k → Rel α)
    (hrealizes : ∀ i, Realizes (matrices i) (relations i) x)
    (initial final : α) :
    (composeFinCircuit matrices initial final).circuit.eval x = true ↔
      Rel.composeList (List.ofFn relations) initial final := by
  rw [composeFinCircuit_eval_iff]
  rw [← Rel.chain_iff_composeList, ← finPath_iff_chain_ofFn]
  constructor
  · rintro ⟨states, hfirst, hlast, hedges⟩
    exact ⟨states, hfirst, hlast, fun i =>
      (hrealizes i (states i.castSucc) (states i.succ)).mp (hedges i)⟩
  · rintro ⟨states, hfirst, hlast, hedges⟩
    exact ⟨states, hfirst, hlast, fun i =>
      (hrealizes i (states i.castSucc) (states i.succ)).mpr (hedges i)⟩

end PackedRelationCircuit
end Allender
