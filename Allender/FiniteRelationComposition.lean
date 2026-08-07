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

/-- Normalizing all edge circuits raises a common depth bound by at most one. -/
theorem finEdgeCircuits_depth_le {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (states : Fin (k + 1) → α) (D : Nat)
    (hdepth : ∀ i a b, (matrices i a b).circuit.depth ≤ D) :
    ∀ C ∈ finEdgeCircuits matrices states, C.circuit.depth ≤ D + 1 := by
  rw [finEdgeCircuits, List.forall_mem_ofFn_iff]
  intro i
  exact (PackedACmCircuit.normalize_depth_le _).trans
    (Nat.add_le_add_right
      (hdepth i (states i.castSucc) (states i.succ)) 1)

/-- Sum of the normalized edge widths under common depth and width bounds. -/
theorem finEdgeCircuits_width_sum_le {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (states : Fin (k + 1) → α) (D W : Nat)
    (hdepth : ∀ i a b, (matrices i a b).circuit.depth ≤ D)
    (hwidth : ∀ i a b, (matrices i a b).width ≤ W) :
    ((finEdgeCircuits matrices states).map
      PackedACmCircuit.width).sum ≤ k * (D * W + 1) := by
  calc
    ((finEdgeCircuits matrices states).map
        PackedACmCircuit.width).sum ≤
        (D * W + 1) *
          ((finEdgeCircuits matrices states).map
            PackedACmCircuit.width).length :=
      sum_le_mul_length_of_each_le _ (D * W + 1) (by
        intro width hwidthMem
        rw [List.mem_map] at hwidthMem
        rcases hwidthMem with ⟨C, hC, rfl⟩
        rw [finEdgeCircuits, List.mem_ofFn] at hC
        rcases hC with ⟨i, rfl⟩
        calc
          ((matrices i (states i.castSucc)
            (states i.succ)).normalize).width ≤
              (matrices i (states i.castSucc)
                (states i.succ)).circuit.size + 1 :=
            PackedACmCircuit.normalize_width_le _
          _ ≤ D * W + 1 := by
            apply Nat.add_le_add_right
            exact Nat.mul_le_mul
              (hdepth i (states i.castSucc) (states i.succ))
              (hwidth i (states i.castSucc) (states i.succ)))
    _ = k * (D * W + 1) := by
      simp [finEdgeCircuits, Nat.mul_comm]

/-- Variant controlled directly by the genuine padded gate count. -/
theorem finEdgeCircuits_width_sum_le_of_size {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (states : Fin (k + 1) → α) (S : Nat)
    (hsize : ∀ i a b, (matrices i a b).circuit.size ≤ S) :
    ((finEdgeCircuits matrices states).map
      PackedACmCircuit.width).sum ≤ k * (S + 1) := by
  calc
    ((finEdgeCircuits matrices states).map
        PackedACmCircuit.width).sum ≤
        (S + 1) *
          ((finEdgeCircuits matrices states).map
            PackedACmCircuit.width).length :=
      sum_le_mul_length_of_each_le _ (S + 1) (by
        intro width hwidthMem
        rw [List.mem_map] at hwidthMem
        rcases hwidthMem with ⟨C, hC, rfl⟩
        rw [finEdgeCircuits, List.mem_ofFn] at hC
        rcases hC with ⟨i, rfl⟩
        exact (PackedACmCircuit.normalize_width_le _).trans
          (Nat.add_le_add_right
            (hsize i (states i.castSucc) (states i.succ)) 1))
    _ = k * (S + 1) := by simp [finEdgeCircuits, Nat.mul_comm]

/-- A trajectory checker has constant additive depth overhead, independent
of the number of edges in the trajectory. -/
theorem finPathCircuit_depth_le [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (states : Fin (k + 1) → α) (D : Nat)
    (hdepth : ∀ i a b, (matrices i a b).circuit.depth ≤ D) :
    (finPathCircuit matrices initial final states).circuit.depth ≤ D + 2 := by
  apply PackedACmCircuit.conjoinParallel_depth_le _ (D + 1)
  intro C hC
  rcases List.mem_append.mp hC with hendpoint | hedge
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hendpoint
    rcases hendpoint with hendpoint | hendpoint
    · subst C
      simp [PackedACmCircuit.constant, ACmCircuit.depth]
    · subst C
      simp [PackedACmCircuit.constant, ACmCircuit.depth]
  · exact finEdgeCircuits_depth_le matrices states D hdepth C hedge

/-- Explicit width bound for one trajectory checker. -/
theorem finPathCircuit_width_le [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (states : Fin (k + 1) → α) (D W : Nat)
    (hdepth : ∀ i a b, (matrices i a b).circuit.depth ≤ D)
    (hwidth : ∀ i a b, (matrices i a b).width ≤ W) :
    (finPathCircuit matrices initial final states).width ≤
      k * (D * W + 1) + 3 := by
  let edges := finEdgeCircuits matrices states
  calc
    (finPathCircuit matrices initial final states).width ≤
        (([PackedACmCircuit.constant m n
              (decide (states (firstIndex k) = initial)),
            PackedACmCircuit.constant m n
              (decide (states (Fin.last k) = final))] ++ edges).map
          PackedACmCircuit.width).sum + 1 := by
      exact PackedACmCircuit.conjoinParallel_width_le _
    _ = ((edges.map PackedACmCircuit.width).sum + 3) := by
      simp [edges, PackedACmCircuit.constant] <;> omega
    _ ≤ k * (D * W + 1) + 3 := Nat.add_le_add_right
      (finEdgeCircuits_width_sum_le matrices states D W hdepth hwidth) 3

/-- Trajectory-checker width controlled directly by entry gate counts. -/
theorem finPathCircuit_width_le_of_size [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (states : Fin (k + 1) → α) (S : Nat)
    (hsize : ∀ i a b, (matrices i a b).circuit.size ≤ S) :
    (finPathCircuit matrices initial final states).width ≤
      k * (S + 1) + 3 := by
  let edges := finEdgeCircuits matrices states
  calc
    (finPathCircuit matrices initial final states).width ≤
        (([PackedACmCircuit.constant m n
              (decide (states (firstIndex k) = initial)),
            PackedACmCircuit.constant m n
              (decide (states (Fin.last k) = final))] ++ edges).map
          PackedACmCircuit.width).sum + 1 :=
      PackedACmCircuit.conjoinParallel_width_le _
    _ = (edges.map PackedACmCircuit.width).sum + 3 := by
      simp [edges, PackedACmCircuit.constant] <;> omega
    _ ≤ k * (S + 1) + 3 := Nat.add_le_add_right
      (finEdgeCircuits_width_sum_le_of_size matrices states S hsize) 3

/-- Indexed form of the composition circuit.  The common length is carried
by the type, so circuit matrices and semantic relations cannot be misaligned. -/
noncomputable def composeFinCircuit [Fintype α] [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) : PackedACmCircuit m n :=
  PackedACmCircuit.disjoinParallel
    ((Finset.univ : Finset (Fin (k + 1) → α)).toList.map
      (finPathCircuit matrices initial final))

/-- Finite-state trajectory expansion adds at most five layers, independently
of the block length and of the number of trajectories. -/
theorem composeFinCircuit_depth_le [Fintype α] [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (D : Nat)
    (hdepth : ∀ i a b, (matrices i a b).circuit.depth ≤ D) :
    (composeFinCircuit matrices initial final).circuit.depth ≤ D + 5 := by
  apply PackedACmCircuit.disjoinParallel_depth_le _ (D + 2)
  intro C hC
  rw [List.mem_map] at hC
  rcases hC with ⟨states, _hstates, rfl⟩
  exact finPathCircuit_depth_le matrices initial final states D hdepth

/-- Explicit finite-state composition width bound.  Its only dependence on
the group length is through the number of trajectories and the number of
normalized edge circuits. -/
theorem composeFinCircuit_width_le [Fintype α] [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (D W : Nat)
    (hdepth : ∀ i a b, (matrices i a b).circuit.depth ≤ D)
    (hwidth : ∀ i a b, (matrices i a b).width ≤ W) :
    (composeFinCircuit matrices initial final).width ≤
      (Fintype.card α) ^ (k + 1) * (k * (D * W + 1) + 3) + 1 := by
  let paths :=
    ((Finset.univ : Finset (Fin (k + 1) → α)).toList.map
      (finPathCircuit matrices initial final))
  let pathWidth := k * (D * W + 1) + 3
  calc
    (composeFinCircuit matrices initial final).width ≤
        (paths.map PackedACmCircuit.width).sum + 1 := by
      exact PackedACmCircuit.disjoinParallel_width_le _
    _ = (Finset.univ : Finset (Fin (k + 1) → α)).sum
          (fun states =>
            (finPathCircuit matrices initial final states).width) + 1 := by
      simp [paths]
    _ ≤ (Finset.univ : Finset (Fin (k + 1) → α)).sum
          (fun _ => pathWidth) + 1 := by
      apply Nat.add_le_add_right
      apply Finset.sum_le_sum
      intro states _hstates
      exact finPathCircuit_width_le matrices initial final states
        D W hdepth hwidth
    _ = (Fintype.card α) ^ (k + 1) * pathWidth + 1 := by
      simp [Fintype.card_fun, pathWidth]

/-- Composition width controlled directly by entry gate counts. -/
theorem composeFinCircuit_width_le_of_size
    [Fintype α] [DecidableEq α] {k : Nat}
    (matrices : Fin k → PackedRelationCircuit m n α)
    (initial final : α) (S : Nat)
    (hsize : ∀ i a b, (matrices i a b).circuit.size ≤ S) :
    (composeFinCircuit matrices initial final).width ≤
      (Fintype.card α) ^ (k + 1) * (k * (S + 1) + 3) + 1 := by
  let paths :=
    ((Finset.univ : Finset (Fin (k + 1) → α)).toList.map
      (finPathCircuit matrices initial final))
  let pathWidth := k * (S + 1) + 3
  calc
    (composeFinCircuit matrices initial final).width ≤
        (paths.map PackedACmCircuit.width).sum + 1 :=
      PackedACmCircuit.disjoinParallel_width_le _
    _ = (Finset.univ : Finset (Fin (k + 1) → α)).sum
          (fun states =>
            (finPathCircuit matrices initial final states).width) + 1 := by
      simp [paths]
    _ ≤ (Finset.univ : Finset (Fin (k + 1) → α)).sum
          (fun _ => pathWidth) + 1 := by
      apply Nat.add_le_add_right
      apply Finset.sum_le_sum
      intro states _hstates
      exact finPathCircuit_width_le_of_size matrices initial final states
        S hsize
    _ = (Fintype.card α) ^ (k + 1) * pathWidth + 1 := by
      simp [pathWidth]

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
