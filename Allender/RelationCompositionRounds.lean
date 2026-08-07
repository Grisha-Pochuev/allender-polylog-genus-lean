import Allender.FiniteRelationComposition

/-!
# Semantics-preserving rounds of finite relation composition

Relations are bundled with the concrete target circuit for each matrix entry.
A round partitions an ordered list into consecutive nonempty groups and
replaces each group by its explicitly composed relation circuit.  The proofs
below show that every round preserves the exact ordered composite.
-/

namespace Allender

/-- A relation-valued function of the input together with a concrete target
circuit matrix realizing every entry. -/
structure RealizedRelation (m n : Nat) (α : Type*) where
  matrix : PackedRelationCircuit m n α
  relation : BitState n → Rel α
  realizes : ∀ x, matrix.Realizes (relation x) x

namespace RealizedRelation

/-- Uniform target-depth bound for every matrix entry of a realized relation. -/
def DepthAtMost (D : Nat) (entry : RealizedRelation m n α) : Prop :=
  ∀ initial final, (entry.matrix initial final).circuit.depth ≤ D

/-- Uniform padded gate-count bound for every matrix entry. -/
def SizeAtMost (S : Nat) (entry : RealizedRelation m n α) : Prop :=
  ∀ initial final, (entry.matrix initial final).circuit.size ≤ S

/-- Fuelled consecutive grouping, used to keep the executable definition
structurally recursive.  The public `groups` supplies sufficient fuel. -/
def groupsAux (L : Nat) : Nat → List β → List (List β)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, items@(_ :: _) =>
      items.take L :: groupsAux L fuel (items.drop L)

/-- Sufficient fuel makes grouping lossless whenever the group size is
positive. -/
theorem flatten_groupsAux (L : Nat) (hL : 0 < L) (fuel : Nat)
    (items : List β) (hlen : items.length ≤ fuel) :
    (groupsAux L fuel items).flatten = items := by
  induction fuel generalizing items with
  | zero =>
      have : items = [] := by simpa using hlen
      simp [this, groupsAux]
  | succ fuel ih =>
      cases items with
      | nil => simp [groupsAux]
      | cons item items =>
          let whole := item :: items
          have hdrop : (whole.drop L).length ≤ fuel := by
            rw [List.length_drop]
            dsimp [whole] at hlen ⊢
            omega
          rw [groupsAux]
          simp only [List.flatten_cons]
          rw [ih (whole.drop L) hdrop]
          exact List.take_append_drop L whole

/-- Partition a list into consecutive groups of at most `L` elements. -/
def groups (L : Nat) (items : List β) : List (List β) :=
  groupsAux L items.length items

/-- No relation is omitted, duplicated, or permuted by grouping. -/
theorem flatten_groups (L : Nat) (hL : 0 < L) (items : List β) :
    (groups L items).flatten = items := by
  exact flatten_groupsAux L hL items.length items le_rfl

/-- If `q` groups of capacity `L` can hold the input, the fuelled grouping
produces at most `q` groups.  The result does not rely on division or an
asymptotic approximation. -/
theorem groupsAux_length_le_of_length_le_mul (L : Nat) (hL : 0 < L)
    (q fuel : Nat) (items : List β) (hlen : items.length ≤ q * L) :
    (groupsAux L fuel items).length ≤ q := by
  induction q generalizing fuel items with
  | zero =>
      have : items = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      subst items
      cases fuel <;> rfl
  | succ q ih =>
      cases fuel with
      | zero => simp [groupsAux]
      | succ fuel =>
          cases items with
          | nil => simp [groupsAux]
          | cons item items =>
              rw [groupsAux]
              simp only [List.length_cons]
              apply Nat.succ_le_succ
              apply ih
              rw [List.length_drop]
              rw [Nat.succ_mul] at hlen
              omega

/-- Capacity bound for the public consecutive grouping. -/
theorem groups_length_le_of_length_le_mul (L : Nat) (hL : 0 < L)
    (q : Nat) (items : List β) (hlen : items.length ≤ q * L) :
    (groups L items).length ≤ q := by
  exact groupsAux_length_le_of_length_le_mul L hL q items.length items hlen

/-- Every produced group has at most the requested capacity. -/
theorem mem_groupsAux_length_le (L fuel : Nat) (items : List β)
    {block : List β} (hblock : block ∈ groupsAux L fuel items) :
    block.length ≤ L := by
  induction fuel generalizing items with
  | zero => simp [groupsAux] at hblock
  | succ fuel ih =>
      cases items with
      | nil => simp [groupsAux] at hblock
      | cons item items =>
          rw [groupsAux, List.mem_cons] at hblock
          rcases hblock with rfl | hblock
          · exact List.length_take_le L (item :: items)
          · exact ih (items := (item :: items).drop L) hblock

theorem mem_groups_length_le (L : Nat) (items : List β)
    {block : List β} (hblock : block ∈ groups L items) :
    block.length ≤ L :=
  mem_groupsAux_length_le L items.length items hblock

/-- Collapse an ordered list of realized relations to one explicitly composed
relation.  The empty list correctly yields the identity relation. -/
noncomputable def collapse (block : List (RealizedRelation m n α))
    [Fintype α] [DecidableEq α] : RealizedRelation m n α where
  matrix := fun initial final =>
    PackedRelationCircuit.composeFinCircuit
      (fun i => (block.get i).matrix) initial final
  relation := fun x =>
    Rel.composeList (block.map fun entry => entry.relation x)
  realizes := by
    intro x initial final
    rw [PackedRelationCircuit.composeFinCircuit_eval_iff_composeList
      (relations := fun i => (block.get i).relation x)
      (x := x) (initial := initial) (final := final)]
    · have hrelations :
      List.ofFn (fun i => (block.get i).relation x) =
            block.map (fun entry => entry.relation x) := by
          apply List.ext_getElem
          · simp
          · intro i hi₁ hi₂
            simp
      rw [hrelations]
    · intro i
      exact (block.get i).realizes x

/-- Collapsing any finite block adds only five layers to a common depth
bound; the overhead is independent of the block length. -/
theorem collapse_depthAtMost (block : List (RealizedRelation m n α))
    [Fintype α] [DecidableEq α] (D : Nat)
    (hdepth : ∀ entry ∈ block, entry.DepthAtMost D) :
    (collapse block).DepthAtMost (D + 5) := by
  intro initial final
  apply PackedRelationCircuit.composeFinCircuit_depth_le _ initial final D
  intro i a b
  exact hdepth (block.get i) (List.get_mem block i) a b

/-- Exact numerical size consequence for collapsing one block. -/
theorem collapse_sizeAtMost (block : List (RealizedRelation m n α))
    [Fintype α] [DecidableEq α] (D S : Nat)
    (hdepth : ∀ entry ∈ block, entry.DepthAtMost D)
    (hsize : ∀ entry ∈ block, entry.SizeAtMost S) :
    (collapse block).SizeAtMost
      ((D + 5) * ((Fintype.card α) ^ (block.length + 1) *
        (block.length * (S + 1) + 3) + 1)) := by
  intro initial final
  apply Nat.mul_le_mul
  · apply PackedRelationCircuit.composeFinCircuit_depth_le _ initial final D
    intro i a b
    exact hdepth (block.get i) (List.get_mem block i) a b
  · apply PackedRelationCircuit.composeFinCircuit_width_le_of_size
    intro i a b
    exact hsize (block.get i) (List.get_mem block i) a b

/-- Common size bound after collapsing any block of length at most `L`. -/
def nextSizeBound (α : Type*) [Fintype α] (L D S : Nat) : Nat :=
  (D + 5) * ((Fintype.card α) ^ (L + 1) * (L * (S + 1) + 3) + 1)

theorem collapse_sizeAtMost_nextSizeBound
    (block : List (RealizedRelation m n α))
    [Fintype α] [Nonempty α] [DecidableEq α]
    (L D S : Nat) (hlen : block.length ≤ L)
    (hdepth : ∀ entry ∈ block, entry.DepthAtMost D)
    (hsize : ∀ entry ∈ block, entry.SizeAtMost S) :
    (collapse block).SizeAtMost (nextSizeBound α L D S) := by
  have hraw := collapse_sizeAtMost block D S hdepth hsize
  intro initial final
  apply (hraw initial final).trans
  unfold nextSizeBound
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (Fintype.card_pos)
      (Nat.add_le_add_right hlen 1)
  · exact Nat.add_le_add_right
      (Nat.mul_le_mul_right (S + 1) hlen) 3

/-- One blocking round: group consecutive entries and collapse each group. -/
noncomputable def collapseRound [Fintype α] [DecidableEq α]
    (L : Nat) (entries : List (RealizedRelation m n α)) :
    List (RealizedRelation m n α) :=
  (groups L entries).map fun block => collapse block

/-- One round decreases the list length by the advertised blocking factor. -/
theorem collapseRound_length_le_of_length_le_mul
    [Fintype α] [DecidableEq α] (L : Nat) (hL : 0 < L) (q : Nat)
    (entries : List (RealizedRelation m n α))
    (hlen : entries.length ≤ q * L) :
    (collapseRound L entries).length ≤ q := by
  simpa [collapseRound] using
    groups_length_le_of_length_le_mul L hL q entries hlen

/-- Every relation produced by one blocking round satisfies the common
five-layer enlarged depth bound. -/
theorem collapseRound_depthAtMost [Fintype α] [DecidableEq α]
    (L : Nat) (hL : 0 < L) (entries : List (RealizedRelation m n α))
    (D : Nat) (hdepth : ∀ entry ∈ entries, entry.DepthAtMost D) :
    ∀ entry ∈ collapseRound L entries, entry.DepthAtMost (D + 5) := by
  intro entry hentry
  rw [collapseRound, List.mem_map] at hentry
  rcases hentry with ⟨block, hblock, rfl⟩
  apply collapse_depthAtMost block D
  intro source hsource
  apply hdepth source
  rw [← flatten_groups L hL entries]
  exact List.mem_flatten.mpr ⟨block, hblock, hsource⟩

/-- One round transports a common gate-count bound through every group. -/
theorem collapseRound_sizeAtMost
    [Fintype α] [Nonempty α] [DecidableEq α]
    (L : Nat) (hL : 0 < L) (entries : List (RealizedRelation m n α))
    (D S : Nat) (hdepth : ∀ entry ∈ entries, entry.DepthAtMost D)
    (hsize : ∀ entry ∈ entries, entry.SizeAtMost S) :
    ∀ entry ∈ collapseRound L entries,
      entry.SizeAtMost (nextSizeBound α L D S) := by
  intro entry hentry
  rw [collapseRound, List.mem_map] at hentry
  rcases hentry with ⟨block, hblock, rfl⟩
  apply collapse_sizeAtMost_nextSizeBound block L D S
  · exact mem_groups_length_le L entries hblock
  · intro source hsource
    apply hdepth source
    rw [← flatten_groups L hL entries]
    exact List.mem_flatten.mpr ⟨block, hblock, hsource⟩
  · intro source hsource
    apply hsize source
    rw [← flatten_groups L hL entries]
    exact List.mem_flatten.mpr ⟨block, hblock, hsource⟩

/-- A blocking round preserves the exact composite semantic relation. -/
theorem composeList_collapseRound [Fintype α] [DecidableEq α]
    (L : Nat) (hL : 0 < L) (entries : List (RealizedRelation m n α))
    (x : BitState n) :
    Rel.composeList ((collapseRound L entries).map fun entry => entry.relation x) =
      Rel.composeList (entries.map fun entry => entry.relation x) := by
  unfold collapseRound collapse
  simp only [List.map_map, Function.comp_def]
  have hmap :
      List.map
          (fun block =>
            Rel.composeList (List.map (fun entry => entry.relation x) block))
          (groups L entries) =
        List.map Rel.composeList
          (List.map (fun block =>
            List.map (fun entry => entry.relation x) block) (groups L entries)) := by
    simp only [List.map_map, Function.comp_def]
  rw [hmap, Rel.composeList_map_composeList]
  apply congrArg Rel.composeList
  rw [← List.map_flatten, flatten_groups L hL]

/-- Repeat the same semantics-preserving blocking round. -/
noncomputable def collapseRounds [Fintype α] [DecidableEq α]
    (L : Nat) : Nat → List (RealizedRelation m n α) →
      List (RealizedRelation m n α)
  | 0, entries => entries
  | rounds + 1, entries => collapseRounds L rounds (collapseRound L entries)

/-- Numerical size recurrence for repeated rounds. -/
def roundsSizeBound (α : Type*) [Fintype α] (L : Nat) :
    Nat → Nat → Nat → Nat
  | 0, _D, S => S
  | rounds + 1, D, S =>
      roundsSizeBound α L rounds (D + 5) (nextSizeBound α L D S)

/-- `rounds` blocking rounds reduce a list fitting in `q * L^rounds`
positions to at most `q` realized relations. -/
theorem collapseRounds_length_le_of_length_le_mul_pow
    [Fintype α] [DecidableEq α] (L : Nat) (hL : 0 < L)
    (rounds q : Nat) (entries : List (RealizedRelation m n α))
    (hlen : entries.length ≤ q * L ^ rounds) :
    (collapseRounds L rounds entries).length ≤ q := by
  induction rounds generalizing entries q with
  | zero => simpa [collapseRounds] using hlen
  | succ rounds ih =>
      apply ih (entries := collapseRound L entries)
      apply collapseRound_length_le_of_length_le_mul L hL (q * L ^ rounds)
      simpa [pow_succ, Nat.mul_assoc] using hlen

/-- Every number of rounds preserves the exact ordered composite. -/
theorem composeList_collapseRounds [Fintype α] [DecidableEq α]
    (L : Nat) (hL : 0 < L) (rounds : Nat)
    (entries : List (RealizedRelation m n α)) (x : BitState n) :
    Rel.composeList
        ((collapseRounds L rounds entries).map fun entry => entry.relation x) =
      Rel.composeList (entries.map fun entry => entry.relation x) := by
  induction rounds generalizing entries with
  | zero => rfl
  | succ rounds ih =>
      rw [collapseRounds, ih]
      exact composeList_collapseRound L hL entries x

/-- After `rounds` rounds the common depth has increased by at most five
layers per round. -/
theorem collapseRounds_depthAtMost [Fintype α] [DecidableEq α]
    (L : Nat) (hL : 0 < L) (rounds : Nat)
    (entries : List (RealizedRelation m n α)) (D : Nat)
    (hdepth : ∀ entry ∈ entries, entry.DepthAtMost D) :
    ∀ entry ∈ collapseRounds L rounds entries,
      entry.DepthAtMost (D + 5 * rounds) := by
  induction rounds generalizing entries D with
  | zero => simpa [collapseRounds] using hdepth
  | succ rounds ih =>
      rw [collapseRounds]
      have hone := collapseRound_depthAtMost L hL entries D hdepth
      have hrest := ih (collapseRound L entries) (D + 5) hone
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hrest

/-- Repeated rounds satisfy the explicit size recurrence. -/
theorem collapseRounds_sizeAtMost
    [Fintype α] [Nonempty α] [DecidableEq α]
    (L : Nat) (hL : 0 < L) (rounds : Nat)
    (entries : List (RealizedRelation m n α)) (D S : Nat)
    (hdepth : ∀ entry ∈ entries, entry.DepthAtMost D)
    (hsize : ∀ entry ∈ entries, entry.SizeAtMost S) :
    ∀ entry ∈ collapseRounds L rounds entries,
      entry.SizeAtMost (roundsSizeBound α L rounds D S) := by
  induction rounds generalizing entries D S with
  | zero => simpa [collapseRounds, roundsSizeBound] using hsize
  | succ rounds ih =>
      rw [collapseRounds, roundsSizeBound]
      apply ih
      · exact collapseRound_depthAtMost L hL entries D hdepth
      · exact collapseRound_sizeAtMost L hL entries D S hdepth hsize

end RealizedRelation
end Allender
