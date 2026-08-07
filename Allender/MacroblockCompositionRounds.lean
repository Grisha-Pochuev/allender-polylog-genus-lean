import Allender.MacroblockRelationCircuits
import Allender.RelationCompositionRounds

/-!
# Multi-round composition of the canonical macroblock relations

This module instantiates the generic blocking construction with the actual
canonical macroblocks.  Unlike the earlier one-shot circuit, the block length
and number of rounds are explicit parameters.  Exact semantics holds for every
positive block length and every number of rounds; quantitative family bounds
are layered on top of this construction.
-/

namespace Allender
namespace PlanarizedFamily

/-- The ordered list of actual macroblock relations, each bundled with its
concrete common-modulus target matrix and exact realization proof. -/
noncomputable def realizedMacroblockRelations (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) :
    List (RealizedRelation m n (BitState F.width)) :=
  List.ofFn fun b =>
    { matrix := fun initial final =>
        P.macroblockRelationCircuit A hn b initial final
      relation := fun x => SegmentRelation
        ((F.circuit n).macroblockLayers
          ((macroblockTags (F.circuit n).layers.tail.length
            (P.cuts n)).get b)) x
      realizes := fun x initial final =>
        P.macroblockRelationCircuit_eval_iff A hsim hn b initial final x }

/-- The bundled semantic relations are exactly the pre-existing ordered
macroblock relation list. -/
theorem realizedMacroblockRelations_semantics (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (x : BitState n) :
    (P.realizedMacroblockRelations A hsim hn).map
        (fun entry => entry.relation x) =
      (F.circuit n).macroblockRelations (P.cuts n) x := by
  unfold realizedMacroblockRelations Circuit.macroblockRelations
  rw [List.map_ofFn]
  simpa using List.ofFn_getElem_eq_map
    (macroblockTags (F.circuit n).layers.tail.length (P.cuts n))
    (fun block => SegmentRelation ((F.circuit n).macroblockLayers block) x)

/-- The initial bundled relations inherit the common macroblock depth bound. -/
theorem realizedMacroblockRelations_depthAtMost (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (D : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D) :
    ∀ entry ∈ P.realizedMacroblockRelations A hsim hn,
      entry.DepthAtMost (D + 4) := by
  rw [realizedMacroblockRelations, List.forall_mem_ofFn_iff]
  intro b initial final
  exact P.macroblockRelationCircuit_depth_le A hn b initial final D hdepth

/-- The initial bundled relations inherit the common pointwise gate-count
bound from the simultaneous Hansen batch. -/
theorem realizedMacroblockRelations_sizeAtMost (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (D S : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D)
    (hsize : ∀ t, (A.circuit n t).size ≤ S) :
    ∀ entry ∈ P.realizedMacroblockRelations A hsim hn,
      entry.SizeAtMost (macroblockRelationSizeBound F.width D S) := by
  rw [realizedMacroblockRelations, List.forall_mem_ofFn_iff]
  intro b initial final
  exact P.macroblockRelationCircuit_size_le A hn b initial final D S
    hdepth hsize

/-- The relations remaining after a chosen number of consecutive blocking
rounds. -/
noncomputable def roundedMacroblockRelations (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (L rounds : Nat) :
    List (RealizedRelation m n (BitState F.width)) :=
  RealizedRelation.collapseRounds L rounds
    (P.realizedMacroblockRelations A hsim hn)

/-- Final matrix entry after rounding and one last composition of the at-most
few remaining relations. -/
noncomputable def roundedComposedMacroblockCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (L rounds : Nat)
    (initial final : BitState F.width) : PackedACmCircuit m n :=
  (RealizedRelation.collapse
    (P.roundedMacroblockRelations A hsim hn L rounds)).matrix initial final

/-- Multi-round composition computes exactly the original ordered composite,
with no asymptotic or associativity gap. -/
theorem roundedComposedMacroblockCircuit_eval_iff
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (L : Nat) (hL : 0 < L) (rounds : Nat)
    (initial final : BitState F.width) (x : BitState n) :
    (P.roundedComposedMacroblockCircuit A hsim hn L rounds
      initial final).circuit.eval x = true ↔
      Rel.composeList
        ((F.circuit n).macroblockRelations (P.cuts n) x)
        initial final := by
  have hcollapse :=
    (RealizedRelation.collapse
      (P.roundedMacroblockRelations A hsim hn L rounds)).realizes
        x initial final
  rw [roundedComposedMacroblockCircuit]
  rw [hcollapse]
  change Rel.composeList
      ((P.roundedMacroblockRelations A hsim hn L rounds).map
        (fun entry => entry.relation x)) initial final ↔ _
  rw [roundedMacroblockRelations,
    RealizedRelation.composeList_collapseRounds L hL]
  rw [P.realizedMacroblockRelations_semantics A hsim hn x]

/-- If the original macroblock count fits in `L^rounds`, at most one relation
remains before the final constant-size composition. -/
theorem roundedMacroblockRelations_length_le_one
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (L : Nat) (hL : 0 < L) (rounds : Nat)
    (hcount :
      (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).length ≤
        L ^ rounds) :
    (P.roundedMacroblockRelations A hsim hn L rounds).length ≤ 1 := by
  apply RealizedRelation.collapseRounds_length_le_of_length_le_mul_pow
    L hL rounds 1
  simpa [realizedMacroblockRelations] using hcount

/-- Quantitative depth bound for every relation after the chosen rounds. -/
theorem roundedMacroblockRelations_depthAtMost
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (L : Nat) (hL : 0 < L) (rounds D : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D) :
    ∀ entry ∈ P.roundedMacroblockRelations A hsim hn L rounds,
      entry.DepthAtMost (D + 4 + 5 * rounds) := by
  exact RealizedRelation.collapseRounds_depthAtMost L hL rounds _ (D + 4)
    (P.realizedMacroblockRelations_depthAtMost A hsim hn D hdepth)

/-- Quantitative gate-count recurrence for every relation after the rounds. -/
theorem roundedMacroblockRelations_sizeAtMost
    (P : PlanarizedFamily F) (A : P.goodCircuitBatch.ACmBatch m)
    (hsim : A.Simulates) {n : Nat} (hn : 1 ≤ n)
    (L : Nat) (hL : 0 < L) (rounds D S : Nat)
    (hdepth : ∀ n t, (A.circuit n t).depth ≤ D)
    (hsize : ∀ t, (A.circuit n t).size ≤ S) :
    ∀ entry ∈ P.roundedMacroblockRelations A hsim hn L rounds,
      entry.SizeAtMost
        (RealizedRelation.roundsSizeBound (BitState F.width) L rounds
          (D + 4) (macroblockRelationSizeBound F.width D S)) := by
  exact RealizedRelation.collapseRounds_sizeAtMost L hL rounds _
    (D + 4) (macroblockRelationSizeBound F.width D S)
    (P.realizedMacroblockRelations_depthAtMost A hsim hn D hdepth)
    (P.realizedMacroblockRelations_sizeAtMost A hsim hn D S hdepth hsize)

end PlanarizedFamily
end Allender
