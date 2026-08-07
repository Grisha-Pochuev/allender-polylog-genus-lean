import Allender.FiniteRelationComposition
import Allender.MacroblockRelationCircuits

/-!
# Concrete composition circuit for all canonical macroblocks

This module joins the per-macroblock relation circuits to the original
ordered macroblock semantics.  The construction explicitly guesses every
constant-width boundary state, checks all selected relation entries in
parallel, and ORs all valid trajectories.
-/

namespace Allender
namespace PlanarizedFamily

/-- The indexed matrix of concrete target circuits for every canonical
macroblock. -/
noncomputable def macroblockMatrices (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n) :
    Fin (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).length →
      PackedRelationCircuit m n (BitState F.width) :=
  fun b initial final =>
    P.macroblockRelationCircuit A hn b initial final

/-- The correspondingly indexed concrete semantic relations. -/
def macroblockSemanticRelations (P : PlanarizedFamily F) (n : Nat)
    (x : BitState n) :
    Fin (macroblockTags (F.circuit n).layers.tail.length (P.cuts n)).length →
      Rel (BitState F.width) :=
  fun b => SegmentRelation
    ((F.circuit n).macroblockLayers
      ((macroblockTags (F.circuit n).layers.tail.length
        (P.cuts n)).get b)) x

/-- `List.ofFn` of the indexed relations is exactly the existing ordered
macroblock relation list, so no permutation or omission is hidden. -/
theorem ofFn_macroblockSemanticRelations (P : PlanarizedFamily F)
    (n : Nat) (x : BitState n) :
    List.ofFn (P.macroblockSemanticRelations n x) =
      (F.circuit n).macroblockRelations (P.cuts n) x := by
  unfold macroblockSemanticRelations Circuit.macroblockRelations
  simpa using List.ofFn_getElem_eq_map
    (macroblockTags (F.circuit n).layers.tail.length (P.cuts n))
    (fun block => SegmentRelation ((F.circuit n).macroblockLayers block) x)

/-- One concrete target circuit for the composite transition from `initial`
to `final` through all canonical macroblocks. -/
noncomputable def composedMacroblockCircuit (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) {n : Nat} (hn : 1 ≤ n)
    (initial final : BitState F.width) : PackedACmCircuit m n :=
  PackedRelationCircuit.composeFinCircuit (P.macroblockMatrices A hn)
    initial final

/-- Exact correctness of the complete macroblock-composition circuit. -/
theorem composedMacroblockCircuit_eval_iff (P : PlanarizedFamily F)
    (A : P.goodCircuitBatch.ACmBatch m) (hsim : A.Simulates)
    {n : Nat} (hn : 1 ≤ n) (initial final : BitState F.width)
    (x : BitState n) :
    (P.composedMacroblockCircuit A hn initial final).circuit.eval x = true ↔
      Rel.composeList
        ((F.circuit n).macroblockRelations (P.cuts n) x)
        initial final := by
  rw [composedMacroblockCircuit,
    PackedRelationCircuit.composeFinCircuit_eval_iff_composeList
      (relations := P.macroblockSemanticRelations n x)
      (x := x) (initial := initial) (final := final)]
  · rw [P.ofFn_macroblockSemanticRelations n x]
  · intro b
    exact fun a c => P.macroblockRelationCircuit_eval_iff
      A hsim hn b a c x

end PlanarizedFamily
end Allender
