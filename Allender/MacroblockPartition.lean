import Allender.MacroblockCounting
import Mathlib.Data.List.SplitBy

/-!
# Constructive macroblock partition

Section 4 of the manuscript partitions the ordered transition indices into
singleton bad transitions and maximal consecutive runs of good transitions.
`List.splitBy` supplies the canonical contiguous-run decomposition.
-/

namespace Allender

/-- A transition index together with the result of the cut-layer test. -/
structure TransitionTag where
  index : Nat
  bad : Bool
  deriving DecidableEq, Repr

/-- Ordered transition tags for indices `0, ..., count - 1`. -/
def transitionTags (count : Nat) (cuts : Finset Nat) : List TransitionTag :=
  (List.range count).map fun i =>
    ⟨i, decide (i ∈ badTransitions cuts)⟩

/-- Adjacent transitions belong to the same macroblock exactly when both are good. -/
def sameGoodRun (a b : TransitionTag) : Bool :=
  (!a.bad) && (!b.bad)

/-- Canonical partition into singleton bad transitions and maximal good runs. -/
def macroblockTags (count : Nat) (cuts : Finset Nat) : List (List TransitionTag) :=
  (transitionTags count cuts).splitBy sameGoodRun

@[simp] theorem transitionTags_length (count : Nat) (cuts : Finset Nat) :
    (transitionTags count cuts).length = count := by
  simp [transitionTags]

/-- Concatenating all macroblocks recovers the original ordered transition list. -/
@[simp] theorem flatten_macroblockTags (count : Nat) (cuts : Finset Nat) :
    (macroblockTags count cuts).flatten = transitionTags count cuts := by
  simp [macroblockTags]

/-- The partition is empty exactly when there are no transitions. -/
theorem macroblockTags_eq_nil_iff (count : Nat) (cuts : Finset Nat) :
    macroblockTags count cuts = [] ↔ count = 0 := by
  rw [macroblockTags, List.splitBy_eq_nil]
  simp [transitionTags]

/-- No macroblock produced by the canonical partition is empty. -/
theorem nil_not_mem_macroblockTags (count : Nat) (cuts : Finset Nat) :
    [] ∉ macroblockTags count cuts := by
  exact List.nil_notMem_splitBy sameGoodRun (transitionTags count cuts)

/-- Every macroblock is internally a chain of same-good-run adjacencies. -/
theorem macroblock_isChain {count : Nat} {cuts : Finset Nat}
    {block : List TransitionTag} (hblock : block ∈ macroblockTags count cuts) :
    block.IsChain fun a b => sameGoodRun a b := by
  exact List.isChain_of_mem_splitBy hblock

/-- Consecutive macroblocks are separated by a failed same-good-run test. -/
theorem macroblocks_separated (count : Nat) (cuts : Finset Nat) :
    (macroblockTags count cuts).IsChain fun a b =>
      ∃ ha hb, sameGoodRun (a.getLast ha) (b.head hb) = false := by
  exact List.isChain_getLast_head_splitBy sameGoodRun (transitionTags count cuts)

end Allender
