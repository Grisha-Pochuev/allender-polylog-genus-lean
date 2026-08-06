import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Counting bad transitions and macroblocks

A transition `i → i+1` is bad when either endpoint layer is cut.  Hence each
cut layer contributes at most two transition indices.  Partitioning an ordered
transition sequence into singleton bad transitions and maximal good runs then
produces at most `2|B|+1` blocks.
-/

namespace Allender

/-- Transition indices incident to at least one cut layer. -/
def badTransitions (cuts : Finset Nat) : Finset Nat :=
  cuts ∪ cuts.image Nat.pred

/-- Every cut layer contributes at most two bad transition indices. -/
theorem card_badTransitions_le (cuts : Finset Nat) :
    (badTransitions cuts).card ≤ 2 * cuts.card := by
  unfold badTransitions
  calc
    (cuts ∪ cuts.image Nat.pred).card ≤ cuts.card + (cuts.image Nat.pred).card :=
      Finset.card_union_le _ _
    _ ≤ cuts.card + cuts.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * cuts.card := by omega

/-- Singleton bad blocks plus maximal good runs give at most `2b+1` blocks. -/
theorem macroblock_count_le_of_bad_count {blocks bad : Nat}
    (hpartition : blocks ≤ bad + (bad + 1)) :
    blocks ≤ 2 * bad + 1 := by
  omega

/-- Combining the two counting estimates gives the paper's `4|J|+1` bound. -/
theorem macroblock_count_le_of_cuts {blocks : Nat} (cuts : Finset Nat)
    (hpartition : blocks ≤ (badTransitions cuts).card + ((badTransitions cuts).card + 1)) :
    blocks ≤ 4 * cuts.card + 1 := by
  have hblocks : blocks ≤ 2 * (badTransitions cuts).card + 1 :=
    macroblock_count_le_of_bad_count hpartition
  have hbad := card_badTransitions_le cuts
  omega

end Allender
