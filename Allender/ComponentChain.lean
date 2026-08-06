import Allender.FiniteComponent
import Allender.Halving

/-!
# Chains of descendants under median-layer cuts

Following one nonplanar component through the recursive separator process gives
a nested chain of connected descendants. Each median cut halves the vertex
count. This file turns that graph-theoretic chain into `HalvingChain` and proves
that no nonempty descendant survives `log₂ N + 1` rounds.
-/

namespace Allender
namespace LayeredDigraph
namespace FiniteConnectedSet

variable {V : Type*} [DecidableEq V] {G : LayeredDigraph V}

/-- A chain obtained by choosing a median layer and one surviving descendant at each round. -/
inductive DescendantChain :
    G.FiniteConnectedSet → Nat → G.FiniteConnectedSet → Prop
  | nil (C : G.FiniteConnectedSet) : DescendantChain C 0 C
  | cons {parent terminal : G.FiniteConnectedSet} {rounds : Nat}
      (median : parent.MedianLayer)
      (descendant : parent.DescendantAfterCut median.index)
      (tail : DescendantChain descendant.component rounds terminal) :
      DescendantChain parent (rounds + 1) terminal

namespace DescendantChain

/-- Vertex cardinalities along a descendant chain form a numerical halving chain. -/
theorem toHalvingChain {start terminal : G.FiniteConnectedSet} {rounds : Nat}
    (h : DescendantChain start rounds terminal) :
    HalvingChain start.verts.card rounds terminal.verts.card := by
  induction h with
  | nil C => exact .nil C.verts.card
  | @cons parent terminal rounds median descendant tail ih =>
      exact .cons (descendant.card_halves median rfl) ih

/-- No nonempty descendant chain can survive `log₂ N + 1` median-cut rounds. -/
theorem impossible_after_log {start terminal : G.FiniteConnectedSet} {N : Nat}
    (h : DescendantChain start (Nat.log 2 N + 1) terminal)
    (hstart : start.verts.card ≤ N) : False := by
  have hzero : terminal.verts.card = 0 :=
    HalvingChain.terminal_eq_zero_of_start_le h.toHalvingChain hstart
  have hpositive : 0 < terminal.verts.card := terminal.nonempty.card_pos
  omega

end DescendantChain
end FiniteConnectedSet
end LayeredDigraph
end Allender
