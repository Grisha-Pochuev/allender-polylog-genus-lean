# Manuscript-to-Lean alignment

Basis: the 12-page proof candidate *Polylogarithmic Genus Does Not Increase the Power of Constant-Width Polynomial-Size Circuits* and its Russian technical notes.

This document records what is genuinely represented in Lean. It must not be read as a claim that the final theorem is already formalized.

## Section 2 — Circuit model and notation

| Manuscript claim | Lean representation |
|---|---|
| Gates are AND, OR, literals, negated literals, and constants | `Allender.Gate` |
| A layer maps one width-`w` state to the next | `CircuitLayer.eval` |
| A layered circuit is a sequence of layers | `Circuit` |
| A nonuniform family contains one concrete circuit per input length | `CircuitFamily` |
| State space is `Q={0,1}^w`, `|Q|=2^w` | `BitState`, `BitState.card` |
| Circuit graph consists of gate positions and consecutive-layer dependencies | `Circuit.Vertex`, `Circuit.layeredGraph` |

The current source model pads every layer to the fixed width. Output-location conventions and exact equivalence with the model used by Hansen still need a formal conversion theorem.

## Section 3 — Layer planarization lemma

| Manuscript step | Lean declaration |
|---|---|
| Edges go only between consecutive layers | `LayeredDigraph.edge_next` |
| A surviving edge stays in one cut interval | `edge_same_block_of_source_survives` |
| A surviving undirected walk cannot cross a deleted layer | `no_surviving_walk_across_layer` |
| A finite component has a weighted median layer | `FiniteConnectedSet.exists_medianLayer` |
| A connected descendant lies wholly below or above the cut | `DescendantAfterCut.all_below_or_all_above` |
| A descendant has at most half the parent cardinality | `DescendantAfterCut.card_halves` |
| Repeated descendants form a numerical halving chain | `DescendantChain.toHalvingChain` |
| No nonempty descendant survives `log₂ N+1` cuts | `DescendantChain.impossible_after_log` |
| At most `g` positive-cost components exist under budget `g` | `card_le_of_positive_cost_sum_le` |
| At most `g(log₂N+1)` selections occur across bounded rounds | `separator_round_count_bound` |

Still missing: actual orientable genus, its monotonicity/additivity, construction of the complete round sequence, and the final theorem that deleting the union of selected layers leaves a planar graph.

## Section 4 — Macroblocks

| Manuscript step | Lean declaration |
|---|---|
| A cut layer is incident with at most two bad transitions | `card_badTransitions_le` |
| Singleton bad transitions plus maximal good runs give at most `4|J|+1` blocks | `macroblock_count_le_of_cuts` |

Still missing: an explicit macroblock datatype extracted from a circuit, maximal-run construction, and proof that every good block graph is a subgraph of the planarized graph.

## Section 5 — Relations on the state space

| Manuscript step | Lean declaration |
|---|---|
| Binary relations and sequential composition | `Rel.comp` |
| Composition is associative | `Rel.comp_assoc` |
| List composition matches splitting into sublists | `Rel.composeList_append` |
| Explicit intermediate-state witnesses match composition | `Rel.chain_iff_composeList` |
| Concrete circuit evaluation gives a transition chain | `Circuit.chain_from_zero_to_final` |

Still missing: block boundary predicates with arbitrary initial state, first-layer consistency predicate `I_p`, and final acceptance predicate.

## Section 6 — Simultaneous Hansen simulation

| Manuscript step | Lean declaration |
|---|---|
| Padded length `N(n,t)=n^(d+2)+t` | `paddedLength` |
| Gaps between adjacent ranges dominate `n^d` | `padding_gap` |
| Valid padded ranges for distinct `n` are disjoint | `paddedLength_injective_on_ranges` |

Still missing: a formal `ACC⁰` model, formal planar circuit families, the exact Hansen theorem, fixing ignored variables, and uniform common depth/modulus/size extraction.

## Section 7 — Polylogarithmic relation composition

| Manuscript step | Lean declaration |
|---|---|
| Number of assignments to `L` intermediate width-`w` states | `card_stateAssignments` |
| For `L=log₂(n+2)`, this number is polynomial | `card_stateAssignments_log_le` |
| Witness-chain semantics is the OR-over-assignments formula at proposition level | `RelationChain.lean` |

Still missing: concrete unbounded-fan-in AND/OR circuit construction, depth increment of two per round, polynomial size recurrence, and constant number of blocking rounds for an arbitrary fixed polylog exponent.

## Section 8 — Main theorem

No final theorem is currently present. The root module verifies the source-aligned lemmas above, not the bounty conclusion.

## External theorem boundary

The manuscript explicitly relies on:

1. orientable graph genus monotonicity;
2. Battle–Harary–Kodama–Youngs additivity of genus;
3. Hansen's constant-width planar characterization of `ACC⁰`.

These dependencies must eventually be represented by exact Lean theorem statements. Any theorem using them must expose them in `#print axioms` until their proofs are formalized.
