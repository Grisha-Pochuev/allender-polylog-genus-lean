# Formalization status

Last verified commit: `aa11f91c9c740fb0cb53a377fb6a9bb667523a49`  
Successful workflow run: `31070265777`  
Toolchain: Lean 4.32.2, mathlib 4.32.2

## Status labels

- **checked** — built without `sorry`/`admit`, included in the root module, audited, and replayed by `leanchecker`.
- **partial** — a mathematically relevant core is checked, but the manuscript statement is not yet represented end to end.
- **external** — a published result still needs formalization or an exact named trust boundary.
- **pending** — not yet represented adequately in Lean.

## Source-aligned ledger

| ID | Item | Lean declaration/file | Status |
|---|---|---|---|
| C1 | Boolean gate basis and evaluation | `Gate.eval` | checked |
| C2 | Deterministic layer transition | `CircuitLayer.transition_functional` | checked |
| C3 | Concrete circuit and family evaluation | `Circuit.eval`, `CircuitFamily.accepts` | checked |
| C4 | Circuit dependency graph and size | `Circuit.layeredGraph`, `Circuit.size_eq_card_vertex` | checked |
| S1 | Fixed state space and cardinality | `BitState.card` | checked |
| R1 | Relation composition and associativity | `Rel.comp_assoc`, `Rel.composeList_append` | checked |
| R2 | Explicit intermediate-state witness semantics | `Rel.chain_iff_composeList` | checked |
| G1 | Layered graph and whole-layer cuts | `LayeredGraph.lean` | checked |
| G2 | No surviving path crosses a deleted layer | `no_surviving_walk_across_layer` | checked |
| G3 | Underlying undirected simple graph | `toSimpleGraph` | checked |
| M1 | Existence of weighted median layer | `exists_medianLayer` | checked |
| M2 | Each connected descendant halves | `DescendantAfterCut.card_halves` | checked |
| M3 | Descendant chain terminates after logarithmically many rounds | `DescendantChain.impossible_after_log` | checked |
| T1 | Positive-cost components are bounded by the total budget | `card_le_of_positive_cost_sum_le` | checked |
| T2 | Total selected layers over bounded rounds | `separator_round_count_bound` | checked |
| T3 | Orientable genus definition and monotonicity | — | pending |
| T4 | Genus additivity over components | Battle–Harary–Kodama–Youngs | external |
| T5 | Global construction of cut layers with planar remainder | — | partial |
| B1 | Bad-transition bound | `card_badTransitions_le` | checked |
| B2 | Macroblock-count bound | `macroblock_count_le_of_cuts` | checked |
| H1 | Exact Hansen theorem in the same circuit model | — | external |
| H2 | Common-family padding ranges | `padding_gap`, `paddedLength_injective_on_ranges` | checked |
| P1 | Polynomial number of intermediate state assignments | `card_stateAssignments_log_le` | checked |
| P2 | Explicit relation-chain semantics | `RelationChain.lean` | checked |
| P3 | Constant-depth `AC⁰[m]` circuit construction and size accounting | — | pending |
| F1 | End-to-end theorem: source family lies in `ACC⁰` | — | **not proved** |

## Removed material

The following earlier placeholders were deleted and must not be cited as verification:

- the structure with arbitrary `CircuitFamily.accepts` unrelated to a circuit;
- the `TopologyInterface` whose main planarization statement was merely a field;
- obsolete proof-obligation and planning documents referring to those interfaces.

## Release criterion

The repository may claim a full Lean verification of Allender's theorem only after:

1. a concrete final theorem quantifies over the source circuit family defined here;
2. the target is a concrete `ACC⁰` definition with fixed modulus/depth and polynomial size;
3. the global separator construction is proved for the actual graph/genus definitions;
4. Hansen and genus additivity are either formalized or isolated as exact published dependencies;
5. `#print axioms` for the final theorem contains no `sorryAx` or undocumented assumption;
6. clean build, axiom audit, and `leanchecker` all pass.
