# Staged formalization plan

The project is divided so that each milestone produces a useful checked artifact without overstating the final result.

## Stage 0 — Reproducible foundation

- pin Lean and `mathlib`;
- build on every push and pull request;
- reject `sorry` and `admit`;
- keep an explicit axiom audit;
- document provenance and the trust boundary.

## Stage 1 — Finite-state semantics

- represent width-`w` layer states by `Fin w → Bool`;
- define transition relations between boundary states;
- prove identity, associativity, list composition, and functionality lemmas;
- later add Boolean matrices and equivalence with relational semantics.

Deliverable: the semantic algebra needed to compose circuit segments.

## Stage 2 — Layered circuit graphs

- define finite layered directed graphs;
- define deletion of whole layers;
- define interval blocks induced by cut layers;
- prove that surviving edges cannot jump between interval blocks;
- define paths and show that a surviving path remains inside one block.

Deliverable: the purely combinatorial separation facts, independent of topology.

## Stage 3 — Median-layer recursion

For every nonplanar connected component:

1. select a median layer;
2. delete that entire layer;
3. prove each surviving component contains at most half the old vertices;
4. recurse for at most `⌈log₂ N⌉ + 1` rounds;
5. charge at most one selected layer per positive-genus component per round;
6. use genus additivity to bound the number of such components by the total genus.

Deliverable: a theorem producing at most `O(g log N)` cut layers whose deletion leaves a planar graph.

## Stage 4 — Topological graph theory

- define embeddings in orientable surfaces or import an accepted combinatorial-map model;
- define orientable genus;
- prove monotonicity under subgraphs;
- prove or import additivity over connected components;
- connect the abstract `TopologyInterface` to the genuine definition.

Deliverable: removal of the temporary topology interface.

## Stage 5 — Circuit syntax and `ACC⁰`

- define bounded-fan-in source circuits and their layered normal form;
- define constant width and polynomial size;
- define `AC⁰[m]` and `ACC⁰` circuits with exact uniformity conventions;
- define recognition of languages;
- prove routine closure and substitution lemmas.

Deliverable: a concrete target proposition rather than an informal class name.

## Stage 6 — Planar macroblocks

- formalize each planar block's boundary transition relation;
- state the exact form of Hansen's theorem used;
- ensure input literals and negated boundary bits are treated correctly;
- prove that all blocks use one common fixed modulus, not a modulus depending on `n` or on the block.

Deliverable: `ACC⁰` descriptions of all block transition relations.

## Stage 7 — Polylogarithmic composition

- encode transition relations on the constant state set;
- compose many relations using balanced products / finite monoid evaluation;
- prove constant depth and polynomial size under the actual block-count bounds;
- track all constants and moduli explicitly.

Deliverable: an `ACC⁰` simulation of the full source circuit.

## Stage 8 — End-to-end theorem and audit

- state the exact Allender theorem;
- prove it from concrete definitions;
- run `#print axioms` on the final theorem;
- run Lean's independent environment checker;
- align every prose lemma with a Lean declaration;
- publish a release containing source, generated documentation, and the paper.

## Order of attack

The immediate next formal task is Stage 2's path/block theorem, followed by the finite combinatorial core of Stage 3. Topological genus should not be developed until the recursion theorem is stable in an abstract additive-cost setting.
