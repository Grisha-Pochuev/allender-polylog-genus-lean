# Proof obligations

This document is the gatekeeper for any future claim that the bounty problem has been formalized.

## A. Definitions

- [ ] Fix the exact Boolean gate basis of source circuits.
- [ ] Fix fan-in conventions and the treatment of negations.
- [ ] Define circuit size, depth, and width.
- [ ] Define layered normal form and prove normalization preserves the required bounds.
- [ ] Define the underlying undirected graph used for genus.
- [ ] Define embeddings in orientable surfaces and orientable genus.
- [ ] Define planar circuit graphs consistently with Hansen's theorem.
- [ ] Define `AC⁰[m]` and `ACC⁰`, including the fixed-modulus requirement.
- [ ] Decide and document whether families are uniform or nonuniform.

## B. Layer deletion and topology

- [x] Define interval blocks induced by whole-layer cuts.
- [x] Prove a surviving edge remains in one interval block.
- [ ] Define directed paths/walks in the cut graph.
- [ ] Prove a surviving path remains in one interval block.
- [ ] Define the median layer of a finite connected component.
- [ ] Prove deletion of a median layer halves every surviving component.
- [ ] Prove recursion terminates in at most `⌈log₂ N⌉ + 1` rounds.
- [ ] Prove genus is monotone under subgraphs.
- [ ] Prove orientable genus is additive over disjoint connected components.
- [ ] Prove at most `g` positive-genus components can coexist in one round.
- [ ] Derive the bound `|J| ≤ g(⌈log₂ N⌉ + 1)`.
- [ ] Prove deleting the selected layers leaves a planar graph.

## C. Macroblocks

- [ ] Define cut-layer boundary states.
- [ ] Define the semantic transition relation of a circuit segment.
- [x] Prove abstract relation composition is associative.
- [x] Prove list splitting preserves sequential relational semantics.
- [ ] Prove the whole circuit relation equals the composition of its macroblocks.
- [ ] Treat circuit inputs that occur in intermediate layers.
- [ ] Treat constants, repeated wires, and negated boundary bits.
- [ ] Bound the number of macroblocks after layer deletion.

## D. Hansen simulation

- [ ] State Hansen's theorem in exactly the form needed here.
- [ ] Verify whether the theorem gives `ACC⁰`, one `AC⁰[m]`, or a finite collection of moduli.
- [ ] Prove all planar block relations are representable using one fixed modulus independent of `n`.
- [ ] Bound the size and depth of each block simulator.
- [ ] Record every external theorem as an explicit imported dependency or named assumption.

## E. Composition in `ACC⁰`

- [ ] Encode relations on the constant set `BitState w`.
- [ ] Prove correctness of Boolean-matrix multiplication / relation composition.
- [ ] Give the exact constant-depth construction for composing polylogarithmically many relations.
- [ ] Prove its depth is independent of `n`.
- [ ] Prove its size is polynomial in `n`.
- [ ] Prove the construction stays within one fixed `ACC⁰` modulus set.
- [ ] Connect initial and accepting boundary states to language recognition.

## F. Final theorem and verification

- [ ] State the final theorem with no informal notation hidden in comments.
- [ ] Prove the final theorem in Lean.
- [ ] Confirm `#print axioms final_theorem` contains no `sorryAx`.
- [ ] Confirm no undocumented custom axiom occurs.
- [ ] Run `lake build` from a clean checkout.
- [ ] Run Lean's independent environment checker.
- [ ] Match the paper's hypotheses and conclusion to the Lean theorem line by line.
- [ ] Make a versioned public release before claiming the bounty.

## Known high-risk points

1. A layer separator is combinatorial; planarity after deletion is topological and must not be inferred without proof.
2. Genus additivity must match the exact graph model, including disconnected graphs and isolated vertices.
3. Hansen's result must be used with the same notion of planarity and circuit width.
4. `ACC⁰` requires fixed depth and fixed modular gates across the family.
5. Composing a polylogarithmic number of descriptions is not automatically a constant-depth operation.
6. A proof under abstract interfaces is a conditional reduction, not yet the bounty theorem.
