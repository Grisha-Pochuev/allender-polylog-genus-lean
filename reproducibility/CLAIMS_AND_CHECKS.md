# Claim-by-claim audit map

This file maps the proof's main claims to the manuscript and states what an independent reviewer should verify. It is an audit guide, not an endorsement.

| ID | Claim | Manuscript location | Independent check |
|---|---|---|---|
| Q1 | The manuscript addresses Allender's Open Question 3 in the intended polynomial-size nonuniform setting. | Section 1, Theorem 1.1 and Remark 1.2 | Compare definitions and scope with Allender 2023 and ADR 2005. Confirm that adding polynomial size is intended rather than an unannounced strengthening of the hypothesis. |
| G1 | Orientable genus is monotone under subgraphs and additive over connected components. | Start of Section 3 | Verify the exact graph-genus convention and the cited Battle-Harary-Kodama-Youngs theorem. |
| G2 | At every round there are at most `g` nonplanar connected components. | Lemma 3.1 | Check that additivity applies to disconnected residual graphs and each nonplanar component has positive integer genus. |
| S1 | A weighted median layer exists for every finite component. | Lemma 3.1 | Check the cumulative layer-weight argument, including empty layers and a median layer containing many vertices. |
| S2 | Deleting the whole median layer leaves every descendant component with at most half the vertices. | Lemma 3.1 | Verify that all graph edges join consecutive layers and no surviving path can cross the deleted layer. |
| S3 | After `ceil(log2 N)+1` rounds no nonplanar component remains. | Lemma 3.1 | Check the descendant-chain argument and that every residual nonplanar component has a parent in the prior round. |
| S4 | At most `g(ceil(log2 N)+1)` whole layers are deleted. | Lemma 3.1 | Check duplicate selected layers and union cardinality only improve the bound. |
| B1 | The circuit splits into only `O(g log N)` planar good macroblocks and constant-size bad transitions. | Section 4 | Verify both incident transitions of every deleted layer are marked bad and every good block avoids all cut layers. |
| R1 | A macroblock is correctly represented as a relation on `Q={0,1}^w`. | Section 5 | Check treatment of repeated input literals, literals on boundary layers, constants, dummy vertices, and the initial-state predicate. |
| H1 | Every good macroblock output bit is covered by Hansen's planar constant-width theorem. | Lemma 6.2 | Check exact basis, fan-in, layering, planarity, size, constants, and designated-output conventions against Hansen. |
| U1 | All block simulators can use one fixed modulus, depth, and polynomial bound. | Lemma 6.1 | Check injectivity/disjointness of padded input lengths and that the resulting family remains polynomial size. |
| Z1 | Full output-state equality is obtained by a constant Boolean combination of simulated output bits. | Lemma 6.2 and Section 10.5 | Check closure under complement and conjunction without changing the fixed modulus. |
| C1 | `Theta(log n)` consecutive fixed-state relations can be composed in two additional Boolean layers and polynomial size. | Lemma 7.1 | Count intermediate state sequences and confirm the exponent depends only on constant width. |
| C2 | A polylogarithmic number of relations collapses in a constant number of grouping rounds. | Lemma 7.1 | Check the exact number of rounds for `M(n)=O((log n)^r)` and accumulated size/depth. |
| F1 | The final acceptance predicate is in one fixed `AC^0[m]` family. | Section 8 | Trace common parameters through all blocks, composition rounds, initial state, and final accepting state. |
| N1 | Only the nonuniform theorem is proved. | Sections 1, 8, 10.8 | Confirm no uniform construction is claimed or implicitly required by the bounty. |

## Highest-risk interfaces

A reviewer should prioritize these points:

1. exact compatibility with Hansen's model;
2. the global parent/descendant logic in the iterative layer deletion;
3. the common-modulus family padding;
4. boundary input literals and equality of complete states;
5. accumulated polynomial-size bounds in relation composition.
