# Polylogarithmic-Genus Constant-Width Circuits: Technical Synopsis

**Status:** complete candidate proof of Eric Allender's US$1000 open problem, not an independent acceptance, peer review, or bounty decision.

## Exact statement addressed

Let `{C_n}` be a nonuniform family of layered Boolean circuits. Assume that, for fixed constants `w, k, c` and `A > 0`,

- `width(C_n) <= w`;
- `|C_n| <= n^k`;
- the orientable genus of the underlying graph is at most `A(log(n+2))^c`.

The candidate proof concludes that the language recognized by `{C_n}` belongs to `ACC^0`.

The polynomial-size hypothesis is essential and is part of the theorem whose earlier published proof was retracted. Without a size bound, sufficiently long constant-width sequential circuits can compute arbitrary Boolean functions.

## Core new lemma: planarization by whole-layer deletion

Let `G` be a layered graph with `N` vertices and orientable genus at most `g`. The proof claims that one can delete at most

`g(ceil(log_2 N) + 1)`

whole layers so that the remaining graph is planar.

### Proof mechanism

1. By additivity of orientable genus over connected components, the number of nonplanar connected components of any residual graph is at most `g`.
2. In each nonplanar component, choose a weighted median layer: at most half of that component's vertices lie strictly below it, and at most half lie strictly above it.
3. Delete every selected global layer.
4. Since edges join only consecutive layers, no surviving connected component can contain vertices on both sides of a deleted layer.
5. Therefore every descendant component has at most half as many vertices as its parent.
6. After `ceil(log_2 N) + 1` rounds, a nonplanar descendant would have fewer than one vertex, which is impossible.
7. At most `g` layers are selected in each round, giving the claimed bound.

For polynomial-size circuits, `N = n^{O(1)}`. If `g = (log n)^{O(1)}`, the number of deleted layers is also polylogarithmic.

## Decomposition into macroblocks

A transition from layer `i` to layer `i+1` is called bad when either endpoint layer was deleted. The circuit is partitioned into:

- each bad transition as a singleton block;
- each maximal interval of nonbad transitions as one good block.

There are only `O(g log N)` blocks.

Every good block avoids all deleted layers and is therefore a subgraph of the planar residual graph. Every bad singleton block contains only two layers of constant width, so its transition behavior has constant size.

## Boundary states

Pad every layer to width `w` with isolated zero vertices. A layer state then belongs to the fixed set

`Q = {0,1}^w`.

For a macroblock `B` and states `p,q in Q`, define `R_B(p,q;x)` to mean that, on input `x`, block `B` maps boundary state `p` to boundary state `q`.

Input literals appearing inside a block are evaluated directly from `x`. A state on the first boundary of a block is treated as prescribed data; consistency is enforced by the preceding block, or by the initial-state predicate for the first layer.

The original circuit accepts exactly when there is a sequence of boundary states connecting an allowed initial state to an accepting final state through all macroblock relations.

## A common `ACC^0` simulation for all blocks

For a good planar block, a fixed input boundary state, and one output coordinate, the resulting circuit is planar, constant width, and polynomial size. Hansen's theorem places such a circuit in `ACC^0`.

A subtlety is that `ACC^0` is a union over fixed moduli. Applying Hansen separately to different block families would not by itself guarantee one common modulus.

The proof packages every block-output circuit into one padded family using input lengths

`N(n,t) = n^(d+2) + t`,

where `t` indexes the block, boundary state, and output coordinate. The ranges for different `n` are disjoint, and the padded family remains planar, constant width, and polynomial size. Hansen's theorem is then applied once to this single family. Consequently all block simulators share:

- one fixed modulus `m`;
- one constant depth bound;
- one polynomial size bound.

Equality with a complete output state `q` is obtained by conjoining the required output bits and complements of output bits after the Hansen simulation. Since `w` is constant, this adds only constant Boolean overhead.

Bad singleton blocks are constant-size Boolean predicates and can be padded to the same depth.

## Constant-depth composition of polylogarithmically many relations

Consider a consecutive group of at most

`L = ceil(log_2(n+2))`

relations on the fixed state set `Q`. The composite relation between endpoints `p,q` is

`OR over u_1,...,u_(L-1) in Q of AND_i R_i(u_(i-1),u_i;x)`.

The number of intermediate state sequences is

`|Q|^(L-1) = n^{O(1)}`

because `|Q| = 2^w` is constant. Thus one group can be composed with one unbounded-fan-in AND layer, one OR layer, and polynomial size.

If the original number of relations is `O((log n)^r)`, grouping `Theta(log n)` relations reduces the exponent of the logarithm by one. A constant number of rounds leaves a single relation. The total depth remains constant, the total size remains polynomial, and no new modulus is introduced.

## Final deduction

1. Delete only polylogarithmically many whole layers.
2. Decompose the circuit into only polylogarithmically many planar or constant-size macroblocks.
3. Simulate every macroblock relation in one common `AC^0[m]`.
4. Compose the relations in constant depth and polynomial size.
5. Add the constant-size initial-state and accepting-state conditions.

Therefore the language belongs to `ACC^0`.

## Scope and limitations

The argument proves only the nonuniform statement. It does not show that the cut layers, planar embeddings, or target circuits can be generated by a uniform low-complexity algorithm.

This synopsis describes a proof candidate. It does not replace an independent review of the complete manuscript.

## Priority checks for an independent reviewer

- Confirm the exact form of orientable-genus additivity and its applicability to residual disconnected graphs.
- Check the parent/descendant argument through all separator rounds.
- Verify exact compatibility between the circuit model used here and Hansen's theorem, including fan-in, COPY gates, constants, layering, and size.
- Check boundary input literals and equality with full output states.
- Verify the padded-family argument gives one fixed modulus for all blocks.
- Audit the polynomial-size bound across all relation-composition rounds.
- Confirm that the bounty question is the intended nonuniform polynomial-size theorem.
