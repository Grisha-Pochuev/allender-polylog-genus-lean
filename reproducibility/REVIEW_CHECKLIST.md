# Independent mathematical review checklist

Reviewer name: ____________________  
Date: ____________________  
Version/commit: ____________________

Mark each item as **verified**, **problem found**, or **not checked**.

## A. Problem match

- [ ] The stated theorem matches the intended bounty problem.
- [ ] Polynomial-size, constant-width, nonuniformity, and orientable genus are all handled explicitly.
- [ ] No stronger hidden hypothesis is introduced.

## B. Layer planarization

- [ ] Genus additivity is applicable to the residual disconnected graph.
- [ ] The number of nonplanar components is at most the genus budget.
- [ ] A valid weighted median layer exists.
- [ ] Deleting that entire layer separates lower from upper layers.
- [ ] Every descendant component has at most half the parent's vertices.
- [ ] Every later nonplanar component can be followed through a parent chain.
- [ ] The logarithmic-round termination and layer-count bound are correct.

## C. Circuit decomposition and semantics

- [ ] Every good macroblock is a subgraph of the planarized graph.
- [ ] Every bad macroblock has only constant-size interface/behavior.
- [ ] The fixed state space `Q={0,1}^w` correctly represents all layer values.
- [ ] Inputs and negated inputs on arbitrary layers are handled correctly.
- [ ] Boundary consistency is neither omitted nor checked twice in a harmful way.

## D. Hansen interface

- [ ] The source circuit model matches Hansen's gate basis and fan-in.
- [ ] Constants, copies, designated output, and layering conversions have constant overhead.
- [ ] Each planar block has polynomial size and constant width under the same conventions.
- [ ] The theorem is used only in the direction actually proved by Hansen.

## E. Common parameters and composition

- [ ] The padding map `N(n,t)=n^(d+2)+t` gives disjoint ranges.
- [ ] Packaging all block-output circuits yields one polynomial-size planar family.
- [ ] One fixed modulus and depth therefore apply to every block.
- [ ] Equality with an output state, including zero bits, stays in the same `AC^0[m]`.
- [ ] The explicit OR-of-ANDs for `O(log n)` relations has polynomial size.
- [ ] Only constantly many composition rounds are required.
- [ ] Final depth is constant and final size is polynomial.

## F. Verdict

- [ ] I found no gap in the checked scope.
- [ ] I found a potentially repairable gap.
- [ ] I found a fatal gap or counterexample.
- [ ] I cannot reach a verdict without further source checking.

Detailed comments should be recorded with `REVIEW_REPORT_TEMPLATE.md` or in a signed review document that identifies the exact commit.
