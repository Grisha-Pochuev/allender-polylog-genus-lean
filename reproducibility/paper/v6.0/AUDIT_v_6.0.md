# Post-revision adversarial audit of Version 6.0

Audit date: 11 August 2026.

## Verdict

No red-level or orange-level mathematical gap was found in the proof **as explicitly stated in Version 6.0** during this audit. The remaining limitations are declared trust/scope boundaries rather than hidden proof steps.

This is not independent peer review and does not guarantee correctness. It records the failure modes actively attacked after the Version 6.0 edits.

## High-risk checks

### 1. Whole-layer planarization

**Attack:** Simultaneous deletion of the median layers of several nonplanar components might invalidate the single-layer halving lemma.

**Result:** Closed. Lemma 3.2 now applies to any connected vertex set avoiding a chosen layer. A next-round component is connected in the previous graph and avoids its parent's median layer even if additional layers were deleted simultaneously. It therefore lies entirely on one side and has at most half the parent's vertices.

### 2. Existence of the nonplanar ancestor chain

**Attack:** A next-round nonplanar component might fail to have a nonplanar parent in the previous remainder.

**Result:** Closed. The child lies in a unique previous connected component; monotonicity of genus makes that parent nonplanar. Repeated parents yield the halving chain used in the logarithmic-round contradiction.

### 3. Number of active nonplanar components

**Attack:** Several nonplanar components might share the same handles, invalidating the count `#components <= genus`.

**Result:** Closed relative to the classical Battle--Harary--Kodama--Youngs additivity theorem. Ordinary orientable graph genus is additive over components (indeed over blocks), so each positive-genus component consumes at least one unit in the sum.

### 4. Source-circuit model versus Allender's prize problem

**Attack:** Version 5.0 could have proved only a narrower Hansen gate basis unrelated to the bounty statement.

**Result:** The primary-source chain was checked. Allender's Section 4 introduces Open Question 3 directly as the unresolved polylogarithmic-genus extension of Hansen's planar constant-width characterization. Hansen explicitly defines fan-in-two AND/OR and unary COPY. Allender--Datta--Roy present their theorem as that extension. Version 6.0 now documents this lineage and does not claim an arbitrary-higher-fan-in normalization.

**Residual wording caveat:** the one-line bounty statement itself does not restate gate arities or the polynomial-size qualifier. The surrounding source context and ADR Theorem 6 support the interpretation used here, but the manuscript states the caveat openly.

### 5. Good-block planarity

**Attack:** A good transition run could still contain a deleted layer or acquire nonplanar boundary wiring.

**Result:** Closed. Both transitions incident with a cut layer are marked bad, so a good run contains no cut layer. The standalone boundary layer has no dependency parents and its graph embeds in the ambient good-block graph; fixing the boundary bits to constants preserves those parent sets.

### 6. Free boundary-state inputs at the Hansen step

**Attack:** Hansen might accidentally be applied to an `(n+w)`-input block while the final relation is supposed to be over the original `n` inputs.

**Result:** Closed. The boundary state `p` is fixed to a constant first layer before Hansen is applied. The Hansen batch therefore contains genuine `n`-input planar circuits `P_{B,p,j}`.

### 7. One common modulus

**Attack:** Applying Hansen independently to blocks might yield unrelated moduli.

**Result:** Closed. All good-block/state/output circuits are first encoded into one planar polynomial-size family. Hansen is invoked once on that family, producing one fixed modulus for all lengths and block indices.

### 8. De-padding after the combined Hansen family

**Attack:** The target circuit at coded length may use artificial padded input coordinates even though the source function ignores them.

**Result:** Closed explicitly in Version 6.0. Those target inputs are fixed to zero and gates reading them are replaced by constants. The modulus and depth are unchanged and size does not increase.

### 9. Polynomial size and integer grouping in finite-state relation composition

**Attack:** Enumerating intermediate states across polylogarithmically many relations might be quasipolynomial or exponential; additionally, the earlier draft wrote a real-valued quantity `C_0 (log_2(n+2)+1)` as though it were literally a number of relations.

**Result:** Closed and rewritten before release. The state space has constant size `|Q|=2^w`. Version 6.0 now defines the integer group length `L(n)=ceil(C_0 (log_2(n+2)+1))`. Hence a group has only `|Q|^{L(n)} = n^{O(1)}` candidate state sequences, the ceiling costs only a constant factor, and `M(n) <= L(n)^{c+1}`. Because `L(n)` is a positive integer, the number of groups after one round is at most `L(n)^c`; iterating leaves at most one relation after `c+1` rounds.

### 10. Zero and one boundary cases

**Attack:** The formulas might silently take `log 0`, fail when the macroblock list is empty, or force the exceptional input length `n=0` into an impossible normalized size bound.

**Result:** Improved. The cut corollary now treats `|C_n|=0` before taking a logarithm. The paper treats `n=0` by a single nonuniform constant target circuit using the same modulus. The Lean theorem remains explicitly narrower because its normalized source-size predicate includes `n=0`.

### 11. Width normalization

**Attack:** Padding a width-at-most-`w` presentation could introduce too many gates or raise the genus.

**Result:** Closed at paper level. Empty layers are removed first. With every remaining layer nonempty, the number of layers is at most the original gate count; padding to exactly `w` multiplies size by at most `w`. Unused constant gates can be isolated, so genus does not increase.

### 12. Lean verification claims

**Attack:** A green build could be presented as a foundational proof or could refer to a moving branch state.

**Result:** Closed in the manuscript wording. Version 6.0 pins proof source commit `37f90d350278a40c360375c7f8731c46a2610ec5`, identifies GitHub Actions run `31135088313` as a pull-request run, and continues to expose the external genus/Hansen interfaces. It calls the result partial formal verification.

## Remaining declared boundaries

1. Ordinary orientable genus is not defined from surface embeddings inside the Lean project; it is represented by an external definition boundary plus standard properties.
2. Hansen's forward theorem is imported as an external family-level theorem rather than reproved in Lean.
3. The `n=0` finite wrapper of the paper is not part of the current final Lean declaration.
4. Version 6.0 intentionally proves the Hansen-style source model supported by the primary-source chain; it does not prove a separate arbitrary-higher-fan-in theorem.

None of these is hidden in the manuscript.
