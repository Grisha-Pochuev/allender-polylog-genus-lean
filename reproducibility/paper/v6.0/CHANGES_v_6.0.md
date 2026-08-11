# Changes in Version 6.0

Version 6.0 is a conservative revision of Version 5.0. It does not change the separator-based proof strategy. It closes the remaining audit items and makes the scope of the theorem and of the Lean verification more exact.

## Mathematical and source-scope changes

1. **Strengthened the one-side separator lemma.** The former statement about a connected component after deleting one layer has been replaced by a stronger statement for any nonempty connected vertex set avoiding the chosen layer. This makes the halving step literally valid when all median layers selected in a round are deleted simultaneously.
2. **Made simultaneous deletion explicit in the proof of whole-layer planarization.** A surviving nonplanar child only needs to be connected and to avoid its parent's median layer; extra layers deleted in the same round cannot invalidate the halving argument.
3. **Recorded the primary-source lineage of Allender's Open Question 3.** Allender introduces the question as the unresolved polylogarithmic-genus extension of Hansen's planar characterization. Hansen explicitly defines constant-width source circuits using fan-in-two AND/OR and fan-in-one COPY gates, with literal/constant inputs. The manuscript therefore uses this convention explicitly and does not claim a theorem for a separate arbitrary-higher-fan-in source model.
4. **Kept the polynomial-size scope explicit.** Allender--Datta--Roy Theorem 6 and its ECCC abstract state the result for polynomial-size constant-width circuits. The manuscript continues to distinguish this sourced formulation from a hypothetical literal size-free reading of the one-line bounty statement.
5. **Handled the zero-gate case in the cut corollary.** The proof now separates `|C_n|=0` before writing a logarithm of the circuit size.
6. **Made de-padding after Hansen explicit.** Added input coordinates in the simultaneous family are fixed to zero in the target circuit, and target input gates reading those coordinates are replaced by constants. This preserves the modulus and depth and does not increase size.
7. **Clarified the target negation convention.** Complementing already computed target bits is treated as the standard constant-depth closure convention for `AC^0[m]`, with no change of modulus.
8. **Made exact-width padding more literal.** Empty layers are deleted first; then padding each nonempty layer to width `w` multiplies size by at most a constant and adds only unused constant gates, so genus does not increase.
9. **Tightened the weighted-median proof wording.** The left-side bound now follows from minimality of the chosen cumulative index, while the right-side bound follows from having already accumulated at least half the vertices.
10. **Made the composition block length an integer.** The paper now uses `L(n)=ceil(C_0 (log_2(n+2)+1))`, proves `M(n) <= L(n)^{c+1}`, accounts for the ceiling in the trajectory bound, and gives the exact integer ceiling argument showing that `c+1` grouping rounds suffice. This was caught during the post-revision audit before the final bundle was produced.

## Lean/reproducibility changes

11. **Pinned the proof state to an exact commit:** `37f90d350278a40c360375c7f8731c46a2610ec5`.
12. **Clarified GitHub Actions wording.** Workflow run `31135088313` is described as a successful pull-request run with that PR-head SHA; GitHub checked the generated pull-request merge result.
13. **Stopped using a moving branch tip as the proof-version identifier.** Later documentation/workflow changes are not treated as evidence for a different mathematical proof state.

## Presentation changes

14. Added a dedicated remark on the circuit convention inherited by Open Question 3.
15. Added primary-source URLs for Allender's author draft and Hansen's ECCC preliminary version.
16. Expanded the adversarial-check section to include simultaneous cuts, exact de-padding, source-model interpretation, and pinned Lean state.

No new mathematical assumption was introduced into the separator, macroblock, Hansen-padding, or relation-composition arguments.
