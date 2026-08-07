# Review guide

This page is the shortest route through the repository for a new mathematical
reviewer.  The project contains two complementary artifacts: a prose proof for
human review and a Lean reduction for machine checking.  Neither should be
silently substituted for the other.

## Five-minute orientation

1. Read [`problem.md`](problem.md) for the exact circuit problem and notation.
2. Read the main [`README`](../README.md), especially **Scope of the final
   theorem** and **Exact external boundary**.
3. Inspect [`Allender/MainTheorem.lean`](../Allender/MainTheorem.lean) for the
   final declaration `Allender.allender_polylog_genus_in_ACC0`.
4. Inspect [`Allender/AxiomAudit.lean`](../Allender/AxiomAudit.lean) to see the
   dependencies reported by `#print axioms`.
5. Use [`source-alignment.md`](source-alignment.md) to move between manuscript
   claims and Lean declarations.

## Which artifact answers which question?

| Question | Start here |
|---|---|
| What is the mathematical argument? | [`reproducibility/paper/allender_polylog_genus_acc0_proof.tex`](../reproducibility/paper/allender_polylog_genus_acc0_proof.tex) |
| How does the manuscript map to Lean? | [`source-alignment.md`](source-alignment.md) |
| What is the exact final Lean statement? | [`Allender/MainTheorem.lean`](../Allender/MainTheorem.lean) |
| Which results are trusted rather than formalized here? | [`trust-boundary.md`](trust-boundary.md) and [`Allender/AxiomAudit.lean`](../Allender/AxiomAudit.lean) |
| What is checked, conditional, external, or pending? | [`STATUS.md`](../STATUS.md) |
| How do I reproduce the machine check? | **Run the verification** below |

## Run the verification

The pinned versions are Lean 4.32.2 and mathlib 4.32.2.  Install
[`elan`](https://github.com/leanprover/elan), then run from the repository root:

```bash
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

The script performs four checks in order:

1. rejects `sorry` and `admit` in project Lean files;
2. builds every module imported by `Allender.lean`;
3. compiles the explicit axiom audit;
4. replays every generated project module sequentially with `leanchecker`.

The same script is used by `.github/workflows/lean.yml`.  A green workflow run
therefore checks the same proof objects as the documented local command.

## Suggested mathematical review order

1. **Models:** `FiniteState.lean`, `Gate.lean`, `CircuitLayer.lean`,
   `Circuit.lean`, `CircuitFamily.lean`, `ACC0Gate.lean`, `ACC0Circuit.lean`.
2. **Topology and planarization:** `OrientableGenus.lean`,
   `CanonicalComponents.lean`, `CanonicalPlanarization.lean`.
3. **Macroblocks:** `MacroblockPartition.lean`, `MacroblockCircuit.lean`,
   `BlockCircuit.lean`, `GoodBlockBatch.lean`.
4. **Simulation and composition:** `Hansen.lean`, `SimultaneousHansen.lean`,
   `FiniteRelationComposition.lean`, `RelationCompositionRounds.lean`,
   `AcceptanceCircuit.lean`.
5. **Quantitative close and final theorem:** `PolynomialBounds.lean`,
   `MainTheorem.lean`, `AxiomAudit.lean`.

## What a green run does and does not mean

A green run verifies the end-to-end reduction

```lean
PolynomialSize -> PolylogGenus -> InACC0
```

for the concrete circuit definitions in this repository.  The reduction is
relative to five named standard facts about orientable graph genus and the
published forward direction of Hansen's theorem.  Those six external results
are deliberately visible in the axiom audit; a green run does not claim that
they were re-proved from first principles here.

When reporting a problem, say whether it concerns the prose proof, its Lean
translation, a definition, or one of the named external results.  This makes a
review report actionable.
