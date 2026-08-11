# Project status

Last project-structure review: 12 August 2026.

This file summarizes the whole repository. The human-review manuscript is maintained on `main`; the authoritative current Lean development is on branch `formalization/canonical-components-v2`.

## Two complementary tracks

| Track | Authoritative location | Current status |
|---|---|---|
| Human mathematical review | `main/reproducibility/` | Version 6.0 is the current proof candidate; independent expert review still required |
| Lean formalization | `formalization/canonical-components-v2` | end-to-end reduction checked relative to five named genus facts and Hansen's published theorem |

## Current manuscript

The latest manuscript snapshot is:

```text
reproducibility/paper/v6.0/allender_polylog_genus_acc0_proof_v_6.0.tex
```

Its companion files are kept in the same `v6.0/` directory. The older unversioned manuscript remains in place as a historical reproducibility baseline.

The latest hostile audit recorded in the project found no remaining red/orange mathematical gap in Version 6.0 as stated. This is not a substitute for independent specialist review.

## Lean verification

Authoritative branch:

```text
formalization/canonical-components-v2
```

Final declaration:

```lean
Allender.allender_polylog_genus_in_ACC0
```

Verified GitHub source commit:

```text
37f90d350278a40c360375c7f8731c46a2610ec5
```

Successful complete GitHub Actions run:

```text
31135088313
```

The verified run rejects proof placeholders, performs `lake build`, compiles the explicit axiom audit, and replays the project modules with `leanchecker`.

To reproduce locally after installing `elan`:

```bash
git switch formalization/canonical-components-v2
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

The same script is called by the branch's GitHub Actions workflow.

## Exact machine-checking claim

Lean checks the end-to-end reduction from the concrete source-family hypotheses `PolynomialSize` and `PolylogGenus` to `InACC0` for the formalized circuit model. The final theorem depends on an explicit external boundary consisting of five named standard facts about ordinary orientable graph genus and the forward family-level direction of Hansen's planar constant-width theorem.

Those external published results are not re-proved from first principles in this repository; they are isolated and visible through `Allender/AxiomAudit.lean`.

## Branch policy

- `main` is the stable public-facing index and human-review package.
- `formalization/canonical-components-v2` is the authoritative current Lean development and contains the final theorem.
- `formalization/full-reduction-v1` is the historical base of the completed development.
- `Allender/` on `main` is an earlier baseline retained for provenance and is not authoritative for current Lean coverage.
- Manuscript and Lean status remain distinct: a prose revision does not alter Lean declarations, and a green Lean run does not replace independent human review of the manuscript.

## Claim discipline

The current correct description is:

> Version 6.0 is the current complete proof candidate; the repository also contains an end-to-end Lean verification of the formalized reduction relative to explicit published external results, while independent expert acceptance remains outstanding.

The repository does not itself certify that Eric Allender has accepted the proof or that the bounty is payable.
