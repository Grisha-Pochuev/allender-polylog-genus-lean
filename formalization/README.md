# Lean formalization pointer

The authoritative current Lean development is on branch:

[`formalization/canonical-components-v2`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/tree/formalization/canonical-components-v2)

Use the branch's:

- [`docs/REVIEW_GUIDE.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/docs/REVIEW_GUIDE.md) for the shortest review route and exact verification command;
- [`README.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/README.md) for the full overview;
- [`Allender/MainTheorem.lean`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/Allender/MainTheorem.lean) for the final theorem;
- [`Allender/AxiomAudit.lean`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/Allender/AxiomAudit.lean) for the visible trust boundary;
- [`STATUS.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/STATUS.md) for the exact proof ledger;
- [`docs/source-alignment.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/docs/source-alignment.md) for manuscript-to-Lean correspondence.

## Final theorem and verified run

The final declaration is:

```lean
Allender.allender_polylog_genus_in_ACC0
```

Verified GitHub source commit:

```text
37f90d350278a40c360375c7f8731c46a2610ec5
```

Successful complete workflow run:

```text
31135088313
```

## Run locally

Install `elan`, then from the repository root run:

```bash
git switch formalization/canonical-components-v2
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

The script rejects `sorry`/`admit`, builds the project, compiles the axiom audit, and independently replays the project modules with `leanchecker`. The GitHub Actions workflow on the authoritative branch calls the same script.

## Exact claim level

Lean checks the end-to-end reduction from the formalized `PolynomialSize` and `PolylogGenus` hypotheses to `InACC0`. The proof is relative to five explicitly named standard facts about ordinary orientable graph genus and the published forward direction of Hansen's theorem; those external results are not re-proved from first principles.

## Branch distinction

- `formalization/canonical-components-v2` — authoritative current Lean development;
- `formalization/full-reduction-v1` — historical base of the completed development;
- `Allender/` on `main` — earlier stable baseline retained for provenance only.

The human-review manuscript package is maintained separately under [`reproducibility/`](../reproducibility/README.md), with Version 6.0 under `reproducibility/paper/v6.0/`.
