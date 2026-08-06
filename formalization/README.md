# Lean formalization pointer

The authoritative current Lean development is maintained on the branch:

[`formalization/full-reduction-v1`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/tree/formalization/full-reduction-v1)

Use the branch's own:

- [`README.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/README.md) for orientation;
- [`STATUS.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/STATUS.md) for the exact proof ledger;
- [`docs/source-alignment.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/docs/source-alignment.md) for manuscript-to-Lean correspondence;
- [`Allender/AxiomAudit.lean`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/Allender/AxiomAudit.lean) for the trusted-dependency audit.

## Important distinction

The `Allender/` directory on `main` is an earlier stable baseline retained for provenance. It is not the current formalization and should not be used to assess total Lean progress.

The human-review manuscript package is maintained separately under [`reproducibility/`](../reproducibility/README.md).

## Current claim level

The active branch contains substantial checked infrastructure, but it does not yet contain the final end-to-end theorem resolving Allender's bounty question. Its own `STATUS.md` is authoritative for what is checked, conditional, external, or pending.
