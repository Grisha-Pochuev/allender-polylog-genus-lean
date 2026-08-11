# Relationship to the Lean formalization

The human-review package and the Lean development serve different purposes and remain intentionally separate.

## Human-review package

**Authoritative location:** `main/reproducibility/`

The current prose manuscript is Version 6.0 under:

```text
reproducibility/paper/v6.0/
```

This directory preserves the current manuscript source, source-verification notes, audit records, and review materials. It is the place to assess the written mathematical argument.

## Lean formalization

**Authoritative location:** branch [`formalization/canonical-components-v2`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/tree/formalization/canonical-components-v2)

Use that branch's:

- [`docs/REVIEW_GUIDE.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/docs/REVIEW_GUIDE.md);
- [`README.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/README.md);
- [`Allender/MainTheorem.lean`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/Allender/MainTheorem.lean);
- [`Allender/AxiomAudit.lean`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/Allender/AxiomAudit.lean);
- [`STATUS.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/STATUS.md);
- [`docs/source-alignment.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/docs/source-alignment.md).

The final Lean declaration is:

```lean
Allender.allender_polylog_genus_in_ACC0
```

Verified GitHub source commit: `37f90d350278a40c360375c7f8731c46a2610ec5`.  
Successful complete workflow run: `31135088313`.

## Reproduce the machine check

Install `elan`, then run from the repository root:

```bash
git switch formalization/canonical-components-v2
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

The branch's GitHub Actions workflow calls the same script.

## Exact trust boundary

Lean checks the end-to-end reduction for the concrete circuit model. The final theorem is relative to:

- five explicitly named standard facts about ordinary orientable graph genus;
- the published forward family-level direction of Hansen's planar constant-width theorem.

These external dependencies are isolated and visible in `Allender/AxiomAudit.lean`; they are not re-proved from foundational definitions in this repository.

## Manuscript-to-Lean relation

The two artifacts should not be silently substituted for each other:

- Version 6.0 is the current prose proof candidate and must still be read as mathematics;
- the Lean branch verifies the formal reduction and exposes its external assumptions;
- `docs/source-alignment.md` records the intended correspondence between manuscript steps and Lean declarations;
- independent expert acceptance remains separate from both reproducibility and machine checking.

## Branch history

`formalization/full-reduction-v1` is the historical base of the current formalization. The `Allender/` files on `main` are an earlier baseline retained for provenance and are not authoritative for current Lean coverage.

## Merge safety

Files under `reproducibility/` do not modify Lean source declarations. Documentation may link the two tracks, but changes to the prose manuscript do not by themselves alter the machine-checked theorem.
