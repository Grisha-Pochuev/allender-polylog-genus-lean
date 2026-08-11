# Human-review reproducibility package

This directory contains the human-review materials for the separator-based candidate proof of Eric Allender's Open Question 3.

## Current manuscript

The latest manuscript snapshot is **Version 6.0**:

```text
reproducibility/paper/v6.0/
```

Start with:

1. `paper/v6.0/README_v_6.0.md`
2. `paper/v6.0/allender_polylog_genus_acc0_proof_v_6.0.tex`
3. `paper/v6.0/AUDIT_v_6.0.md`
4. `paper/v6.0/SOURCE_VERIFICATION_v_6.0.md`
5. `paper/v6.0/MANIFEST.sha256`

The latest hostile audit recorded in the project found no remaining red/orange mathematical gap in Version 6.0 as stated. Independent expert review is still required.

The older `paper/allender_polylog_genus_acc0_proof.tex` and the existing top-level build scripts are retained as a historical reproducibility baseline.

## What this package is for

It gives an independent reader:

- the current versioned LaTeX manuscript;
- provenance and source-verification records;
- primary-source links;
- a claim-by-claim audit map;
- an independent-review checklist and report template;
- integrity records for preserved manuscript snapshots.

This package supports human mathematical review. File integrity and successful PDF generation do not by themselves prove the mathematics.

## Relation to Lean

The current end-to-end Lean reduction is maintained separately on branch:

[`formalization/canonical-components-v2`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/tree/formalization/canonical-components-v2)

The final Lean declaration is `Allender.allender_polylog_genus_in_ACC0`. Complete verification run `31135088313` succeeded for source commit `37f90d350278a40c360375c7f8731c46a2610ec5`.

To reproduce the Lean check after installing `elan`:

```bash
git switch formalization/canonical-components-v2
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

See [`LEAN_INTEGRATION.md`](LEAN_INTEGRATION.md) for the exact relationship between the prose and Lean tracks.

## Directory map

```text
reproducibility/
  README.md
  STATUS.md
  PROVENANCE.md
  SOURCES.md
  CLAIMS_AND_CHECKS.md
  REVIEW_CHECKLIST.md
  REVIEW_REPORT_TEMPLATE.md
  LEAN_INTEGRATION.md
  MANIFEST.sha256                  historical baseline manifest
  paper/
    README.md
    allender_polylog_genus_acc0_proof.tex   historical baseline
    v6.0/
      README_v_6.0.md
      allender_polylog_genus_acc0_proof_v_6.0.tex
      AUDIT_v_6.0.md
      CHANGES_v_6.0.md
      SOURCE_VERIFICATION_v_6.0.md
      MANIFEST.sha256
  notes/
    allender_polylog_genus_acc0_synopsis_en.md
  scripts/
    build-paper.sh
    verify-bundle.sh
```

## Recommended human-review order

1. Read `STATUS.md`.
2. Compare `SOURCES.md` with the statement in Version 6.0.
3. Read `paper/v6.0/allender_polylog_genus_acc0_proof_v_6.0.tex`.
4. Read the v6.0 audit and source-verification notes.
5. Work through `CLAIMS_AND_CHECKS.md` and `REVIEW_CHECKLIST.md`.
6. Consult `LEAN_INTEGRATION.md` and the authoritative Lean branch for machine-checking coverage.

## Historical build tools

The existing commands

```bash
cd reproducibility
bash scripts/verify-bundle.sh
```

and

```bash
cd reproducibility
bash scripts/build-paper.sh
```

continue to target the older unversioned reproducibility baseline. They should not be confused with the current Version 6.0 snapshot.
