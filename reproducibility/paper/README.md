# Manuscript sources

This directory keeps both the historical reproducibility baseline and the current versioned manuscript.

## Current manuscript: Version 6.0

The latest manuscript snapshot is:

```text
v6.0/allender_polylog_genus_acc0_proof_v_6.0.tex
```

Companion files in `v6.0/` include:

- `README_v_6.0.md`
- `AUDIT_v_6.0.md`
- `CHANGES_v_6.0.md`
- `SOURCE_VERIFICATION_v_6.0.md`
- `MANIFEST.sha256`

The latest hostile audit recorded in the project found no remaining red/orange mathematical gap in Version 6.0 as stated; independent expert review is still required.

The original v6.0 source bundle also contained a PDF, but the binary PDF is not currently committed in this GitHub directory. The committed `.tex` is the exact source preserved from that bundle.

## Historical baseline

The unversioned file

```text
allender_polylog_genus_acc0_proof.tex
```

is an older 12-page reproducibility baseline. It is retained for provenance and for the existing legacy build workflow; it is not the current manuscript version.

The existing commands

```bash
cd reproducibility
bash scripts/build-paper.sh
```

and

```bash
cd reproducibility
bash scripts/verify-bundle.sh
```

continue to target that historical unversioned baseline.

## Lean verification

The current Lean proof is maintained separately on branch `formalization/canonical-components-v2`. See the repository root `README.md` or `formalization/README.md` for the exact branch, verified commit, workflow run, and local verification command.
