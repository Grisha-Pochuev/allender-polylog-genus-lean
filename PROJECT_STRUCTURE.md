# Project structure and review routes

This repository intentionally separates human review of the manuscript from machine checking of the Lean reduction.

## 1. Human-review track

**Authoritative location:** `main/reproducibility/`

The latest manuscript snapshot is **Version 6.0**:

```text
reproducibility/paper/v6.0/
```

Recommended route:

1. `reproducibility/STATUS.md`
2. `reproducibility/SOURCES.md`
3. `reproducibility/paper/v6.0/README_v_6.0.md`
4. `reproducibility/paper/v6.0/allender_polylog_genus_acc0_proof_v_6.0.tex`
5. `reproducibility/paper/v6.0/AUDIT_v_6.0.md`
6. `reproducibility/paper/v6.0/SOURCE_VERIFICATION_v_6.0.md`
7. `reproducibility/CLAIMS_AND_CHECKS.md`
8. `reproducibility/REVIEW_CHECKLIST.md`

The older unversioned manuscript under `reproducibility/paper/` is retained as a historical reproducibility baseline.

## 2. Lean formalization track

**Authoritative location:** branch `formalization/canonical-components-v2`.

The branch contains the end-to-end theorem:

```lean
Allender.allender_polylog_genus_in_ACC0
```

Recommended route:

1. `docs/REVIEW_GUIDE.md`
2. branch `README.md`
3. `Allender/MainTheorem.lean`
4. `Allender/AxiomAudit.lean`
5. branch `STATUS.md`
6. `docs/source-alignment.md`

To reproduce the complete machine check after installing `elan`:

```bash
git switch formalization/canonical-components-v2
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

The branch's GitHub Actions workflow calls the same script. The verified source tree is commit `37f90d350278a40c360375c7f8731c46a2610ec5`; complete verification run `31135088313` succeeded.

A green run checks the formal reduction relative to the explicitly named external genus facts and Hansen's published theorem. It does not claim those external results were formalized from first principles.

## Branch policy

### `main`

Stable public-facing branch. It contains:

- the project index and synchronized status;
- the human-review reproducibility package;
- Version 6.0 of the manuscript;
- an earlier Lean baseline retained for provenance.

The `Allender/` directory on `main` is not the authoritative current formalization.

### `formalization/canonical-components-v2`

Authoritative current Lean development. It contains the final theorem, the exact external trust boundary, the single verification script, and the detailed review guide.

### `formalization/full-reduction-v1`

Historical base of the current formalization. It should not be used as the current proof-status authority.

### Temporary branches

Branches beginning with `agent/` are maintenance branches and are not authoritative mathematical sources.

## Synchronization rules

When the manuscript changes:

1. preserve the versioned source;
2. update the human-review navigation and status;
3. record whether the Lean statement is affected;
4. do not infer Lean progress merely from prose changes.

When Lean changes:

1. update the branch status and `docs/source-alignment.md`;
2. run `scripts/verify-lean.sh` completely;
3. record the exact verified commit and workflow run;
4. keep the external assumptions visible in `AxiomAudit.lean`.

## Workflow separation

- manuscript/reproducibility workflows concern the human-review package;
- Lean verification concerns the authoritative formalization branch;
- documentation-only maintenance does not alter Lean proof objects.

## Release criterion

A combined public release should distinguish three facts clearly:

- the prose manuscript and its human-review status;
- the Lean-checked reduction and its explicit external assumptions;
- independent expert acceptance, which remains a separate requirement.
