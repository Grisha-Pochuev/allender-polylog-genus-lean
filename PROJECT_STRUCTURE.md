# Project structure and review routes

This repository intentionally separates two kinds of verification.

## 1. Human-review track

**Authoritative location:** `main/reproducibility/`

Purpose:

- preserve the exact manuscript and its source;
- make the PDF independently rebuildable;
- expose provenance and primary references;
- guide a specialist through the mathematical claims;
- record an independent review verdict.

Recommended order:

1. `reproducibility/STATUS.md`
2. `reproducibility/SOURCES.md`
3. `reproducibility/paper/allender_polylog_genus_acc0_proof.tex`
4. generated PDF from the reproducibility workflow
5. `reproducibility/notes/allender_polylog_genus_acc0_synopsis_en.md`
6. `reproducibility/CLAIMS_AND_CHECKS.md`
7. `reproducibility/REVIEW_CHECKLIST.md`
8. `reproducibility/REVIEW_REPORT_TEMPLATE.md`

A reviewer should not use the state of the Lean branch as a substitute for checking the prose argument.

## 2. Lean formalization track

**Authoritative base:** branch `formalization/full-reduction-v1`

**Current continuation:** branch `formalization/canonical-components-v2`

Purpose:

- formalize the exact source circuit model;
- formalize the separator and finite-state reductions;
- make external dependencies explicit;
- construct the final `ACC⁰` theorem when all obligations are complete.

Recommended order:

1. branch `README.md`
2. branch `STATUS.md`
3. `docs/source-alignment.md`
4. `Allender/AxiomAudit.lean`
5. the specific Lean modules named by the status ledger

A green partial build certifies only the declarations imported by the checked root module. It does not certify a theorem that has not yet been stated and proved.

## Branch policy

### `main`

Stable public-facing branch. It contains:

- the project index;
- the human-review reproducibility package;
- project-wide status;
- an earlier stable Lean baseline retained for provenance.

The `Allender/` directory on `main` is not the current authoritative formalization.

### `formalization/full-reduction-v1`

Stable base of the active Lean development. It contains the source-aligned
formalization and its declaration-level status ledger.

### `formalization/canonical-components-v2`

Checked continuation that constructs the actual nonplanar remainder
components, their canonical parents, and the unconditional layer-planarization
lemma relative to the named genus declarations.  It also connects the canonical
macroblock partition to concrete circuit layers, exact segment relations, and
standalone planar good-block circuits with exact semantics.  Hansen's forward
theorem is isolated as one exact family-level external dependency.  The branch
is reviewed through PR #7 before integration into the base branch.

Do not describe a manuscript claim as machine checked unless the branch status names the exact Lean declaration and a successful verification run includes it.

### Temporary branches

Branches with names beginning `agent/` are implementation branches used for isolated repository maintenance. Once their pull requests have been merged, they are obsolete and should be deleted.

## Integration policy

The two tracks may progress independently. They are synchronized through explicit records, not by informal claims.

When the manuscript changes:

1. update the LaTeX source;
2. rebuild and refresh the integrity manifest;
3. update the claim audit;
4. state whether the Lean branch is affected.

When Lean formalizes a manuscript step:

1. name the exact manuscript lemma or section;
2. name the exact Lean declaration;
3. update `docs/source-alignment.md` and branch `STATUS.md`;
4. run the full build and axiom audit;
5. do not upgrade the overall claim beyond what the final theorem establishes.

## Workflow separation

- `.github/workflows/reproducibility.yml` checks only the manuscript package and runs automatically only for relevant paths.
- `.github/workflows/lean.yml` is manual and checks the currently selected ref.

This prevents documentation maintenance from creating misleading Lean verification runs.

## Final release criterion

A combined public release should be prepared only after:

- the prose proof has received independent expert review;
- the final Lean theorem exists and matches the manuscript statement;
- its exact external assumptions are documented;
- the complete Lean branch passes build, axiom audit, and `leanchecker`;
- the manuscript, English synopsis, status ledgers, and citation metadata agree.
