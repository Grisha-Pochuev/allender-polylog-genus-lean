# Status of the human-review package

**Package type:** scientific reproducibility and review package.  
**Current manuscript:** Version 6.0 under `paper/v6.0/`.  
**Mathematical status:** complete proof candidate; not independently accepted.  
**Machine-checking status:** an end-to-end Lean reduction exists on `formalization/canonical-components-v2`, relative to explicit external genus facts and Hansen's theorem.  
**Status date:** 12 August 2026.

## Current manuscript

The latest manuscript source is:

```text
paper/v6.0/allender_polylog_genus_acc0_proof_v_6.0.tex
```

The same directory contains the v6.0 README, change record, hostile-audit record, source-verification notes, and integrity manifest. The older unversioned manuscript is retained as a historical reproducibility baseline.

The latest hostile audit recorded in the project found no remaining red/orange mathematical gap in Version 6.0 as stated. Independent expert review is still required before treating the result as accepted.

## Lean status

The authoritative current Lean branch is:

```text
formalization/canonical-components-v2
```

Final declaration:

```lean
Allender.allender_polylog_genus_in_ACC0
```

Verified source commit:

```text
37f90d350278a40c360375c7f8731c46a2610ec5
```

Successful complete workflow run:

```text
31135088313
```

The Lean verification checks the end-to-end reduction for the concrete formalized circuit model, relative to five named standard facts about ordinary orientable genus and the published forward family-level direction of Hansen's theorem. Those external results are not re-proved from first principles in the repository.

## Run Lean verification

After installing `elan`, from the repository root:

```bash
git switch formalization/canonical-components-v2
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

The same verification script is used by the GitHub Actions workflow on the authoritative branch.

## What is not certified here

Neither this package nor a green Lean run by itself certifies that:

- an independent specialist has accepted the prose proof;
- the five external genus facts or Hansen's theorem were formalized from foundations here;
- Eric Allender has accepted the result;
- the $1000 bounty is payable.

The manuscript, Lean reduction, external published dependencies, and independent expert review should therefore be reported as distinct layers of evidence.
