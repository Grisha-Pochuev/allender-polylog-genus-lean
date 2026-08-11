# Allender polylogarithmic-genus project

This repository studies Eric Allender's US $1000 open question:

> Does every language accepted by a nonuniform family of polynomial-size, constant-width Boolean circuits of polylogarithmic orientable genus belong to `ACC⁰`?

The repository contains two deliberately separate review tracks:

1. a prose manuscript for human mathematical review;
2. an end-to-end Lean reduction for machine checking, relative to an explicit external trust boundary.

## Start here

### A. Current manuscript for human review

The latest manuscript snapshot is **Version 6.0**:

- [`reproducibility/paper/v6.0/allender_polylog_genus_acc0_proof_v_6.0.tex`](reproducibility/paper/v6.0/allender_polylog_genus_acc0_proof_v_6.0.tex)
- [`reproducibility/paper/v6.0/README_v_6.0.md`](reproducibility/paper/v6.0/README_v_6.0.md)
- [`reproducibility/paper/v6.0/AUDIT_v_6.0.md`](reproducibility/paper/v6.0/AUDIT_v_6.0.md)
- [`reproducibility/paper/v6.0/SOURCE_VERIFICATION_v_6.0.md`](reproducibility/paper/v6.0/SOURCE_VERIFICATION_v_6.0.md)
- [`reproducibility/paper/v6.0/MANIFEST.sha256`](reproducibility/paper/v6.0/MANIFEST.sha256)

Version 6.0 is the current revised article; the latest hostile audit recorded in the project found no remaining red/orange gap in the proof as stated, although independent expert review is still required.

Earlier drafts had unresolved issues around exact Hansen-model compatibility, obtaining one common modulus, and making the planarization/composition steps fully explicit.

The older `reproducibility/paper/allender_polylog_genus_acc0_proof.tex` is retained as a historical reproducibility baseline and is not the current manuscript version.

### B. Lean verification

The **authoritative current Lean development** is on branch:

[`formalization/canonical-components-v2`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/tree/formalization/canonical-components-v2)

Start with:

1. [`docs/REVIEW_GUIDE.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/docs/REVIEW_GUIDE.md)
2. [`README.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/README.md)
3. [`Allender/MainTheorem.lean`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/Allender/MainTheorem.lean)
4. [`Allender/AxiomAudit.lean`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/Allender/AxiomAudit.lean)
5. [`STATUS.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/canonical-components-v2/STATUS.md)

The final checked declaration is:

```lean
Allender.allender_polylog_genus_in_ACC0
```

The verified GitHub source tree is commit:

```text
37f90d350278a40c360375c7f8731c46a2610ec5
```

A complete successful GitHub Actions verification of that tree is run **31135088313** (`Lean verification #98`).

### Run Lean locally

Install `elan`, switch to the authoritative branch, and run from the repository root:

```bash
git switch formalization/canonical-components-v2
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

The verification script:

- rejects `sorry` and `admit` in project Lean files;
- runs the complete `lake build`;
- compiles the explicit axiom audit;
- independently replays the generated project modules with `leanchecker`.

The GitHub workflow on the authoritative branch calls the same `scripts/verify-lean.sh`. It can also be started with **Actions → Lean verification → Run workflow**, selecting `formalization/canonical-components-v2`.

### What the Lean result means

A green verification checks the complete reduction

```text
PolynomialSize → PolylogGenus → InACC0
```

for the concrete circuit definitions in the formalization. The proof is relative to five explicitly named standard facts about orientable graph genus and the published forward direction of Hansen's planar constant-width theorem; those external results are visible in the axiom audit and are not re-proved from first principles here.

## Repository map

```text
main
├── README.md                         project entry point
├── STATUS.md                         synchronized project status
├── PROJECT_STRUCTURE.md              branch and review routes
├── reproducibility/                  human-review materials
│   ├── paper/
│   │   ├── allender_polylog_genus_acc0_proof.tex   historical baseline
│   │   └── v6.0/                     current manuscript snapshot
│   ├── notes/                        technical synopsis
│   ├── SOURCES.md                    primary-source ledger
│   ├── CLAIMS_AND_CHECKS.md          mathematical audit map
│   └── scripts/                      legacy manuscript rebuild tools
├── formalization/README.md           pointer to current Lean branch
├── Allender/                         earlier Lean baseline on main only
└── .github/workflows/                repository workflows

formalization/canonical-components-v2
├── Allender/                         authoritative Lean source
├── Allender/MainTheorem.lean         final theorem
├── Allender/AxiomAudit.lean          explicit trust-boundary audit
├── scripts/verify-lean.sh             single verification entry point
├── docs/REVIEW_GUIDE.md              shortest review route
├── docs/source-alignment.md          manuscript-to-Lean map
├── README.md                         Lean-specific overview
└── STATUS.md                         declaration-level status ledger
```

`formalization/full-reduction-v1` is the historical base of the completed development, not the current authoritative branch. The small `Allender/` directory on `main` is retained for provenance and should not be used to judge current Lean coverage.

## Current claim level

- Version 6.0 is the current prose proof candidate.
- The project has an end-to-end Lean verification of the reduction on `formalization/canonical-components-v2`, relative to the explicitly listed external genus facts and Hansen theorem.
- The project does not claim a from-first-principles formalization of those external published results.
- The manuscript has not yet been independently accepted by a specialist, and the repository does not itself establish that the bounty is payable.

## Primary references

- Eric Allender, *Parting Thoughts and Parting Shots*, SIGACT News 54(1), 2023.
- Eric Allender, Samir Datta, Sambuddha Roy, *Topology inside NC¹*, CCC 2005 / ECCC TR04-108.
- Kristoffer Arnsfelt Hansen, *Constant Width Planar Computation Characterizes ACC⁰*, Theory of Computing Systems 39, 2006.
- J. Battle, F. Harary, Y. Kodama, J. W. T. Youngs, *Additivity of the Genus of a Graph*, 1962.

## Authorship and provenance

Project owner: **Grisha Pochuev**, independent researcher.

The manuscript, documentation, and Lean code were developed with AI assistance under the project owner's direction. Mathematical responsibility remains with the author and any eventual submitting author. Machine acceptance verifies only the declarations actually present and their explicitly listed dependencies.

## License

Lean source code and project documentation are released under the MIT License unless a file states otherwise.
