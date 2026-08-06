# Human-review reproducibility package

This directory contains the ordinary scientific reproducibility package for the separator-based candidate proof of Eric Allender's Open Question 3.

## What this package does

It gives an independent reader the exact manuscript, its editable LaTeX source, an English technical synopsis, primary-source links, a claim-by-claim audit map, and repeatable integrity/build commands.

It is designed for **human mathematical review**. It is not, by itself, a machine-checked proof and it does not claim that the bounty has been won.

The Lean formalization is developed separately in this repository. The two efforts can proceed in parallel:

- this directory preserves and documents the prose proof candidate;
- the Lean branch formalizes selected claims and will eventually provide a machine-checked theorem if the full reduction is completed.

## Contents

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
  MANIFEST.sha256
  paper/
    README.md
    allender_polylog_genus_acc0_proof.tex
  notes/
    allender_polylog_genus_acc0_synopsis_en.md
  scripts/
    build-paper.sh
    verify-bundle.sh
```

## Fast verification

From the repository root:

```bash
cd reproducibility
bash scripts/verify-bundle.sh
```

The script always checks the SHA-256 integrity manifest. If `latexmk` is installed, it also rebuilds the PDF from the committed LaTeX source into `reproducibility/build/`. GitHub Actions performs the same build and publishes the PDF as a workflow artifact.

Manual build:

```bash
cd reproducibility
bash scripts/build-paper.sh
```

Required LaTeX packages are standard packages from a reasonably complete TeX Live installation (`texlive-latex-extra` is sufficient on Ubuntu).

## Recommended review order

1. Read `STATUS.md` so the claim level is clear.
2. Compare the exact problem in `SOURCES.md` with Theorem 1.1 of the manuscript.
3. Read the English synopsis in `notes/`.
4. Read the complete manuscript in `paper/`.
5. Work through `CLAIMS_AND_CHECKS.md` and `REVIEW_CHECKLIST.md`.
6. Record an independent verdict using `REVIEW_REPORT_TEMPLATE.md`.
7. Consult `LEAN_INTEGRATION.md` only to see which parts are or are not machine checked.

## Reproducibility versus correctness

A successful integrity check proves that the files are exactly the committed files. A successful LaTeX build proves that the manuscript can be regenerated. Neither proves the mathematics. Mathematical correctness requires expert review or a completed formal proof.
