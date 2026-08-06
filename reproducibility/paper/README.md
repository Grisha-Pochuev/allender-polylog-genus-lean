# Manuscript source and PDF generation

`allender_polylog_genus_acc0_proof.tex` is the authoritative editable source in this repository.

Build the PDF from the repository root with:

```bash
cd reproducibility
bash scripts/build-paper.sh
```

The result is written to:

```text
reproducibility/build/allender_polylog_genus_acc0_proof.pdf
```

The reference PDF originally supplied to the project had 12 pages and SHA-256:

```text
e8d04870bf696263d34cdc863d2337897ca9ed4f46e997121e2c7da2a9f97225
```

A fresh build can have a different binary hash because PDF metadata may differ. Before packaging, a fresh rebuild and the reference PDF were rendered at 120 DPI and all 12 pages were pixel-identical.

The GitHub workflow `.github/workflows/reproducibility.yml` builds the PDF and uploads it as an Actions artifact whenever this directory changes.
