# Provenance and custody of files

## Author and project owner

Grisha Pochuev, independent researcher.

The manuscript and supporting materials were prepared with AI assistance. Mathematical responsibility remains with the author and any eventual submitting author.

## Source artifacts

The files committed here originate from the project's source library and the reproducibility packaging process:

- `paper/allender_polylog_genus_acc0_proof.tex` - exact editable manuscript source from the project library;
- reference PDF - retained in the project source library; GitHub builds the PDF from the committed `.tex` source;
- `notes/allender_polylog_genus_acc0_synopsis_en.md` - English technical synopsis prepared from the complete manuscript for international review.

At packaging time, the reference PDF used for verification matched the supplied project PDF byte for byte, with SHA-256:

```text
e8d04870bf696263d34cdc863d2337897ca9ed4f46e997121e2c7da2a9f97225
```

The committed LaTeX source had SHA-256:

```text
6ecd5e76ed6d58004286b68bd6533bb3e55df057d8b7ca12f26ad9cc48002175
```

The authoritative current integrity values for the whole directory, including the English synopsis, are in `MANIFEST.sha256`.

## Build verification performed before commit

- LaTeX compilation completed successfully.
- The generated PDF contains 12 pages.
- The reference PDF and a fresh rebuild were rendered and compared at 120 DPI; all 12 pages were pixel-identical. (Binary PDF hashes can differ because of metadata.)
- The PDF was also rendered page by page for visual inspection.
- No clipped pages, missing pages, or obvious rendering failures were observed.
- After the normal multi-pass LaTeX build, no unresolved references remained; only harmless PDF-bookmark warnings for mathematics in one heading were reported.

Generated auxiliary files are deliberately not committed. They can be recreated with `scripts/build-paper.sh`.

## Change policy

Any mathematical edit to the `.tex` file should:

1. rebuild the PDF and refresh the workflow artifact;
2. update the relevant entries in `CLAIMS_AND_CHECKS.md`;
3. refresh `MANIFEST.sha256`;
4. record the reason in the Git commit message;
5. avoid silently upgrading the status from “candidate” to “proved”.
