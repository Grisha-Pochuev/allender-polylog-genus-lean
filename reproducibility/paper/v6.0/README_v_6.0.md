# Version 6.0 article bundle

This bundle contains the Version 6.0 manuscript for the Allender polylogarithmic-genus constant-width circuit problem.

## Files

- `allender_polylog_genus_acc0_proof_v_6.0.pdf` - publication-style manuscript.
- `allender_polylog_genus_acc0_proof_v_6.0.tex` - complete LaTeX source; bibliography is embedded, so no `.bib` file is required.
- `CHANGES_v_6.0.md` - changes from Version 5.0.
- `AUDIT_v_6.0.md` - post-revision adversarial audit.
- `SOURCE_VERIFICATION_v_6.0.md` - primary-source basis for the Hansen/Allender/ADR model interpretation.
- `MANIFEST.sha256` - SHA-256 checksums of the bundle files.

## Rebuilding the PDF

A standard TeX installation with the packages named in the preamble is sufficient. Run `pdflatex` at least twice; three passes are harmless and ensure all references have settled.

```bash
pdflatex -interaction=nonstopmode -halt-on-error allender_polylog_genus_acc0_proof_v_6.0.tex
pdflatex -interaction=nonstopmode -halt-on-error allender_polylog_genus_acc0_proof_v_6.0.tex
pdflatex -interaction=nonstopmode -halt-on-error allender_polylog_genus_acc0_proof_v_6.0.tex
```

No Python program is needed to build or verify the mathematical manuscript.

## Lean proof state referenced by the manuscript

Repository:
https://github.com/Grisha-Pochuev/allender-polylog-genus-lean

Pinned proof-source commit:
`37f90d350278a40c360375c7f8731c46a2610ec5`

Successful pull-request workflow run cited in the manuscript:
`31135088313`

The manuscript deliberately describes this as **partial formal verification** because ordinary orientable genus and Hansen's theorem remain explicit external interfaces.

## Status

Version 6.0 is a proof manuscript and verification package, not a certificate of peer-reviewed acceptance. The post-revision audit found no red- or orange-level gap in the theorem as explicitly stated, but independent expert review remains appropriate for a new claimed resolution of an open problem.
