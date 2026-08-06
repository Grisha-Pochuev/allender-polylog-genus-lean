# Status of this package

**Package type:** ordinary scientific reproducibility package for human review.  
**Mathematical status:** complete proof candidate, not independently accepted.  
**Machine-checking status:** partial Lean formalization exists elsewhere in the repository; the end-to-end Allender theorem is not yet machine checked.  
**Package date:** 6 August 2026.

## What is complete here

- Exact English manuscript in LaTeX.
- Repeatable generation of the 12-page PDF from the committed source.
- Russian technical synopsis.
- Primary-source bibliography and links.
- Claim-by-claim audit guide.
- Independent-review checklist and report template.
- SHA-256 integrity manifest.
- Repeatable source-build and integrity-check scripts.

## What is not certified here

This package does not certify that:

- the new layer-planarization lemma is correct in every graph-genus convention;
- the circuit model exactly matches every detail of Hansen's model;
- the common-modulus padding argument has no hidden family-indexing issue;
- every polynomial-size and constant-depth bound has been formalized;
- Eric Allender or an independent specialist has accepted the proof;
- the $1000 bounty is payable.

Those are review questions, not file-reproducibility questions.

## Relation to Lean

The ordinary package and the Lean formalization are intentionally separate. Changes under `reproducibility/` do not alter Lean declarations. The current formalization work should only be described as a full machine-checked solution after the repository contains an end-to-end theorem matching the bounty statement and its axiom audit is explicit.
