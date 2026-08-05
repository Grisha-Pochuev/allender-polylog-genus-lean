# Paper workspace

This directory is reserved for the prose proof candidate and its publication-ready sources.

Planned contents:

```text
paper/
  allender_polylog_genus_acc0_proof.tex
  allender_polylog_genus_acc0_proof.pdf
  figures/
  sections/
```

The full 12-page candidate manuscript referred to in the project notes was not available as a file in the environment used to initialize this repository, so it has not been reconstructed from a summary. Add the original `.tex` and generated PDF here when available.

## Synchronization rule

Every theorem or lemma used in the paper should eventually include the corresponding Lean declaration name, for example:

```text
Lean: Allender.Rel.composeList_append
```

The paper must not describe the bounty problem as formally proved until the end-to-end Lean theorem satisfies the release criteria in `STATUS.md`.
