# Paper location

The maintained prose proof candidate is now part of the international human-review reproducibility package:

- [candidate manuscript LaTeX source](../reproducibility/paper/allender_polylog_genus_acc0_proof.tex)
- [manuscript build instructions](../reproducibility/paper/README.md)
- [English technical synopsis](../reproducibility/notes/allender_polylog_genus_acc0_synopsis_en.md)
- [claim-by-claim audit map](../reproducibility/CLAIMS_AND_CHECKS.md)
- [independent-review checklist](../reproducibility/REVIEW_CHECKLIST.md)

The generated 12-page PDF is rebuilt by `.github/workflows/reproducibility.yml` and published as a workflow artifact.

## Synchronization rule

Every theorem or lemma used in the paper should eventually be mapped to the corresponding Lean declaration or to an explicitly named external theorem.

The paper and this repository must not describe the bounty problem as formally proved until the end-to-end Lean theorem satisfies the release criteria in `STATUS.md`. Likewise, the human-review package must remain labeled as a proof candidate until independent specialists have reviewed it.
