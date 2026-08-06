# Project status

Last project-structure review: 6 August 2026.

This file summarizes the whole repository. The detailed Lean proof ledger is maintained on the branch `formalization/full-reduction-v1`.

## Two independent tracks

| Track | Authoritative location | Current status |
|---|---|---|
| Human mathematical review | `main/reproducibility/` | complete reproducibility package; independent expert review still required |
| Lean formalization | branch `formalization/full-reduction-v1` | substantial partial formalization; final theorem not proved |

## Human-review package

The package contains the exact English manuscript source, an English synopsis, primary sources, provenance, integrity hashes, a claim audit, and a reviewer checklist.

Verified properties of the package:

- the LaTeX source compiles;
- the generated manuscript has 12 pages;
- integrity is checked with `MANIFEST.sha256`;
- the build is repeatable through `reproducibility/scripts/verify-bundle.sh`;
- GitHub Actions can build and publish the PDF artifact.

These checks establish reproducibility of the files, not correctness of the mathematics.

## Lean formalization

Authoritative branch:

```text
formalization/full-reduction-v1
```

Latest fully verified code commit recorded by that branch:

```text
443db2186476346f91f4af8f66f47aa39fe4dcb6
```

Successful recorded workflow run:

```text
31116859409
```

The branch reports machine-checked infrastructure for circuit semantics, fixed-width states, relation composition, layer deletion, weighted medians, component halving, genus-budget consequences relative to explicit external genus declarations, macroblock counting, `ACC⁰` syntax, state enumeration, and padding.

The following decisive obligations remain:

1. construct the canonical separation process for actual nonplanar components of every remainder graph;
2. prove the unconditional layer-planarization lemma;
3. extract and verify the planar macroblock subcircuits;
4. state Hansen's theorem exactly in the same circuit model or prove a conversion;
5. construct common-modulus `AC⁰[m]` simulations and the polylogarithmic relation composition circuits;
6. prove the final end-to-end theorem corresponding to the bounty statement.

Therefore the project does not yet contain a full machine proof of the $1000 result.

## Branch policy

- `main` is the stable public-facing index and human-review package.
- `formalization/full-reduction-v1` is the only active Lean development branch.
- Lean work is not copied into the human-review package.
- Manuscript changes are not represented as Lean progress until a named declaration is checked.
- Integration of the Lean branch into `main` should happen only through an explicitly reviewed pull request after its current status and axiom audit are verified.

The `Allender/` files on `main` are an earlier stable baseline and are not the authoritative current formalization.

## Workflow policy

- The reproducibility workflow runs only for relevant package changes or by manual request.
- Lean verification is manual, preventing ordinary documentation edits from creating unrelated Lean jobs.
- The Lean branch itself is also configured for manual verification.

## Claim discipline

The repository may claim a full formal verification only when:

1. a concrete final Lean theorem matches the manuscript hypotheses and conclusion;
2. the theorem has an explicit `#print axioms` audit with no `sorryAx` or undocumented premise;
3. the complete checked-out branch passes `lake build`, the axiom audit, and `leanchecker`;
4. the exact external theorems are isolated and cited;
5. the prose manuscript and formal statement are independently compared.

Until then, the correct description is:

> complete proof candidate with a reproducible human-review package and an incomplete Lean formalization.
