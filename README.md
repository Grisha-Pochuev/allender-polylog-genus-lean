# Allender polylogarithmic-genus problem — Lean formalization

This private repository develops a Lean 4 formalization of a **candidate proof strategy** for Eric Allender's Open Question 3:

> Does every language accepted by constant-width circuit families of polylogarithmic genus lie in `ACC⁰`?

Allender attached a **US $1000 bounty** to this question in his 2023 SIGACT News column.

## Current status

This repository is **not yet a complete formal proof of the bounty problem**. It is an auditable formalization project. The initial Lean modules have now passed a clean build with the pinned Lean 4.32.2 and `mathlib` 4.32.2 toolchain.

| Component | Status |
|---|---|
| Boolean states of constant width | machine checked |
| Algebra of binary relations and sequential composition | machine checked |
| Basic invariant for cutting a layered graph along whole layers | machine checked |
| Precise quantitative interfaces for size and genus bounds | specified |
| Median-layer planarization theorem | pending |
| Orientable genus and additivity over components | pending / external dependency |
| Hansen's planar constant-width characterization of `ACC⁰` | pending / external dependency |
| Syntax and semantics of Boolean and `ACC⁰` circuits | pending |
| End-to-end theorem resolving Open Question 3 | **not yet proved** |

The successful verification run performed all of the following:

- rejected `sorry` and `admit` placeholders;
- ran `lake update` and restored the pinned `mathlib` cache;
- completed `lake build` successfully;
- compiled `Allender/AxiomAudit.lean` and found no `sorryAx`;
- replayed the compiled `Allender` modules with Lean's `leanchecker`.

A green verification run means only that the declarations currently present have been accepted by Lean. It does **not** mean that Allender's full problem has already been formalized or solved.

See [`STATUS.md`](STATUS.md) and [`docs/proof-obligations.md`](docs/proof-obligations.md) for the detailed proof ledger.

## Human-review reproducibility package

The complete candidate manuscript, its exact LaTeX source, an English technical synopsis, primary-source ledger, claim-by-claim audit map, independent-review checklist, integrity manifest, and repeatable PDF build are in [`reproducibility/`](reproducibility/README.md).

This package supports international **human mathematical review** and is separate from the unfinished Lean formalization. It does not claim independent acceptance, a completed machine proof, or entitlement to the bounty.

## Why formalize this result?

The 2005 paper *Topology inside NC¹* claimed that constant-width, polynomial-size circuits of polylogarithmic genus compute only languages in `ACC⁰`. Eric Allender later stated that the proof of its main theorem is incorrect and that the theorem remains open. A formal development is intended to:

1. expose every hidden definition and dependency;
2. isolate the genuinely new combinatorial argument from published external results;
3. prevent accidental reuse of the invalid topological step from the earlier proof;
4. provide a reproducible artifact that specialists can inspect without trusting prose alone.

## Repository layout

```text
Allender/
  FiniteState.lean              Boolean states of fixed width
  Relation.lean                 relation composition and list semantics
  LayeredGraph.lean             layered directed graphs and cut-layer invariant
  Interfaces/
    Topology.lean               exact statement expected from topology
    Complexity.lean             language/family profiles and growth predicates
  AxiomAudit.lean               `#print axioms` checks for central lemmas
Allender.lean                   root import

docs/
  problem.md                    exact problem and historical context
  candidate-proof-outline.md    current prose strategy mapped to Lean tasks
  formalization-plan.md         staged implementation plan
  proof-obligations.md          checklist of mathematical obligations
  trust-boundary.md             what Lean does and does not currently certify
  references.bib                core bibliography

reproducibility/
  paper/                        exact candidate manuscript source
  notes/                        English technical synopsis
  SOURCES.md                    primary-source ledger
  CLAIMS_AND_CHECKS.md          claim-by-claim audit map
  REVIEW_CHECKLIST.md           independent-review procedure
  MANIFEST.sha256               committed-file integrity checks

paper/README.md                 pointer to the maintained manuscript package
.github/workflows/lean.yml      Lean build and proof checks
.github/workflows/reproducibility.yml
                                manuscript integrity and PDF build
```

## Building locally

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake update
lake exe cache get
lake build
lake env lean Allender/AxiomAudit.lean
lake env leanchecker Allender
```

The Lean toolchain and `mathlib` release are pinned in the repository.

## GitHub verification

The Lean workflow runs automatically on pushes to `main` and can also be started manually from the Actions tab. It checks for proof placeholders, builds the project, compiles the axiom audit, and runs `leanchecker` on the root `Allender` module.

The separate reproducibility workflow checks the integrity manifest, rebuilds the 12-page manuscript from LaTeX, validates the page count, and publishes the generated PDF as an Actions artifact.

## Proof discipline

The project follows these rules:

- no `sorry` or `admit` in committed Lean files;
- every imported external theorem must be named and documented;
- abstract interfaces are not described as completed formalizations;
- `#print axioms` is kept for central lemmas;
- prose claims in the paper must be linked to specific Lean declarations;
- no result is promoted to “checked” until a clean build succeeds.

## Primary sources

- Eric Allender, *Parting Thoughts and Parting Shots*, SIGACT News 54(1), 2023:  
  https://people.cs.rutgers.edu/~allender/papers/sigact.news.draft.pdf
- Eric Allender, Samir Datta, Sambuddha Roy, *Topology inside NC¹*, ECCC TR04-108 / CCC 2005:  
  https://eccc.weizmann.ac.il/eccc-reports/2004/TR04-108/index.html
- Kristoffer Arnsfelt Hansen, *Constant Width Planar Computation Characterizes ACC⁰*, Theory of Computing Systems 39, 2006.

## Authorship and provenance

Project owner: **Grisha Pochuev**, independent researcher.

The initial repository structure and Lean code were prepared with AI assistance under the project owner's direction. Mathematical responsibility remains with the author. Machine acceptance by Lean verifies only the declarations actually present and their listed dependencies.

## License

Lean source code and project documentation are released under the MIT License unless a file states otherwise.
