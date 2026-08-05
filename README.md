# Allender polylogarithmic-genus problem — Lean formalization

This private repository develops a Lean 4 formalization of a **candidate proof strategy** for Eric Allender's Open Question 3:

> Does every language accepted by constant-width circuit families of polylogarithmic genus lie in `ACC⁰`?

Allender attached a **US $1000 bounty** to this question in his 2023 SIGACT News column.

## Current status

This repository is **not yet a complete formal proof of the bounty problem**. It is an auditable formalization project. A green continuous-integration run means only that the theorems currently present in the repository have been accepted by Lean.

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

See [`STATUS.md`](STATUS.md) and [`docs/proof-obligations.md`](docs/proof-obligations.md) for the detailed proof ledger.

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
  AxiomAudit.lean               `#print axioms` checks for proved lemmas
Allender.lean                   root import

docs/
  problem.md                    exact problem and historical context
  formalization-plan.md         staged implementation plan
  proof-obligations.md          checklist of mathematical obligations
  trust-boundary.md             what Lean does and does not currently certify

.github/workflows/lean.yml      reproducible build and proof checks
```

## Building locally

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake update
lake exe cache get
lake build
```

The Lean toolchain and `mathlib` release are pinned in the repository.

## Proof discipline

The project follows these rules:

- no `sorry` or `admit` in committed Lean files;
- every imported external theorem must be named and documented;
- abstract interfaces are not described as completed formalizations;
- `#print axioms` is kept for central checked lemmas;
- prose claims in the paper must be linked to specific Lean declarations;
- changes are accepted only after `lake build` succeeds.

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
