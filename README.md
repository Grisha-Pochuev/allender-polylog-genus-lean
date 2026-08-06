# Allender polylogarithmic-genus project

This repository studies Eric Allender's US $1000 open question:

> Does every language accepted by a nonuniform family of polynomial-size, constant-width Boolean circuits of polylogarithmic orientable genus belong to `ACC⁰`?

The project contains a complete **proof candidate** and an incomplete Lean formalization. These are two different verification tracks and are kept separate so that an external reader can immediately see what has and has not been checked.

## Start here

### Track A — human mathematical review

Use the stable `main` branch and open [`reproducibility/`](reproducibility/README.md).

It contains:

- the exact English LaTeX manuscript;
- an English technical synopsis;
- primary-source and provenance records;
- a claim-by-claim audit map;
- an independent-review checklist and report template;
- SHA-256 integrity checks;
- a repeatable 12-page PDF build.

**Status:** the package is reproducible, but the mathematics has not yet been independently accepted. A successful PDF build is not a correctness certificate.

### Track B — Lean formalization

Use the dedicated branch:

[`formalization/full-reduction-v1`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/tree/formalization/full-reduction-v1)

Begin with that branch's [`README.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/README.md) and [`STATUS.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/STATUS.md).

**Status:** substantial combinatorial and circuit infrastructure is machine checked, but the unconditional layer-planarization construction, the exact Hansen interface, the final `AC⁰[m]` construction, and the end-to-end theorem are still missing. Lean does **not** yet verify the $1000 result.

The small `Allender/` development present on `main` is an earlier stable baseline. It is not the authoritative current Lean development. All new Lean work belongs on `formalization/full-reduction-v1` until an explicitly reviewed integration is made.

## Repository structure

```text
main
├── README.md                         this project index
├── STATUS.md                         project-wide status
├── PROJECT_STRUCTURE.md              branch and review guide
├── reproducibility/                  human-review package
│   ├── paper/                        exact LaTeX manuscript
│   ├── notes/                        English technical synopsis
│   ├── SOURCES.md                    primary-source ledger
│   ├── CLAIMS_AND_CHECKS.md          mathematical audit map
│   ├── REVIEW_CHECKLIST.md           independent-review procedure
│   ├── REVIEW_REPORT_TEMPLATE.md     reviewer verdict template
│   ├── MANIFEST.sha256               integrity record
│   └── scripts/                      rebuild and verification commands
├── formalization/README.md           pointer to the Lean branch
├── Allender/                         earlier verified Lean baseline only
└── .github/workflows/
    ├── reproducibility.yml           manuscript build and integrity check
    └── lean.yml                      manual Lean verification of the checked-out ref

formalization/full-reduction-v1
├── Allender/                         authoritative current Lean source
├── Allender/AxiomAudit.lean          explicit dependency audit
├── README.md                         Lean-specific entry point
├── STATUS.md                         declaration-level proof ledger
└── docs/source-alignment.md          manuscript-to-Lean correspondence
```

See [`PROJECT_STRUCTURE.md`](PROJECT_STRUCTURE.md) for the branch policy, review routes, and integration rules.

## What each verification result means

| Result | What it establishes | What it does not establish |
|---|---|---|
| SHA-256 check passes | files match the committed package | mathematical correctness |
| LaTeX/PDF build passes | the manuscript is reproducible | correctness of the proof |
| Partial Lean build passes | present Lean declarations type-check | the missing final theorem |
| Independent expert review accepts the proof | a specialist endorses the argument | automatic machine verification |
| Final Lean theorem passes with an explicit axiom audit | formal implication is machine checked | correctness of any inaccurately formalized external premise |

## Current status

- The English manuscript is a complete proof candidate, not an accepted result.
- The human-review reproducibility package is present and independently rebuildable.
- The active Lean formalization is isolated on its own branch.
- The final Lean declaration corresponding to the bounty theorem does not yet exist.
- No file in this repository should be interpreted as confirmation that the bounty has been won.

See [`STATUS.md`](STATUS.md) for the concise project-wide ledger.

## Workflows

- `Reproducibility bundle` runs when files under `reproducibility/` change and may also be started manually.
- `Lean verification` is manual. Documentation-only changes do not start a Lean build.

## Primary references

- Eric Allender, *Parting Thoughts and Parting Shots*, SIGACT News 54(1), 2023.
- Eric Allender, Samir Datta, Sambuddha Roy, *Topology inside NC¹*, CCC 2005 / ECCC TR04-108.
- Kristoffer Arnsfelt Hansen, *Constant Width Planar Computation Characterizes ACC⁰*, Theory of Computing Systems 39, 2006.
- J. Battle, F. Harary, Y. Kodama, J. W. T. Youngs, *Additivity of the Genus of a Graph*, 1962.

## Authorship and provenance

Project owner: **Grisha Pochuev**, independent researcher.

The manuscript, documentation, and Lean code were developed with AI assistance under the project owner's direction. Mathematical responsibility remains with the author and any eventual submitting author. Machine acceptance verifies only the declarations actually present and their explicitly listed dependencies.

## License

Lean source code and project documentation are released under the MIT License unless a file states otherwise.
