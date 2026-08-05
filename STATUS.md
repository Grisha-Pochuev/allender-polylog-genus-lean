# Formalization status ledger

Last structural update: 2026-08-06.

## Meaning of labels

- **implemented; build pending** — Lean source and proof terms have been written, but no clean build has yet been completed with the pinned toolchain.
- **checked** — Lean accepts the declaration without `sorry` or `admit` in a clean build.
- **specified** — the intended mathematical statement has an explicit Lean interface, but no implementation has been supplied.
- **external** — a published theorem is intended to be imported or re-proved; it is not currently machine checked here.
- **pending** — no complete Lean statement/proof yet.

## Ledger

| ID | Mathematical item | Lean location | Status |
|---|---|---|---|
| S1 | Boolean state space `Fin w → Bool` | `Allender/FiniteState.lean` | implemented; build pending |
| S2 | Cardinality `|Q_w| = 2^w` | `Allender.BitState.card` | implemented; build pending |
| R1 | Identity and composition of relations | `Allender/Relation.lean` | implemented; build pending |
| R2 | Associativity of relation composition | `Allender.Rel.comp_assoc` | implemented; build pending |
| R3 | Semantics of splitting a list of transitions | `Allender.Rel.composeList_append` | implemented; build pending |
| R4 | Functionality preserved by composition | `Allender.Rel.Functional.comp` | implemented; build pending |
| G1 | Definition of a layered directed graph | `Allender/LayeredGraph.lean` | implemented; build pending |
| G2 | Whole-layer cut block index | `Allender.LayeredDigraph.blockIndex` | implemented; build pending |
| G3 | A surviving edge stays in one interval block | `edge_same_block_of_source_survives` | implemented; build pending |
| T1 | Orientable genus of a finite graph | — | pending |
| T2 | Genus monotonicity under subgraphs | — | pending |
| T3 | Genus additivity over connected components | — | pending / external |
| T4 | Median-layer planarization with `O(g log N)` cuts | `TopologyInterface.planarize_by_layers` | specified, not proved |
| C1 | Boolean circuit syntax and evaluation | — | pending |
| C2 | Constant width and polynomial size predicates | profile only | partially specified |
| C3 | Planarity of the circuit graph | — | pending |
| C4 | Formal definition of `ACC⁰` | — | pending |
| H1 | Hansen planar constant-width characterization | — | pending / external |
| M1 | Macroblock transition semantics | — | pending |
| M2 | One common fixed modulus for all blocks | — | pending |
| M3 | Constant-depth composition of polylogarithmically many transitions | relation algebra only | partially implemented; build pending |
| F1 | End-to-end Allender theorem | — | **not proved** |

## Release criterion for a claimed formal proof

The repository may describe the bounty problem as formally proved only when:

1. `F1` is a concrete Lean theorem with the intended circuit definitions;
2. `#print axioms` for `F1` contains no `sorryAx` and no undocumented project axiom;
3. every remaining external dependency is either already in a trusted Lean library or is stated exactly and identified by a published source;
4. a clean `lake build` and an independent Lean environment check succeed;
5. the prose paper and Lean theorem use the same hypotheses.
