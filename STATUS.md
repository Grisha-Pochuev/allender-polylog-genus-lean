# Formalization status ledger

Last verification update: 2026-08-06.

## Meaning of labels

- **checked** — Lean accepts the declaration without `sorry` or `admit` in a clean build; the compiled project has also passed `leanchecker`.
- **specified** — the intended mathematical statement has an explicit Lean interface, but no implementation has been supplied.
- **external** — a published theorem is intended to be imported or re-proved; it is not currently machine checked here.
- **pending** — no complete Lean statement/proof yet.

## Verification record

The initial development passed:

- `lake build` with Lean 4.32.2 and `mathlib` 4.32.2;
- compilation of `Allender/AxiomAudit.lean`;
- `lake env leanchecker Allender`;
- a source check rejecting `sorry` and `admit`.

The axiom audit reported only standard Lean foundations such as `propext`, `Classical.choice`, and `Quot.sound`; no theorem depended on `sorryAx`.

## Ledger

| ID | Mathematical item | Lean location | Status |
|---|---|---|---|
| S1 | Boolean state space `Fin w → Bool` | `Allender/FiniteState.lean` | checked |
| S2 | Cardinality `|Q_w| = 2^w` | `Allender.BitState.card` | checked |
| R1 | Identity and composition of relations | `Allender/Relation.lean` | checked |
| R2 | Associativity of relation composition | `Allender.Rel.comp_assoc` | checked |
| R3 | Semantics of splitting a list of transitions | `Allender.Rel.composeList_append` | checked |
| R4 | Functionality preserved by composition | `Allender.Rel.Functional.comp` | checked |
| G1 | Definition of a layered directed graph | `Allender/LayeredGraph.lean` | checked |
| G2 | Whole-layer cut block index | `Allender.LayeredDigraph.blockIndex` | checked |
| G3 | A surviving edge stays in one interval block | `edge_same_block_of_source_survives` | checked |
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
| M3 | Constant-depth composition of polylogarithmically many transitions | relation algebra only | partially checked |
| F1 | End-to-end Allender theorem | — | **not proved** |

## Release criterion for a claimed formal proof

The repository may describe the bounty problem as formally proved only when:

1. `F1` is a concrete Lean theorem with the intended circuit definitions;
2. `#print axioms` for `F1` contains no `sorryAx` and no undocumented project axiom;
3. every remaining external dependency is either already in a trusted Lean library or is stated exactly and identified by a published source;
4. a clean `lake build` and an independent Lean environment check succeed for the final theorem;
5. the prose paper and Lean theorem use the same hypotheses.
