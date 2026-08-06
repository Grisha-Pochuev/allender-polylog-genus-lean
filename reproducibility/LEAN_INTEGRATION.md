# Relationship to the Lean formalization

The human-review package and the Lean development serve different purposes and are intentionally decoupled.

## Ordinary reproducibility package

This directory preserves:

- the exact prose proof candidate;
- its compiled rendering;
- source provenance and integrity hashes;
- an explicit expert-review procedure.

It can be completed and reviewed even while Lean work is unfinished.

## Lean formalization

The moving Lean work is maintained on the repository's formalization branch. Its purpose is to express the same definitions and deductions in Lean and eventually prove an end-to-end theorem.

A green build of partial Lean modules does not certify the whole manuscript. Conversely, a reproducible PDF does not certify the mathematics.

## Synchronization rule

When a manuscript claim is formalized, record the correspondence in this table or a successor file:

| Manuscript claim | Intended Lean object | Current interpretation |
|---|---|---|
| Fixed width state space | `BitState` and its cardinality | combinatorial infrastructure |
| Relation composition | `Rel.comp`, list composition, chain semantics | formal support for macroblock composition |
| No path crosses a deleted whole layer | layered-graph cut lemmas | formal support for the halving step |
| Weighted median layer | median-layer existence declaration | formal support for separator rounds |
| Genus monotonicity/additivity | explicitly named external topology declarations unless fully formalized | trust boundary |
| Global planarizing layer set | end-to-end separator theorem | must be proved, not assumed |
| Hansen characterization | exact external theorem in the same circuit model unless fully formalized | trust boundary |
| Common modulus padding | padding family lemmas plus circuit-family construction | reduction step |
| Polylogarithmic relation composition in `AC^0[m]` | explicit target-circuit construction and bounds | reduction step |
| Main theorem | concrete theorem from source circuit family to `ACC^0` | release criterion |

## Merge safety

All files in this package live under `reproducibility/`. They do not change Lean source files, the Lean toolchain, or the existing Lean workflow. The package can therefore be merged independently and later rebased or merged into the formalization branch with minimal conflict risk.
