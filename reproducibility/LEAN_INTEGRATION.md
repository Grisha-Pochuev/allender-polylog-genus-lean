# Relationship to the Lean formalization

The human-review package and the Lean development serve different purposes and are intentionally separated.

## Human-review package

**Authoritative location:** `main/reproducibility/`

This directory preserves:

- the exact prose proof candidate;
- its repeatable PDF build;
- source provenance and integrity hashes;
- an explicit expert-review procedure.

It can be reviewed independently while Lean work remains incomplete.

## Lean formalization

**Authoritative location:** branch [`formalization/full-reduction-v1`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/tree/formalization/full-reduction-v1)

Use that branch's:

- [`README.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/README.md);
- [`STATUS.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/STATUS.md);
- [`docs/source-alignment.md`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/docs/source-alignment.md);
- [`Allender/AxiomAudit.lean`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/blob/formalization/full-reduction-v1/Allender/AxiomAudit.lean).

The `Allender/` files on `main` are an earlier stable baseline retained for provenance. They are not the authoritative current formalization.

A green build of partial Lean modules does not certify the whole manuscript. Conversely, a reproducible PDF does not certify the mathematics.

## Synchronization table

When a manuscript claim is formalized, record the exact correspondence in the Lean branch's `docs/source-alignment.md` and status ledger.

| Manuscript claim | Intended Lean object | Current interpretation |
|---|---|---|
| Fixed-width state space | `BitState` and its cardinality | checked infrastructure |
| Relation composition | `Rel.comp`, list composition, chain semantics | checked infrastructure |
| No path crosses a deleted whole layer | layered-walk cut lemmas | checked support for the halving step |
| Weighted median layer | median-layer existence declaration | checked support for separator rounds |
| Genus monotonicity/additivity | explicitly named external topology declarations unless fully formalized | trust boundary |
| Global planarizing layer set | unconditional end-to-end separator theorem | not yet complete |
| Hansen characterization | exact external theorem in the same circuit model unless fully formalized | not yet stated exactly |
| Common modulus padding | padding family lemmas plus circuit-family construction | partial reduction infrastructure |
| Polylogarithmic relation composition in `AC⁰[m]` | explicit target-circuit construction and bounds | pending |
| Main theorem | concrete theorem from source circuit family to `ACC⁰` | release criterion; not yet proved |

## Merge safety

Files in this package live under `reproducibility/` and do not modify Lean source files or mathematical declarations.

Repository-level documentation may link the two tracks, but progress claims remain separate:

- manuscript reproducibility is recorded on `main`;
- Lean proof status is recorded on `formalization/full-reduction-v1`;
- neither status is silently upgraded by changes in the other track.
