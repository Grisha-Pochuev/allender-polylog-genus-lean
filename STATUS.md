# Formalization status

This is the authoritative status ledger for the Lean formalization.  The
currently checked continuation branch is
`formalization/canonical-components-v2`, based on
`formalization/full-reduction-v1`.  The project-wide status and the
human-review reproducibility package are maintained on `main`.

The manuscript package and this ledger answer different questions:

- `main/reproducibility/` records whether the prose artifact can be rebuilt and reviewed;
- this file records exactly what Lean checks, what is conditional, what is external, and what remains pending.

Last locally fully verified code commit: `9bb31c4`
Earlier successful workflow baseline: `31116859409`
Toolchain: Lean 4.32.2, mathlib 4.32.2

The end-to-end theorem at `9bb31c4` passed a local clean `lake build`, the
complete axiom audit, and a memory-bounded sequential `leanchecker` replay of
every project module. A fresh GitHub Actions run is still required before the
earlier server baseline can be replaced.

The successful workflow rejected `sorry`/`admit`, ran `lake build`, compiled
`Allender/AxiomAudit.lean`, and replayed the environment with `leanchecker`.

Documentation and branch-synchronization commits after the verified code commit do not upgrade the machine-checked claim. A new code claim requires a fresh complete verification run.

## Status labels

- **checked** — built without `sorry`/`admit`, included in the root module, audited, and replayed by `leanchecker`.
- **conditional** — Lean proves the stated implication from an explicit mathematical proof obligation that has not yet been constructed.
- **partial** — a mathematically relevant core is checked, but the manuscript statement is not yet represented end to end.
- **external** — an exact named trust boundary for a published result; it is visible in `#print axioms` and is not being presented as proved in this repository.
- **pending** — not yet represented adequately in Lean.

## Source-aligned ledger

| ID | Item | Lean declaration/file | Status |
|---|---|---|---|
| C1 | Boolean gate basis and evaluation | `Gate.eval` | checked |
| C2 | Deterministic layer transition | `CircuitLayer.transition_functional` | checked |
| C3 | Concrete circuit and family evaluation | `Circuit.eval`, `CircuitFamily.language` | checked |
| C4 | Circuit dependency graph and size | `Circuit.layeredGraph`, `Circuit.size_eq_card_vertex` | checked |
| S1 | Fixed state space and cardinality | `BitState.card` | checked |
| R1 | Relation composition and associativity | `Rel.comp_assoc`, `Rel.composeList_append` | checked |
| R2 | Explicit intermediate-state witness semantics | `Rel.chain_iff_composeList` | checked |
| G1 | Layered graph and whole-layer cuts | `LayeredGraph.lean` | checked |
| G2 | No surviving path crosses a deleted layer | `no_surviving_walk_across_layer` | checked |
| G3 | Underlying undirected simple graph | `toSimpleGraph` | checked |
| G4 | Decidable adjacency for a graph after whole-layer deletion | `instDecidableRelDeleteLayersToSimpleGraph` | checked |
| M1 | Existence of weighted median layer | `exists_medianLayer` | checked |
| M2 | Each connected descendant halves | `DescendantAfterCut.card_halves` | checked |
| M3 | Descendant chain terminates after logarithmically many rounds | `DescendantChain.impossible_after_log` | checked |
| T1 | Positive-cost components are bounded by the total budget | `card_le_of_positive_cost_sum_le` | checked |
| T2 | Total selected layers over bounded rounds | `separator_round_count_bound` | checked |
| T3 | Orientable genus symbol, monotonicity, relabelling invariance, and edgeless base case | `OrientableGenus.genus`, `genus_mono`, `genus_map`, `genus_bot` | external |
| T4 | Genus additivity over components | `genus_eq_sum_components` (Battle–Harary–Kodama–Youngs) | external |
| T4a | Number of nonplanar components is at most genus | `nonplanarComponents_card_le_genus` | checked relative to T3–T4 |
| T4b | Planarity iff no component has positive genus | `isPlanar_iff_nonplanarComponents_eq_empty` | checked relative to T3–T4 |
| T4c | Deleting layers cannot increase genus | `genus_deleteLayers_le` | checked relative to T3 |
| T5a | Accumulated cut layers and bound `|J_t| ≤ g t` | `cumulativeCuts`, `cumulativeCuts_card_le_mul` | checked |
| T5b | One-round representation of actual nonplanar components by active components | `RoundCoverage`, `nonplanar_card_le_active_card` | checked as an implication from explicit representation data |
| T5c | Iteration of initial and stepwise coverage | `PlanarizationCoverage.coverageAt` | checked |
| T5d | Planarity after `log₂ N + 1` covered rounds | `final_isPlanar_of_coverage` | conditional on `PlanarizationCoverage`, relative to T3–T4 |
| T5e | Canonical construction from the actual nonplanar components of every remainder | `canonicalLayerSeparationProcess`, `canonicalParent_active`, `canonicalChild_subset`, `canonicalChild_avoids` | checked relative to T3–T4 |
| T5f | Unconditional layer-planarization conclusion `|J| ≤ g(log₂ N+1)` | `exists_planarizing_layer_set` | checked relative to T3–T4 |
| B1 | Bad-transition bound | `card_badTransitions_le` | checked |
| B2 | Canonical macroblock partition and actual bound `≤ 4|J|+1` | `macroblockTags`, `macroblockTags_length_le_of_cuts` | checked |
| B3 | Canonical block layers concatenate to the exact circuit tail | `flatten_canonicalMacroblockLayers_eq_tail` | checked |
| B4 | Exact acceptance decomposition through canonical block relations | `compose_macroblockRelations_eq_tailSegment`, `accept_cons_iff_macroblockRelations` | checked |
| B5 | Every good block dependency graph is planar when the cut remainder is planar | `macroblockGraph_toSimpleGraph_le_deleteLayers`, `goodMacroblock_isPlanar` | checked relative to T3 |
| B6 | Standalone `(n+w)`-input circuit for each block has exact semantics and size | `macroblockCircuit_eval`, `macroblockCircuit_size` | checked |
| B7 | Every good standalone block circuit is planar; combined cut/block certificate exists | `macroblockCircuit_graph_map_le`, `macroblockCircuit_isPlanar`, `exists_planarizingCuts_with_planar_good_macroblocks` | checked relative to T3–T4 |
| H1 | Hansen forward theorem for concrete planar `CircuitFamily` and concrete `InACC0` | `Hansen.planar_constantWidth_polySize_to_ACC0` | external, exact named published dependency |
| H2 | Common-family padding ranges | `padding_gap`, `paddedLength_injective_on_ranges` | checked |
| P1 | Polynomial number of intermediate state assignments | `card_stateAssignments_log_le` | checked |
| P2 | Explicit relation-chain semantics | `RelationChain.lean` | checked |
| P3 | Constant-depth multi-round relation composition and size accounting | `collapseRounds`, `roundedAcceptanceCircuit_depth_le`, `roundedAcceptanceCircuit_size_le` | checked |
| P4 | Polynomial closure of all numerical size recurrences | `roundsSizeBound_polynomial`, `finalAcceptanceSizeBound_polynomial` | checked |
| F1 | End-to-end theorem: source family lies in `ACC⁰` | `allender_polylog_genus_in_ACC0` | checked relative to T3–T4 and H1 |

## Exact topology trust boundary

`Allender/OrientableGenus.lean` contains exactly five external declarations:

1. `genus` — the ordinary orientable genus as a natural-valued graph invariant;
2. `genus_mono` — monotonicity under taking a spanning subgraph;
3. `genus_map` — invariance under injective vertex relabelling and added isolates;
4. `genus_bot` — an edgeless finite graph has genus zero;
5. `genus_eq_sum_components` — Battle–Harary–Kodama–Youngs additivity over connected components.

`Allender/Hansen.lean` contains one additional external declaration: the
forward, family-level direction of Hansen's Theorem 1.  Its hypotheses use the
concrete source-family graph and polynomial-size definitions, and its
conclusion is the concrete `InACC0` predicate.  No per-block simulator is
postulated.

No separator theorem, planarization theorem, circuit theorem, or final Allender
conclusion is assumed. The finset `components G` fixes one enumeration of
connected components so that all sums use the same data rather than relying on
potentially different `Fintype` instances.

The derived topology lemmas are listed in `Allender/AxiomAudit.lean`. Their
`#print axioms` output exposes the named external declarations above and does
not contain `sorryAx`.

## Completed separator construction

`Allender/CanonicalComponents.lean` and
`Allender/CanonicalPlanarization.lean` instantiate the earlier abstract
recursion with the actual connected components of every graph remainder.

Lean has checked, relative only to the four topology declarations above, that:

1. at most `g` median layers are added per valid round;
2. the cumulative number of distinct cuts after `t` rounds is at most `g * t`;
3. the active identifiers are exactly the finite supports of actual nonplanar
   components;
4. every active next-round component has a nonplanar parent, is contained in
   it, and avoids its newly deleted median layer;
5. after `log₂ N + 1` rounds no nonplanar component remains;
6. `exists_planarizing_layer_set` supplies an actual set of at most
   `g * (log₂ N + 1)` whole layers whose deletion leaves a planar graph.

The earlier conditional `PlanarizationCoverage` API remains useful generic
infrastructure, but it is no longer the trust boundary for Lemma 3.1.

## Removed material

The following earlier placeholders were deleted and must not be cited as verification:

- the structure with arbitrary `CircuitFamily.accepts` unrelated to a circuit;
- the `TopologyInterface` whose main planarization statement was merely a field;
- obsolete proof-obligation and planning documents referring to those interfaces.

## Verification result

The repository now meets the previously stated end-to-end release criterion:

1. a concrete final theorem quantifies over the source circuit family defined here;
2. the target is a concrete `ACC⁰` definition with fixed modulus/depth and polynomial size;
3. the checked standalone planar block circuits are combined, via the padding construction, into one polynomial-size planar family to which Hansen applies;
4. Hansen and genus additivity are either formalized or isolated as exact published dependencies;
5. `#print axioms` for the final theorem contains no `sorryAx` or undocumented assumption;
6. clean build, axiom audit, and `leanchecker` all pass.

The resulting claim is deliberately qualified as a complete Lean reduction
relative to the exact external genus and Hansen declarations listed above.
