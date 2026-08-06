# Manuscript-to-Lean alignment

Basis: the 12-page proof candidate *Polylogarithmic Genus Does Not Increase the Power of Constant-Width Polynomial-Size Circuits* and its Russian technical notes.

This document records what is genuinely represented in Lean. It must not be read as a claim that the final theorem is already formalized.

## Section 2 — Circuit model and notation

| Manuscript claim | Lean representation |
|---|---|
| Gates are AND, OR, literals, negated literals, and constants | `Allender.Gate` |
| A layer maps one width-`w` state to the next | `CircuitLayer.eval` |
| A layered circuit is a sequence of layers | `Circuit` |
| A nonuniform family contains one concrete circuit per input length | `CircuitFamily` |
| State space is `Q={0,1}^w`, `|Q|=2^w` | `BitState`, `BitState.card` |
| Circuit graph consists of gate positions and consecutive-layer dependencies | `Circuit.Vertex`, `Circuit.layeredGraph` |

The source model pads every layer to the fixed width. Output-location conventions and exact equivalence with Hansen's published model still need a formal conversion theorem.

## Section 3 — Layer planarization lemma

| Manuscript step | Lean declaration |
|---|---|
| Edges go only between consecutive layers | `LayeredDigraph.edge_next` |
| A surviving edge stays in one cut interval | `edge_same_block_of_source_survives` |
| A surviving undirected walk cannot cross a deleted layer | `no_surviving_walk_across_layer` |
| A finite component has a weighted median layer | `FiniteConnectedSet.exists_medianLayer` |
| A connected descendant lies wholly below or above the cut | `DescendantAfterCut.all_below_or_all_above` |
| A descendant has at most half the parent cardinality | `DescendantAfterCut.card_halves` |
| Repeated descendants form a numerical halving chain | `DescendantChain.toHalvingChain` |
| No nonempty descendant survives `log₂ N+1` cuts | `DescendantChain.impossible_after_log` |
| Ordinary orientable genus, monotonicity, and the edgeless base case | external declarations `OrientableGenus.genus`, `genus_mono`, `genus_bot` |
| Genus is additive over connected components | external declaration `genus_eq_sum_components` |
| At most `g` components are nonplanar when total genus is at most `g` | `nonplanarComponents_card_le_genus` |
| Deleting layers cannot increase genus | `genus_deleteLayers_le` |
| At most `g` median layers are selected in one process round | `LayerSeparationProcess.roundCuts_card_le` |
| The cumulative number of distinct cuts after `t` rounds is at most `g*t` | `cumulativeCuts_card_le_mul` |
| Initial coverage plus one-step preservation yields coverage at every round | `PlanarizationCoverage.coverageAt` |
| Covered nonplanar components disappear after `log₂ N+1` rounds | `final_isPlanar_of_coverage` |
| Actual nonplanar components are represented by their finite supports | `activeComponentVerts`, `componentForSupport_mem_nonplanar` |
| Every next-round nonplanar component has a nonplanar canonical parent | `canonicalParent_active` |
| A child is contained in its parent and avoids the new median layer | `canonicalChild_subset`, `canonicalChild_avoids` |
| The actual canonical recursion is a valid separation process | `canonicalLayerSeparationProcess` |
| At most `g(log₂ N+1)` deleted whole layers leave a planar remainder | `exists_planarizing_layer_set` |

The generic `final_isPlanar_of_coverage` theorem remains conditional on explicit
`PlanarizationCoverage` data.  The new canonical construction supplies the
corresponding facts directly for actual remainder components, so
`exists_planarizing_layer_set` is the unconditional manuscript Lemma 3.1 inside
the graph model, relative only to the named orientable-genus declarations.

## Section 4 — Macroblocks

| Manuscript step | Lean declaration |
|---|---|
| A cut layer is incident with at most two bad transitions | `card_badTransitions_le` |
| Singleton bad transitions plus maximal good runs give at most `4|J|+1` blocks | `macroblockTags_length_le_of_cuts` |
| A concrete chain of macroblock tags can be constructed | `macroblockTags`, `macroblock_isChain` |
| Adjacent macroblocks are separated correctly | `macroblocks_separated` |
| Every canonical block is a good run or one bad singleton | `macroblock_good_or_singleton` |
| A good block graph is a subgraph of the planarized remainder | `macroblockGraph_toSimpleGraph_le_deleteLayers` |
| Hence every good block graph is planar | `goodMacroblock_isPlanar` |
| Incoming boundary bits become real extra inputs of a standalone block circuit | `boundaryInputLayer`, `Circuit.macroblockCircuit` |
| Standalone block evaluation and size are exact | `macroblockCircuit_eval`, `macroblockCircuit_size` |
| The standalone graph embeds into the ambient block graph | `macroblockCircuit_graph_map_le` |
| Every standalone good-block circuit is planar | `macroblockCircuit_isPlanar` |

The block extraction itself is now complete. Still missing is combining all
valid block/output pairs across input lengths into the one padded planar family
used for simultaneous Hansen simulation.

## Section 5 — Relations on the state space

| Manuscript step | Lean declaration |
|---|---|
| Binary relations and sequential composition | `Rel.comp` |
| Composition is associative | `Rel.comp_assoc` |
| List composition matches splitting into sublists | `Rel.composeList_append` |
| Explicit intermediate-state witnesses match composition | `Rel.chain_iff_composeList` |
| Concrete segment semantics agrees with evaluation | `segmentRelation_iff_eval`, `segmentRelation_append` |
| Initial and accepting boundary conditions are represented | `initialState_iff_transition`, `accept_cons_iff_exists_boundary_states` |
| Concrete circuit evaluation gives a transition chain | `Circuit.chain_from_zero_to_final` |
| Canonical block layer lists concatenate to the exact circuit tail | `flatten_canonicalMacroblockLayers_eq_tail` |
| Composing all canonical block relations equals the full tail relation | `compose_macroblockRelations_eq_tailSegment` |
| Acceptance has exact initial/block-composition/final semantics | `accept_cons_iff_macroblockRelations` |

The proposition-level macroblock decomposition is checked.  Still missing is
its realization by concrete target `AC⁰[m]` circuits with uniform resource
bounds.

## Section 6 — Simultaneous Hansen simulation

| Manuscript step | Lean declaration |
|---|---|
| Concrete gates and layered circuits for `AC⁰[m]` | `ACCGate`, `ACmCircuit` |
| Fixed-modulus families, constant depth, and polynomial size | `ACmFamily`, `InACm`, `InACC0` |
| Padded length `N(n,t)=n^(d+2)+t` | `paddedLength` |
| Gaps between adjacent ranges dominate `n^d` | `padding_gap` |
| Valid padded ranges for distinct `n` are disjoint | `paddedLength_injective_on_ranges` |

The exact family-level forward theorem is isolated as
`Hansen.planar_constantWidth_polySize_to_ACC0`. Still missing:

1. construction of the padded single family of planar block-output circuits;
2. proof of its polynomial size and planarity at invalid padded lengths;
3. fixing ignored variables in the resulting `AC⁰[m]` circuits;
4. extraction of one common modulus, depth bound, and polynomial size bound.

## Section 7 — Polylogarithmic relation composition

| Manuscript step | Lean declaration |
|---|---|
| Number of assignments to `L` intermediate width-`w` states | `card_stateAssignments` |
| For `L=log₂(n+2)`, this number is polynomial | `card_stateAssignments_log_le` |
| Witness-chain semantics is the OR-over-assignments formula at proposition level | `RelationChain.lean` |

Still missing: concrete unbounded-fan-in AND/OR circuit construction, depth increment of two per round, polynomial size recurrence, and the constant-round collapse for an arbitrary fixed polylogarithmic exponent.

## Section 8 — Main theorem

No final theorem of the form

```lean
theorem allender_main
    (F : CircuitFamily)
    (hsize : F.PolynomialSize)
    (hgenus : ...)
    : InACC0 F.language
```

is present. The root module verifies the source-aligned lemmas and conditional reductions above, not the bounty conclusion.

## External theorem boundary

The manuscript relies on the following external mathematics:

1. orientable graph genus is a natural-valued monotone invariant;
2. injective vertex relabelling and adding isolates preserves genus;
3. an edgeless finite graph has genus zero;
4. Battle–Harary–Kodama–Youngs additivity of genus;
5. Hansen's constant-width planar characterization of `ACC⁰`.

The first three are isolated as five exact named declarations (`genus`,
`genus_mono`, `genus_map`, `genus_bot`, and
`genus_eq_sum_components`) in `OrientableGenus.lean`. Hansen's result is the
single exact declaration in `Hansen.lean`. Any theorem using these results must
expose them in `#print axioms` until they are formalized internally.
