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
| Singleton bad transitions plus maximal good runs give at most `4|J|+1` blocks | `macroblock_count_le_of_cuts` |
| A concrete chain of macroblock tags can be constructed | `macroblockTags`, `macroblock_isChain` |
| Adjacent macroblocks are separated correctly | `macroblocks_separated` |

Still missing: extraction of complete macroblock subcircuits from a concrete circuit and proof that every good block graph is a subgraph of the planarized remainder.

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

Still missing: connecting the macroblock partition from Section 4 to concrete segment relations for every good and bad block.

## Section 6 — Simultaneous Hansen simulation

| Manuscript step | Lean declaration |
|---|---|
| Concrete gates and layered circuits for `AC⁰[m]` | `ACCGate`, `ACmCircuit` |
| Fixed-modulus families, constant depth, and polynomial size | `ACmFamily`, `InACm`, `InACC0` |
| Padded length `N(n,t)=n^(d+2)+t` | `paddedLength` |
| Gaps between adjacent ranges dominate `n^d` | `padding_gap` |
| Valid padded ranges for distinct `n` are disjoint | `paddedLength_injective_on_ranges` |

Still missing:

1. an exact formal statement of Hansen's theorem using, or explicitly converting to, these circuit definitions;
2. construction of the padded single family of planar block-output circuits;
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
2. an edgeless finite graph has genus zero;
3. Battle–Harary–Kodama–Youngs additivity of genus;
4. Hansen's constant-width planar characterization of `ACC⁰`.

The first three are now isolated as four exact named declarations (`genus`,
`genus_mono`, `genus_bot`, and `genus_eq_sum_components`) in
`OrientableGenus.lean`. Hansen's result still needs an exact model-compatible
Lean statement. Any theorem using these results must expose them in
`#print axioms` until they are formalized internally.
