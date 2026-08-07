# Allender polylogarithmic-genus problem — Lean formalization

This branch develops a Lean 4 formalization of the proof candidate in:

> **Polylogarithmic Genus Does Not Increase the Power of Constant-Width Polynomial-Size Circuits — A Separator-Based Candidate Proof**

The target is Eric Allender's US $1000 open question: whether every language accepted by a nonuniform family of polynomial-size, constant-width Boolean circuits of polylogarithmic orientable genus belongs to `ACC⁰`.

## Start here

For a first review, follow this short route:

1. [`docs/REVIEW_GUIDE.md`](docs/REVIEW_GUIDE.md) — what each part of the
   repository is for and the exact verification command;
2. [`reproducibility/paper/allender_polylog_genus_acc0_proof.tex`](reproducibility/paper/allender_polylog_genus_acc0_proof.tex)
   — the human-readable proof;
3. [`Allender/MainTheorem.lean`](Allender/MainTheorem.lean) — the final Lean
   theorem;
4. [`Allender/AxiomAudit.lean`](Allender/AxiomAudit.lean) — the complete visible
   trust boundary;
5. [`STATUS.md`](STATUS.md) and
   [`docs/source-alignment.md`](docs/source-alignment.md) — exact status and the
   manuscript-to-Lean map.

To reproduce the complete machine check after installing `elan`:

```bash
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

A green run verifies the reduction relative to the named genus facts and
Hansen's published theorem.  It does not claim that those external results
were formalized from first principles in this repository.

## Branch scope and project navigation

The historical base of the current development is:

```text
formalization/full-reduction-v1
```

The authoritative Lean development, including the final theorem, is currently
`formalization/canonical-components-v2` and is reviewed through PR #7.

The human-review manuscript package is maintained on `main` under [`reproducibility/`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/tree/main/reproducibility). It contains the LaTeX manuscript, English synopsis, sources, integrity checks, and reviewer materials.

The two tracks are deliberately separate:

- this branch records what Lean has checked, what remains conditional, and what is external;
- `main/reproducibility/` records whether the prose artifact can be independently rebuilt and reviewed;
- neither track upgrades the status of the other automatically.

After synchronization with `main`, this branch may contain the same `reproducibility/` files for repository-history safety. They remain maintained from `main` and are not part of the Lean proof audit. For the project-wide map, see [`PROJECT_STRUCTURE.md`](PROJECT_STRUCTURE.md).

## Verified status

Latest locally fully verified code commit:

```text
9bb31c4
```

Equivalent final source tree published on GitHub:

```text
37f90d350278a40c360375c7f8731c46a2610ec5
```

Successful complete GitHub verification of that tree:

[`Lean verification #98, run 31135088313`](https://github.com/Grisha-Pochuev/allender-polylog-genus-lean/actions/runs/31135088313)

The run used Lean 4.32.2 and mathlib 4.32.2 and performed:

- rejection of `sorry` and `admit`;
- `lake build` over every imported module;
- compilation of `Allender/AxiomAudit.lean`;
- independent replay with `leanchecker Allender`.

Documentation-only commits after the verified code commit do not alter the checked Lean declarations.

The complete end-to-end theorem through local code commit `9bb31c4` has passed
both locally and in GitHub Actions:

- a complete `lake build`;
- compilation of the axiom audit, with no `sorryAx` dependency;
- sequential `leanchecker` replay of every built project module.

The GitHub copy has a different commit hash because the six locally verified
commits were recreated through GitHub's authenticated Git-data interface.  Its
final tree hash is exactly the local tree hash `4303f39b5462c36b397ea1621bc0ab96f9c42825`;
the mathematical files are byte-for-byte identical.

The old placeholder interfaces, including the arbitrary `CircuitFamily.accepts` field and an assumed layer-planarization structure field, were deleted. The current circuit family is computed by concrete layers and gates.

## What Lean currently verifies

| Manuscript component | Lean coverage |
|---|---|
| Fixed-width state space `Q = {0,1}^w` and `|Q| = 2^w` | checked |
| Concrete gates, circuit layers, circuit evaluation, and circuit families | checked |
| Concrete layered dependency graph of a circuit | checked |
| Sequential transition relations, segments, and boundary predicates | checked |
| Underlying undirected simple graph and whole-layer deletion | checked |
| A surviving path cannot cross a deleted whole layer | checked |
| Existence of a weighted median layer in a finite component | checked |
| Every connected descendant after a median cut has at most half the vertices | checked |
| A descendant chain cannot survive `log₂ N + 1` rounds | checked |
| Orientable genus monotonicity and additivity | exact external declarations |
| At most `g` connected components are nonplanar in a genus-`g` graph | checked relative to the genus declarations |
| Cumulative cut count after `t` rounds is at most `g*t` | checked |
| Actual nonplanar remainder components and their canonical parents | checked relative to the genus declarations |
| Deleting at most `g(log₂ N+1)` whole layers leaves a planar graph | checked relative to the genus declarations |
| Canonical partition into at most `4|J|+1` macroblocks | checked |
| Exact reconstruction of circuit-tail semantics from macroblock relations | checked |
| Every good macroblock dependency graph is planar after the layer cut | checked relative to genus monotonicity |
| A standalone `(n+w)`-input circuit computes each block/output bit exactly | checked |
| Every standalone good-block circuit is planar | checked relative to genus relabelling invariance |
| Concrete syntax and semantics for `AC⁰[m]` and `ACC⁰` | checked |
| Polynomial count of intermediate state assignments | checked |
| Disjoint padded input-length ranges used in Lemma 6.1 | checked |
| Common-modulus simulation of all good macroblocks | checked relative to Hansen |
| Multi-round finite-state relation composition with exact semantics | checked |
| Constant depth and polynomial size of the final target family | checked |
| `PolynomialSize → PolylogGenus → InACC0` | checked relative to the named external boundary |

See [`STATUS.md`](STATUS.md) and [`docs/source-alignment.md`](docs/source-alignment.md) for declaration-level correspondence and the exact trust boundary.

## Scope of the new planarization result

`Allender/CanonicalComponents.lean` identifies the actual nonplanar connected
components of each remainder, and `Allender/CanonicalPlanarization.lean`
constructs their median cuts and canonical parents.  Lean now proves
`exists_planarizing_layer_set`: deleting at most
`g * (log₂ |V| + 1)` whole layers leaves a graph of genus zero.

This result is unconditional inside the graph model, but it deliberately
depends on named external topology declarations: the genus invariant,
monotonicity, relabelling invariance where used by extracted block circuits,
the edgeless base case, and additivity over components.  It does not by itself
feed into the final circuit-class inclusion proved in
`Allender.allender_polylog_genus_in_ACC0`.

## Scope of the final theorem

Lean now constructs one fixed-modulus target family and proves exact
recognition, constant depth, and polynomial padded gate count.  The final
declaration is:

```lean
Allender.allender_polylog_genus_in_ACC0
```

Its hypotheses are the concrete source-family predicates `PolynomialSize` and
`PolylogGenus`; fixed width is part of `CircuitFamily`.  Empty-layer and
zero-input encodings are handled explicitly.  This is a complete formal
reduction relative to the published Hansen theorem and the five named genus
facts below.  It is not a from-first-principles formalization of those external
published results.

## Exact external boundary

`Allender/OrientableGenus.lean` contains exactly five external declarations:

- `genus` — ordinary orientable graph genus;
- `genus_mono` — monotonicity under taking a spanning subgraph;
- `genus_map` — invariance under injective relabelling and added isolates;
- `genus_bot` — genus zero for an edgeless graph;
- `genus_eq_sum_components` — Battle–Harary–Kodama–Youngs additivity.

No separator, planarization, circuit-simulation, or Allender conclusion is
assumed there. `Allender/Hansen.lean` separately isolates the exact
family-level forward direction of Hansen's published theorem; it does not
assume an arbitrary per-block simulator.

## Repository layout

```text
Allender/
  FiniteState.lean             fixed-width Boolean states
  Gate.lean                    source gate basis
  CircuitLayer.lean            one deterministic layer transition
  Circuit.lean                 layered circuit evaluation
  CircuitFamily.lean           concrete nonuniform families
  CircuitGraph.lean            circuit dependency graph
  Relation.lean                relation algebra
  RelationChain.lean           explicit intermediate-state witnesses
  CircuitSegment.lean          concrete segment semantics
  BoundaryPredicates.lean      initial and accepting boundaries
  ACC0Gate.lean                target `AC⁰[m]` gate syntax
  ACC0Circuit.lean             target circuits, families, and `InACC0`
  LayeredGraph.lean            layered directed graphs and cuts
  LayeredWalk.lean             undirected paths and layer separation
  SimpleGraph.lean             underlying undirected simple graph
  LayerDeletion.lean           accumulated whole-layer deletion
  OrientableGenus.lean         exact external genus boundary
  FiniteComponent.lean         connected sets and descendant halves
  ComponentSupport.lean        actual component supports as connected sets
  CanonicalComponents.lean     nonplanar remainder components and parents
  CanonicalPlanarization.lean  unconditional whole-layer planarization
  MedianExistence.lean         weighted median layer existence
  ComponentChain.lean          logarithmic termination of descendants
  ComponentRounds.lean         global numerical round argument
  LayerSeparationProcess.lean  median-cut processes on connected sets
  CertifiedPlanarization.lean  conditional global planarization bridge
  Halving.lean                 numerical halving core
  GenusBudget.lean             additive positive-cost counting
  MacroblockCounting.lean      bad-transition and block bounds
  MacroblockPartition.lean     concrete macroblock tag chains
  MacroblockCircuit.lean       block semantics, count, and planar block graphs
  BlockCircuit.lean            standalone block circuits and planar embedding
  Hansen.lean                  exact external family-level Hansen theorem
  StateEnumeration.lean        polynomial state enumeration
  Padding.lean                 common-family input-length padding
  InputPadding.lean            source padding and target input restriction
  SimultaneousHansen.lean      one common-modulus simulation family
  GoodBlockBatch.lean          polynomial package of planar good blocks
  GoodBlockRelations.lean      exact good-block relation circuits
  BadBlockRelations.lean       finite bad-block relation circuits
  FixedBoundaryCircuit.lean    first/last boundary predicates
  ACC0Closure.lean             explicit target-circuit closure operations
  FiniteRelationComposition.lean finite relation composition circuits
  MacroblockRelationCircuits.lean per-block target relation circuits
  MacroblockCompositionCircuit.lean one-round composition
  RelationCompositionRounds.lean checked logarithmic blocking rounds
  MacroblockCompositionRounds.lean repeated macroblock composition
  PolynomialBounds.lean       explicit polynomial-bound calculus
  AcceptanceCircuit.lean      end-to-end target-circuit construction
  MainTheorem.lean             final `InACC0` theorem
  AxiomAudit.lean              trusted-dependency report
```

## Build locally

Install `elan`, prepare the pinned dependencies, and run the repository's
single verification entry point:

```bash
lake update
lake exe cache get
bash scripts/verify-lean.sh
```

The script rejects proof placeholders, builds the project, compiles the axiom
audit, and independently replays every project module.  The toolchain and
mathlib revision are pinned. The GitHub Lean workflow calls this same script on
the active formalization branch, on relevant pull requests, and by manual
dispatch. It checks modules sequentially to remain within the runner's memory
limit.

## Proof discipline

- no `sorry` or `admit`;
- no arbitrary semantic placeholder may be described as a circuit theorem;
- conditional theorems must name their missing hypotheses explicitly;
- every manuscript claim must map to named Lean declarations;
- external results must be isolated, named, and visible in `#print axioms`;
- the final theorem may be claimed only when its definitions match the manuscript and its axiom audit is explicit.

## Primary references

- Eric Allender, *Parting Thoughts and Parting Shots*, SIGACT News 54(1), 2023.
- Eric Allender, Samir Datta, Sambuddha Roy, *Topology inside NC¹*, CCC 2005 / ECCC TR04-108.
- Kristoffer Arnsfelt Hansen, *Constant Width Planar Computation Characterizes ACC⁰*, Theory of Computing Systems 39, 2006.
- J. Battle, F. Harary, Y. Kodama, J. W. T. Youngs, *Additivity of the Genus of a Graph*, 1962.

## Authorship

Project owner: **Grisha Pochuev**, independent researcher. Initial code and documentation were prepared with AI assistance. Mathematical responsibility remains with the author.

## License

MIT.
