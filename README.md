# Allender polylogarithmic-genus problem — Lean formalization

This branch develops a Lean 4 formalization of the proof candidate in:

> **Polylogarithmic Genus Does Not Increase the Power of Constant-Width Polynomial-Size Circuits — A Separator-Based Candidate Proof**

The target is Eric Allender's US $1000 open question: whether every language accepted by a nonuniform family of polynomial-size, constant-width Boolean circuits of polylogarithmic orientable genus belongs to `ACC⁰`.

## Branch scope and project navigation

The authoritative base branch is:

```text
formalization/full-reduction-v1
```

The currently checked continuation, including the concrete canonical
planarization construction, is `formalization/canonical-components-v2`.

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

Latest earlier successful GitHub workflow baseline:

```text
31116859409
```

The run used Lean 4.32.2 and mathlib 4.32.2 and performed:

- rejection of `sorry` and `admit`;
- `lake build` over every imported module;
- compilation of `Allender/AxiomAudit.lean`;
- independent replay with `leanchecker Allender`.

Documentation-only commits after the verified code commit do not alter the checked Lean declarations.

The complete end-to-end theorem through commit `9bb31c4` has passed locally:

- a complete `lake build`;
- compilation of the axiom audit, with no `sorryAx` dependency;
- sequential `leanchecker` replay of every built project module.

Its fresh GitHub Actions result is still pending, so run `31116859409` remains
the earlier server-verified baseline rather than verification of the final theorem.

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
feeds into the final circuit-class inclusion proved in
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
  RelationCompositionRounds.lean checked logarithmic blocking rounds
  PolynomialBounds.lean       explicit polynomial-bound calculus
  AcceptanceCircuit.lean      end-to-end target-circuit construction
  MainTheorem.lean             final `InACC0` theorem
  AxiomAudit.lean              trusted-dependency report
```

## Build locally

Install `elan`, then run:

```bash
lake update
lake exe cache get
lake build
lake env lean Allender/AxiomAudit.lean
for olean in $(find .lake/build/lib/lean/Allender -name '*.olean' | sort); do
  module=${olean#.lake/build/lib/lean/}
  module=${module%.olean}
  lake env leanchecker "${module//\//.}"
done
```

The toolchain and mathlib revision are pinned. The GitHub Lean workflow runs on
the active formalization branch, on relevant pull requests, and by manual
dispatch.  It checks modules sequentially to keep independent replay within
the runner's memory limit.

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
