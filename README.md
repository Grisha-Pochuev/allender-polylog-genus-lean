# Allender polylogarithmic-genus problem — Lean formalization

This private repository develops a Lean 4 formalization of the proof candidate in:

> **Polylogarithmic Genus Does Not Increase the Power of Constant-Width Polynomial-Size Circuits — A Separator-Based Candidate Proof**

The target is Eric Allender's US $1000 open question: whether every language accepted by a nonuniform family of polynomial-size, constant-width Boolean circuits of polylogarithmic orientable genus belongs to `ACC⁰`.

## Verified status

The source-aligned formalization branch is:

```text
formalization/full-reduction-v1
```

Latest fully verified code commit:

```text
443db2186476346f91f4af8f66f47aa39fe4dcb6
```

Successful workflow run:

```text
31116859409
```

The run used Lean 4.32.2 and mathlib 4.32.2 and performed:

- rejection of `sorry` and `admit`;
- `lake build` over every imported module;
- compilation of `Allender/AxiomAudit.lean`;
- independent replay with `leanchecker Allender`.

Documentation-only commits after the verified code commit do not alter the checked Lean declarations.

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
| Initial component coverage plus local preservation yields coverage at every round | checked |
| Covered nonplanar components disappear after `log₂ N+1` rounds | checked conditionally |
| At most two bad transitions per cut layer and at most `4|J|+1` macroblocks | checked |
| Concrete syntax and semantics for `AC⁰[m]` and `ACC⁰` | checked |
| Polynomial count of intermediate state assignments | checked |
| Disjoint padded input-length ranges used in Lemma 6.1 | checked |

See [`STATUS.md`](STATUS.md) and [`docs/source-alignment.md`](docs/source-alignment.md) for declaration-level correspondence and the exact remaining obligations.

## Important limitation of the new planarization result

`Allender/CertifiedPlanarization.lean` proves a **conditional planarization bridge**.

It verifies that, once one supplies:

1. an initial injection from the actual nonplanar connected components to the active components of the median-cut process; and
2. a one-round theorem preserving that injection after the next cuts,

then after `log₂ N+1` rounds the actual remainder is planar and at most `g(log₂ N+1)` distinct layers have been deleted.

This does not assume the final planarization statement as an axiom. However, the canonical construction of those active components, parents, and coverage maps from every actual remainder graph is still missing. Therefore the unconditional layer-planarization lemma from the manuscript has **not yet been formalized**.

## What is not yet a complete Lean proof

The final bounty theorem is **not yet formalized**. The main remaining obligations are:

1. construct the canonical separation process from the actual nonplanar components of every remainder and prove initial and one-step coverage;
2. extract concrete macroblock subcircuits and prove every good block is planar;
3. state Hansen's theorem exactly in the same circuit model, or prove an explicit conversion theorem;
4. construct the common-modulus simulations of all planar blocks;
5. construct the constant-depth `AC⁰[m]` circuits for polylogarithmic relation composition and prove depth/size bounds;
6. combine all parts into the final theorem `allender_main`.

A green build certifies only the declarations listed in the axiom audit. It does not by itself establish the $1000 result.

## Exact external boundary

`Allender/OrientableGenus.lean` contains exactly three external declarations:

- `genus` — ordinary orientable graph genus;
- `genus_mono` — monotonicity under taking a spanning subgraph;
- `genus_eq_sum_components` — Battle–Harary–Kodama–Youngs additivity.

No separator, planarization, circuit-simulation, or Allender conclusion is assumed there. Hansen's theorem has not yet been added as an exact Lean declaration.

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
  MedianExistence.lean         weighted median layer existence
  ComponentChain.lean          logarithmic termination of descendants
  ComponentRounds.lean         global numerical round argument
  LayerSeparationProcess.lean  median-cut processes on connected sets
  CertifiedPlanarization.lean  conditional global planarization bridge
  Halving.lean                 numerical halving core
  GenusBudget.lean             additive positive-cost counting
  MacroblockCounting.lean      bad-transition and block bounds
  MacroblockPartition.lean     concrete macroblock tag chains
  StateEnumeration.lean        polynomial state enumeration
  Padding.lean                 common-family input-length padding
  AxiomAudit.lean              trusted-dependency report
```

## Build locally

Install `elan`, then run:

```bash
lake update
lake exe cache get
lake build
lake env lean Allender/AxiomAudit.lean
lake env leanchecker Allender
```

The toolchain and mathlib revision are pinned.

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
