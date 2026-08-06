# Allender polylogarithmic-genus problem — Lean formalization

This private repository develops a Lean 4 formalization of the proof candidate in:

> **Polylogarithmic Genus Does Not Increase the Power of Constant-Width Polynomial-Size Circuits — A Separator-Based Candidate Proof**

The target is Eric Allender's US $1000 open question: whether every language accepted by a nonuniform family of polynomial-size, constant-width Boolean circuits of polylogarithmic orientable genus belongs to `ACC⁰`.

## Verified status

The source-aligned formalization branch is:

```text
formalization/full-reduction-v1
```

Verification run **31070265777** completed successfully with Lean 4.32.2 and mathlib 4.32.2. It performed:

- rejection of `sorry` and `admit`;
- `lake build` over every imported module;
- compilation of `Allender/AxiomAudit.lean`;
- independent replay with `leanchecker Allender`.

The old placeholder interfaces, including the arbitrary `CircuitFamily.accepts` field and an assumed layer-planarization structure field, were deleted. The current circuit family is computed by concrete layers and gates.

## What Lean currently verifies

| Manuscript component | Lean coverage |
|---|---|
| Fixed width state space `Q = {0,1}^w` and `|Q| = 2^w` | checked |
| Concrete gates, circuit layers, circuit evaluation, and circuit families | checked |
| Concrete layered dependency graph of a circuit | checked |
| Sequential transition relations and witness chains | checked |
| Underlying undirected simple graph | checked |
| A surviving path cannot cross a deleted whole layer | checked |
| Existence of a weighted median layer in a finite component | checked |
| Every connected descendant after a median cut has at most half the vertices | checked |
| A descendant chain cannot survive `log₂ N + 1` rounds | checked |
| Positive-component genus-budget counting consequence | checked abstractly |
| At most two bad transitions per cut layer and at most `4|J|+1` macroblocks | checked |
| Polynomial count of intermediate state assignments | checked |
| Disjoint padded input-length ranges used in Lemma 6.1 | checked |

See [`docs/source-alignment.md`](docs/source-alignment.md) for declaration-level correspondence.

## What is not yet a complete Lean proof

The final bounty theorem is **not yet formalized**. The remaining major obligations are:

1. formal orientable graph genus and the Battle–Harary–Kodama–Youngs additivity theorem, or an exact audited external theorem boundary;
2. the global recursive construction of all cut layers and the theorem that the final graph is planar;
3. formal planarity of every good macroblock and exact transition semantics at all boundaries;
4. a concrete `AC⁰[m]`/`ACC⁰` circuit model with depth and size accounting;
5. an exact formal statement of Hansen's planar constant-width characterization;
6. the simultaneous common-modulus simulation and the end-to-end main theorem.

A green build certifies only the declarations listed in the axiom audit. It does not by itself establish the $1000 result.

## Repository layout

```text
Allender/
  FiniteState.lean          fixed-width Boolean states
  Gate.lean                 source gate basis
  CircuitLayer.lean         one deterministic layer transition
  Circuit.lean              layered circuit evaluation
  CircuitFamily.lean        concrete nonuniform families
  CircuitGraph.lean         circuit dependency graph
  Relation.lean             relation algebra
  RelationChain.lean        explicit intermediate-state witnesses
  LayeredGraph.lean         layered directed graphs and cuts
  LayeredWalk.lean          undirected paths and layer separation
  SimpleGraph.lean          underlying undirected simple graph
  FiniteComponent.lean      connected sets and descendant halves
  MedianExistence.lean      weighted median layer existence
  ComponentChain.lean       logarithmic termination of descendants
  Halving.lean              numerical halving core
  GenusBudget.lean          additive positive-cost counting
  MacroblockCounting.lean   bad-transition and block bounds
  StateEnumeration.lean     polynomial state enumeration
  Padding.lean              common-family input-length padding
  AxiomAudit.lean           trusted-dependency report
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
- every source claim must map to named Lean declarations;
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
