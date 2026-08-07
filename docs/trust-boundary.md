# Trust boundary

## What a successful Lean build certifies

A successful build certifies that the declarations currently compiled by Lean follow from:

- Lean's kernel;
- the imported Lean standard library and pinned `mathlib` release;
- any axioms reported by `#print axioms`;
- the definitions and theorem statements actually written in this repository.

For the checked modules currently present, Lean verifies the concrete source
circuit semantics, finite-state relations, the canonical median-layer
recursion, and the layer-planarization conclusion relative to the named genus
declarations.  It also verifies the numerical macroblock, padding, and state
enumeration lemmas, the exact semantic macroblock decomposition, and planar
standalone good-block circuits listed in `STATUS.md`.

## What it does not certify yet

A successful build does **not** currently certify:

- the full statement of Allender's Open Question 3;
- any definition of graph genus or surface embedding;
- an internal proof of Hansen's planar characterization (it is one exact named external theorem);
- the end-to-end simulation from source circuits to `ACC⁰`.

`ACC⁰` has a concrete syntax and family definition in `Allender/ACC0Gate.lean`
and `Allender/ACC0Circuit.lean`; what remains missing is the circuit construction
that realizes the final simulation.  Supplying an arbitrary interface value or
an assumption with the desired conclusion would not prove that construction.

The topology boundary consists of `genus`, `genus_mono`, `genus_map`,
`genus_bot`, and `genus_eq_sum_components`.  The separate complexity boundary
consists only of `Hansen.planar_constantWidth_polySize_to_ACC0`, stated for the
concrete `CircuitFamily` and `InACC0` definitions.

## Axioms

The project forbids `sorry` and `admit`. Abstract mathematical dependencies must be handled in one of three ways:

1. proved in this repository;
2. imported from a trusted library;
3. stated as a named, documented external assumption in a clearly isolated module.

The third option is useful for checking a conditional reduction, but any theorem depending on such an assumption must be described as conditional.

## Continuous integration

GitHub Actions performs:

1. a source scan rejecting `sorry` and `admit`;
2. `lake build` using the pinned Lean and `mathlib` versions;
3. compilation of the central axiom audit;
4. Lean's independent environment checker, run sequentially per project module
   to avoid making memory exhaustion look like a proof failure.

CI protects reproducibility but cannot detect a theorem that has been formalized with the wrong definitions. Definitions must therefore be compared carefully with the cited papers.

## AI assistance

AI-generated Lean code is not trusted merely because it looks plausible. It enters the checked base only when the pinned Lean kernel accepts it. AI-generated mathematical statements must also be reviewed for fidelity to the intended problem; Lean proves the written statement, not the statement an author intended to write.
