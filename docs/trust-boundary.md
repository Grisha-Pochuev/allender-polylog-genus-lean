# Trust boundary

## What a successful Lean build certifies

A successful build certifies that the declarations currently compiled by Lean follow from:

- Lean's kernel;
- the imported Lean standard library and pinned `mathlib` release;
- any axioms reported by `#print axioms`;
- the definitions and theorem statements actually written in this repository.

For the checked modules currently present, Lean verifies finite-state cardinality, relation algebra, and the elementary whole-layer cut invariant.

## What it does not certify yet

A successful build does **not** currently certify:

- the full statement of Allender's Open Question 3;
- any definition of graph genus or surface embedding;
- the median-layer planarization theorem;
- Hansen's planar characterization;
- a formal definition of `ACC⁰`;
- the end-to-end simulation from source circuits to `ACC⁰`.

The interfaces in `Allender/Interfaces` are specifications of future work. Constructing a value of an interface by assumption would not prove the underlying mathematics.

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
3. Lean's independent environment checker through `lean-action`.

CI protects reproducibility but cannot detect a theorem that has been formalized with the wrong definitions. Definitions must therefore be compared carefully with the cited papers.

## AI assistance

AI-generated Lean code is not trusted merely because it looks plausible. It enters the checked base only when the pinned Lean kernel accepts it. AI-generated mathematical statements must also be reviewed for fidelity to the intended problem; Lean proves the written statement, not the statement an author intended to write.
