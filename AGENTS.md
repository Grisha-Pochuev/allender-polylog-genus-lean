# AGENTS.md

Instructions for humans and coding agents working in this repository.

## Mission

Maintain and independently review the Lean 4 formalization of the candidate
proof strategy for Eric Allender's polylogarithmic-genus constant-width circuit
problem. Correctness and explicit scope are more important than apparent
progress.

## Non-negotiable rules

1. Do not introduce `sorry`, `admit`, `by_contra!` placeholders disguised as axioms, or `unsafe` proof shortcuts.
2. Do not state that Open Question 3 is solved unless an end-to-end theorem with the intended definitions exists and its axiom audit is clean.
3. Do not replace graph genus, planarity, `ACC⁰`, or circuit semantics with an unconstrained proposition and then call the result a formalization.
4. Abstract interfaces are allowed only when their status is clearly marked as conditional and every field appears in `STATUS.md`.
5. Keep Lean and `mathlib` pinned. Dependency updates require a successful clean build.
6. Every mathematical lemma from the prose proof should receive a stable declaration name and a documentation comment.
7. Prefer small reusable lemmas over long tactic scripts.
8. Use explicit constants in asymptotic bounds whenever practical.
9. Preserve the distinction between directed circuit semantics and the underlying undirected graph used for topology.
10. Never reuse the invalid handle-ordering assertion identified in the 2005 proof.

## Required validation before committing

```bash
bash scripts/verify-lean.sh
```

Also verify that no placeholders were introduced:

```bash
! grep -R -n -E '\b(sorry|admit)\b' --include='*.lean' Allender Allender.lean
```

For central theorems, add a `#print axioms` line to `Allender/AxiomAudit.lean`.

## File ownership

- `Allender/FiniteState.lean`: constant-width states only.
- `Allender/Relation.lean`: abstract relation algebra and finite transition semantics.
- `Allender/LayeredGraph.lean`: graph layering and whole-layer cuts, no topology assumptions.
- `Allender/Interfaces/Topology.lean`: temporary exact boundary for genus/planarity work.
- `Allender/Interfaces/Complexity.lean`: quantitative family profiles until concrete circuit syntax replaces them.
- future `Allender/Topology/*`: genuine surface embedding and genus results.
- future `Allender/Circuit/*`: circuit syntax, evaluation, width, size, and `ACC⁰`.

## Preferred next tasks

1. Obtain independent expert review of the prose-to-Lean alignment.
2. Replace the five exact orientable-genus declarations with library-backed
   proofs when suitable graph-embedding infrastructure becomes available.
3. Formalize the cited forward direction of Hansen's theorem from its published
   proof, without weakening its hypotheses or conclusion.
4. Keep the final theorem, status ledger, review guide, and workflow result in
   agreement after every change.

## Documentation discipline

Whenever a status changes:

- update `STATUS.md`;
- check the corresponding item in `docs/proof-obligations.md`;
- update the README table if the project-level status changes;
- explain whether the result is unconditional, library-dependent, or interface-dependent.
