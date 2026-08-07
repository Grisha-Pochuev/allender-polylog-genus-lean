# Contributing

The repository is public and mathematical review is welcome.  This file records
the standard for proposed changes and error reports.

## Before opening a change

- Read `README.md`, `docs/REVIEW_GUIDE.md`, `STATUS.md`, `AGENTS.md`, and
  `docs/trust-boundary.md`.
- Identify the exact proof obligation being addressed.
- Check whether the intended definition agrees with the cited source.
- Avoid mixing refactoring with new mathematics.

## Lean requirements

- The project must build with the pinned toolchain.
- Run `bash scripts/verify-lean.sh` before opening a pull request.
- No `sorry`, `admit`, or undocumented custom axiom is permitted.
- New central lemmas must be added to `Allender/AxiomAudit.lean`.
- Definitions should have docstrings explaining their mathematical role.
- Proofs should avoid unnecessary classical choice when a finite constructive argument is easy.

## Pull request description

A mathematical pull request should state:

1. the formal theorem added;
2. the corresponding prose claim;
3. all external dependencies;
4. what remains unproved;
5. the validation commands run.

## Bug reports

A suspected mathematical error is more important than preserving the current strategy. Open an issue containing the smallest failing statement, the relevant source passage, and whether the problem is in the prose argument, its Lean translation, or the definitions.
