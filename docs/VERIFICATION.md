# Verification

## Reproducible environment

The repository pins Lean 4.26.0 in `lean-toolchain` and Mathlib 4.26.0 in
`lakefile.lean`. `lake-manifest.json` fixes the complete dependency graph.

From a fresh checkout:

```bash
./scripts/verify.sh
```

## Checks

The verification script performs eight checks:

1. Build every library root and reject warnings or errors.
2. Apply Mathlib's source-style linter to every Lean module.
3. Print and compare the axiom dependencies of the principal endpoint theorems.
4. Reject proof placeholders in Lean sources.
5. Reject declaration forms that bypass ordinary kernel-checked proof terms.
6. Reject scratch, backup, archive, and temporary development artifacts.
7. Restrict imports to Mathlib and modules in this repository.
8. Confirm that the public statement module imports no proof implementation.

The expected endpoint dependencies are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib foundational dependencies. The development has
no project axioms and no `sorryAx` dependency.

Continuous integration runs the same script on every push and pull request to
the main branch.

## Independent comparator

`AlbertAlgebraStatement.lean` states the Jordan identity, existence of a
Glennie violation, and non-speciality without importing their proofs.
`AlbertAlgebraVerification.lean` connects those statements to the completed
development.

The manually triggered workflow `.github/workflows/comparator.yml` generates a
trusted `Challenge.lean` containing only the public theorem types. The pinned
Lean comparator exports and checks the corresponding proof terms from
`AlbertAlgebraVerification.lean`, admits only `propext`, `Quot.sound`, and
`Classical.choice`, and runs the comparison in a pinned `landrun` sandbox on
Linux.

The workflow deliberately avoids compiling the solution before invoking the
comparator. The challenge file is generated on the runner and is never part of
the repository. `scripts/run-comparator.sh` provides the same entry point for a
properly provisioned local environment.

The placeholder bodies in the generated challenge are trusted specification
holes. They are not imported by the solution, and the comparator rejects any
`sorryAx` dependency in the exported solution proof.

An unsandboxed development shim can check configuration and export
compatibility on macOS, but only the Linux run with a functioning `landrun`
satisfies the workflow's adversarial sandbox assumptions.

The comparator is an additional independent audit layer. Lean's kernel build,
the exact axiom audit, and review of the mathematical statements remain
separate requirements.
