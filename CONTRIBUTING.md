# Contributing

Contributions should preserve the mathematical statement, the explicit proof
architecture, and the repository's small dependency surface.

## Proof policy

- Do not add `sorry`, `admit`, custom axioms, unsafe declarations, opaque proof
  replacements, or native-code trust shortcuts.
- State hypotheses explicitly and avoid definitions that encode their intended
  conclusions.
- Keep declarations in the narrowest relevant module.
- Add comments only when they clarify mathematical structure or a genuinely
  non-obvious proof step.
- Keep the build free of Lean linter warnings.

## Verification

Run the complete verification procedure before opening a pull request:

```bash
./scripts/verify.sh
```

New endpoint theorems should be added to `Verification/Axioms.lean` and to the
expected axiom list in `scripts/verify.sh`.

Changes to comparator endpoints must update `AlbertAlgebraStatement.lean`,
`AlbertAlgebraVerification.lean`, `Verification/comparator.json`, and the
generated challenge in `scripts/run-comparator.sh` together.
