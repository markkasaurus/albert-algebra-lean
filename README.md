# The Albert Algebra in Lean 4

[![CI](https://github.com/markkasaurus/albert-algebra-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/markkasaurus/albert-algebra-lean/actions/workflows/ci.yml)
[![Comparator](https://github.com/markkasaurus/albert-algebra-lean/actions/workflows/comparator.yml/badge.svg)](https://github.com/markkasaurus/albert-algebra-lean/actions/workflows/comparator.yml)

This repository formalizes the real Albert algebra as the Hermitian
three-by-three matrices over the octonions. It proves the Jordan identity and
establishes non-speciality by an explicit violation of Glennie's degree-eight
identity.

## Main results

- `Albert.jordan_identity` proves
  `(x * x * y) * x = (x * x) * (y * x)` for all `x y : H3Octonion`.
- `Albert.Coordinates.finrank_eq_twenty_seven` proves that the underlying real
  vector space has dimension 27.
- `Glennie.glennie_identity_in_associative_symmetrization` proves Glennie's
  identity in the symmetrization of every associative real algebra.
- `Albert.GlennieWitness.violates_glennie_identity` gives three explicit sparse
  elements of the Albert algebra for which the two sides differ.
- `Albert.no_faithful_special_embedding` rules out an injective real-linear
  product-preserving map into the symmetrization of an associative real
  algebra.

The formalization introduces no project axioms. The checked endpoint theorems
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Requirements

- Lean 4.26.0
- Mathlib 4.26.0

Both versions are pinned by `lean-toolchain` and `lake-manifest.json`.

## Build and verify

```bash
lake build
./scripts/verify.sh
```

The verification script performs a warning-free build, applies Mathlib's
source-style linter, checks the axiom dependencies of the principal theorems,
scans the Lean sources for proof placeholders and escape hatches, and checks
the import boundary.

The manually triggered comparator workflow independently exports and checks
the Jordan identity, Glennie violation, and non-speciality proof against the
proof-free public statements in `AlbertAlgebraStatement.lean`.

## Organization

- `AlbertAlgebra/Octonion.lean`: real octonions and their algebraic structure.
- `AlbertAlgebra/OctonionIdentities.lean`: alternativity, Moufang identities,
  and inner-product identities.
- `AlbertAlgebra/Basic.lean`: Hermitian matrices and the symmetrized product.
- `AlbertAlgebra/JordanIdentity.lean`: the Jordan identity.
- `AlbertAlgebra/Coordinates.lean`: six-coordinate model and dimension 27.
- `AlbertAlgebra/CoordinateProduct.lean`: coordinate formula for the product.
- `AlbertAlgebra/GlenniePolynomial.lean`: proof-free degree-eight polynomial
  definitions.
- `AlbertAlgebra/GlennieIdentity.lean`: Glennie's identity in associative
  symmetrizations.
- `AlbertAlgebra/GlennieWitness.lean`: explicit counterexample in the Albert
  algebra.
- `AlbertAlgebra/NonSpecial.lean`: the non-speciality theorem.
- `AlbertAlgebraStatement.lean`: public theorem statements.
- `AlbertAlgebraVerification.lean`: comparator entry points.

Further details are in [Theorems](docs/THEOREMS.md),
[Architecture](docs/ARCHITECTURE.md), and
[Verification](docs/VERIFICATION.md). Historical sources for the mathematical
statements are listed in [References](docs/REFERENCES.md).

## License

Apache License 2.0. See [LICENSE](LICENSE).
