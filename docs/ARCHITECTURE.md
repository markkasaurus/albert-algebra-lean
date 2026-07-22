# Architecture

The development follows the mathematical dependency order.

```text
Octonion
  |
  +-- OctonionIdentities
  |         |
  +-- Basic-+
            |
            +-- JordanIdentity -- Coordinates -- CoordinateProduct
                                                    |
GlenniePolynomial -- GlennieIdentity ---------------+
          |                                         |
          +-- AlbertAlgebraStatement            GlennieWitness
                                                    |
                                                NonSpecial
                                                    |
                                      AlbertAlgebraVerification
```

## Algebraic foundation

`Octonion.lean` defines the real octonions by Cayley-Dickson doubling of the
real quaternions. `OctonionIdentities.lean` proves the scalar, conjugation,
alternativity, Moufang, and inner-product identities used later.

`Basic.lean` defines `H3Octonion` as the submodule of Hermitian matrices and
defines its multiplication by symmetrization.

## Jordan identity

`JordanIdentity.lean` reduces the matrix Jordan identity to finite sums of
octonion associators. Hermitian matrices are split into diagonal and
off-diagonal components; the latter are decomposed into rank-one terms. The
remaining associator sums are discharged using alternativity, polarized
Moufang identities, conjugation, and explicit analysis of the three matrix
indices.

## Coordinate computation

`Coordinates.lean` constructs a linear equivalence between Hermitian matrices
and three real plus three octonion coordinates. `CoordinateProduct.lean` proves
the exact product formula in those coordinates. The Glennie witness uses this
proved equivalence rather than an unverified computational model.

## Non-speciality

`GlenniePolynomial.lean` contains the proof-free polynomial definitions.
`GlennieIdentity.lean` proves the degree-eight identity in arbitrary associative
real algebras under symmetrization. `GlennieWitness.lean` evaluates both sides
on three explicit Albert algebra elements and proves that a coordinate differs.
`NonSpecial.lean` transports this contradiction through a hypothetical
injective product-preserving linear map.

## Verification boundary

`AlbertAlgebraStatement.lean` imports the basic algebra and proof-free Glennie
polynomials, but no endpoint proof. `AlbertAlgebraVerification.lean` supplies
the three declarations exported by the independent comparator.
