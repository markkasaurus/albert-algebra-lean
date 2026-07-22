# Principal Theorems

## The Albert algebra

`H3Octonion` is the real vector space of Hermitian `3 x 3` octonion matrices.
Its multiplication is the symmetrized matrix product

```text
x * y = (1/2) (xy + yx).
```

The matrix product on the right is not assumed associative because octonion
multiplication is nonassociative.

The main theorem is:

```lean
theorem Albert.jordan_identity (x : H3Octonion) :
    ∀ y : H3Octonion, (x * x * y) * x = (x * x) * (y * x)
```

Together with commutativity and distributivity, this supplies the Mathlib
instance:

```lean
instance : IsCommJordan H3Octonion
```

The six independent Hermitian coordinates give a real-linear equivalence

```lean
Albert.Coordinates.coordinateEquiv :
  ((Fin 3 → Real) × (Fin 3 → Octonion)) ≃ₗ[Real] H3Octonion
```

and the dimension theorem:

```lean
theorem Albert.Coordinates.finrank_eq_twenty_seven :
    Module.finrank Real H3Octonion = 27
```

## Glennie's identity

`Glennie.glennieLeft` and `Glennie.glennieRight` define the two degree-eight
polynomials. For every associative real algebra, the symmetrized product
satisfies:

```lean
variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem Glennie.glennie_identity_in_associative_symmetrization
    (x y z : A) :
    associativeGlennieLeft x y z = associativeGlennieRight x y z
```

The elements `glennieX`, `glennieY`, and `glennieZ` are explicit sparse Albert
algebra elements. Exact coordinate evaluation proves:

```lean
theorem Albert.GlennieWitness.violates_glennie_identity :
    glennieLeft glennieX glennieY glennieZ ≠
      glennieRight glennieX glennieY glennieZ
```

The `imK` coordinate of the first off-diagonal octonion is `1` on the left and
`-1` on the right.

## Non-speciality

The Glennie witness yields the final obstruction:

```lean
variable {A : Type*} [Ring A] [Algebra ℝ A] [Invertible (2 : A)]

theorem Albert.no_faithful_special_embedding
    (f : H3Octonion →ₗ[Real] Aˢʸᵐ)
    (hmul : ∀ x y, f (x * y) = f x * f y) :
    ¬ Function.Injective f
```

Thus no real-linear Jordan embedding of the Albert algebra into the
symmetrization of an associative real algebra can be faithful.

See [References](REFERENCES.md) for the original papers defining the Jordan
framework, the exceptional algebra, and the degree-eight special identity.
