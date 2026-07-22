import AlbertAlgebra.Basic
import AlbertAlgebra.GlenniePolynomial
import Mathlib.Algebra.Jordan.Basic
import Mathlib.Algebra.Symmetrized

/-!
# Public statements

The principal results are stated without importing their proofs.
-/

noncomputable section

namespace Albert.Statement

universe u

/-- The Jordan identity for the symmetrized product on `H3Octonion`. -/
def jordanIdentity : Prop :=
  ∀ x y : H3Octonion, (x * x * y) * x = (x * x) * (y * x)

/-- Existence of an Albert algebra counterexample to Glennie's identity. -/
def glennieViolation : Prop :=
  ∃ x y z : H3Octonion,
    Glennie.glennieLeft x y z ≠ Glennie.glennieRight x y z

/-- Nonexistence of a faithful special realization of the Albert algebra. -/
def nonSpeciality : Prop :=
  ∀ (A : Type u) [Ring A] [Algebra ℝ A] [Invertible (2 : A)]
      (f : H3Octonion →ₗ[ℝ] Aˢʸᵐ),
    (∀ x y, f (x * y) = f x * f y) → ¬ Function.Injective f

end Albert.Statement
