import AlbertAlgebra.GlenniePolynomial

/-!
# Glennie's degree-eight identity in associative symmetrizations

The identity is proved for the symmetrized product of every associative real
algebra and transported along injective product-preserving linear maps.
-/

noncomputable section

namespace Glennie

variable {A : Type*} [Ring A] [Algebra ℝ A]

set_option maxHeartbeats 0 in
theorem associativeJordanTriple_eq (x y z : A) :
    associativeJordanTriple x y z =
      (1 / 2 : ℝ) • (x * y * z + z * y * x) := by
  simp only [associativeJordanTriple, associativeJordanProduct, smul_add,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  module

set_option maxHeartbeats 0 in
theorem glennie_identity_in_associative_symmetrization (x y z : A) :
    associativeGlennieLeft x y z = associativeGlennieRight x y z := by
  simp only [associativeGlennieLeft, associativeGlennieRight,
    associativeJordanTriple_eq, associativeJordanProduct, smul_add,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  module

variable {J : Type*} [NonUnitalNonAssocRing J] [Module ℝ J]

theorem map_jordanTriple (f : J →ₗ[ℝ] A)
    (hmul : ∀ x y, f (x * y) = associativeJordanProduct (f x) (f y))
    (x y z : J) :
    f (jordanTriple x y z) =
      associativeJordanTriple (f x) (f y) (f z) := by
  simp only [jordanTriple, map_add, map_sub, hmul, associativeJordanTriple]

theorem map_glennieLeft (f : J →ₗ[ℝ] A)
    (hmul : ∀ x y, f (x * y) = associativeJordanProduct (f x) (f y))
    (x y z : J) :
    f (glennieLeft x y z) = associativeGlennieLeft (f x) (f y) (f z) := by
  simp only [glennieLeft, map_sub, map_nsmul, map_jordanTriple f hmul,
    hmul, associativeGlennieLeft]

theorem map_glennieRight (f : J →ₗ[ℝ] A)
    (hmul : ∀ x y, f (x * y) = associativeJordanProduct (f x) (f y))
    (x y z : J) :
    f (glennieRight x y z) = associativeGlennieRight (f x) (f y) (f z) := by
  simp only [glennieRight, map_sub, map_nsmul, map_jordanTriple f hmul,
    hmul, associativeGlennieRight]

theorem glennie_identity_of_injective_associative_realization
    (f : J →ₗ[ℝ] A)
    (hmul : ∀ x y, f (x * y) = associativeJordanProduct (f x) (f y))
    (hf : Function.Injective f)
    (x y z : J) :
    glennieLeft x y z = glennieRight x y z := by
  apply hf
  calc
    f (glennieLeft x y z) = associativeGlennieLeft (f x) (f y) (f z) :=
      map_glennieLeft f hmul x y z
    _ = associativeGlennieRight (f x) (f y) (f z) :=
      glennie_identity_in_associative_symmetrization _ _ _
    _ = f (glennieRight x y z) := (map_glennieRight f hmul x y z).symm

end Glennie
