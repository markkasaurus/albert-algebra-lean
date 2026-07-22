import AlbertAlgebra.GlennieWitness
import Mathlib.Algebra.Symmetrized

/-!
# Non-speciality of H3(O)

The explicit Glennie witness excludes every faithful realization in the
symmetrization of an associative real algebra.
-/

noncomputable section

namespace Albert

open Glennie
open GlennieWitness

variable {A : Type*} [Ring A] [Algebra ℝ A] [Invertible (2 : A)]

/-- The real-linear map forgetting the symmetrized multiplication on `Aˢʸᵐ`. -/
def symAlgUnsymLinear : Aˢʸᵐ →ₗ[ℝ] A where
  toFun := SymAlg.unsym
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem no_faithful_special_embedding
    (f : H3Octonion →ₗ[ℝ] Aˢʸᵐ)
    (hmul : ∀ x y, f (x * y) = f x * f y) :
    ¬ Function.Injective f := by
  let g : H3Octonion →ₗ[ℝ] A := symAlgUnsymLinear.comp f
  have hinv : ⅟(2 : A) = algebraMap ℝ A (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap ℝ A) 2, ← map_mul]
    norm_num
  have gmul : ∀ x y,
      g (x * y) = associativeJordanProduct (g x) (g y) := by
    intro x y
    change SymAlg.unsym (f (x * y)) =
      (1 / 2 : ℝ) • (SymAlg.unsym (f x) * SymAlg.unsym (f y) +
        SymAlg.unsym (f y) * SymAlg.unsym (f x))
    rw [hmul, SymAlg.unsym_mul, hinv]
    rw [← Algebra.smul_def]
  intro hf
  exact no_injective_associative_realization g gmul
    (SymAlg.unsym_injective.comp hf)

end Albert
