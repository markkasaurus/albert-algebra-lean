import AlbertAlgebra.Octonion

/-!
# Hermitian three-by-three octonion matrices

`H3Octonion` is the real vector space of Hermitian three-by-three octonion
matrices with the symmetrized matrix product.
-/

noncomputable section

set_option autoImplicit false

/-- The real submodule of Hermitian `3 × 3` matrices over the octonions. -/
def H3Octonion : Submodule ℝ (Matrix (Fin 3) (Fin 3) Octonion) where
  carrier := { A | A.conjTranspose = A }
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    funext i j
    simp only [Matrix.conjTranspose_apply, Matrix.zero_apply]
    exact Octonion.star_zero
  add_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    funext i j
    simp only [Matrix.conjTranspose_apply, Matrix.add_apply]
    rw [Octonion.star_add]
    have hAij : star (A j i) = A i j := congr_fun₂ hA i j
    have hBij : star (B j i) = B i j := congr_fun₂ hB i j
    rw [hAij, hBij]
  smul_mem' := by
    intro r A hA
    simp only [Set.mem_setOf_eq] at hA ⊢
    funext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply]
    rw [star_smul, star_trivial]
    have hAij : star (A j i) = A i j := congr_fun₂ hA i j
    rw [hAij]

@[ext] lemma H3Octonion.ext {A B : H3Octonion}
    (h : (A : Matrix (Fin 3) (Fin 3) Octonion) = B) : A = B :=
  Subtype.ext h

noncomputable instance : Mul H3Octonion where
  mul A B :=
    ⟨(1/2 : ℝ) • (A.1 * B.1 + B.1 * A.1), by

      have hA : A.1.conjTranspose = A.1 := A.2
      have hB : B.1.conjTranspose = B.1 := B.2

      funext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply]

      rw [star_smul, star_trivial]

      congr 1

      rw [Octonion.star_add]

      rw [star_sum, star_sum]

      simp_rw [Octonion.star_mul]

      have hA_elem : ∀ p q, star (A.1 p q) = A.1 q p := by
        intro p q
        exact congr_fun₂ hA q p
      have hB_elem : ∀ p q, star (B.1 p q) = B.1 q p := by
        intro p q
        exact congr_fun₂ hB q p
      simp_rw [hA_elem, hB_elem]

      rw [add_comm]⟩

instance : One H3Octonion where
  one := ⟨(1 : Matrix (Fin 3) (Fin 3) Octonion), by
    funext i j
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply]
    split_ifs with h1 h2 h2
    · exact Octonion.star_one
    · exact (h2 h1.symm).elim
    · exact (h1 h2.symm).elim
    · exact Octonion.star_zero⟩
