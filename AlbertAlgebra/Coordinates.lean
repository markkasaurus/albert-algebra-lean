import AlbertAlgebra.JordanIdentity

/-!
# Coordinates and dimension of H3(O)

The independent coordinates are three real diagonal entries and three
octonion off-diagonal entries. They give a real-linear equivalence with
`R^3 x O^3` and a dimension calculation.
-/

noncomputable section

namespace Albert.Coordinates

open Albert

/-- Three real diagonal coordinates and three octonion off-diagonal coordinates. -/
abbrev H3Coordinates := (Fin 3 -> Real) × (Fin 3 -> Octonion)

private theorem fin3_01 : (0 : Fin 3) ≠ 1 := by decide
private theorem fin3_02 : (0 : Fin 3) ≠ 2 := by decide
private theorem fin3_12 : (1 : Fin 3) ≠ 2 := by decide

/-- The linear map placing an octonion in one Hermitian off-diagonal pair. -/
def rankOneLinear (i j : Fin 3) (hij : i ≠ j) :
    Octonion →ₗ[Real] H3Octonion where
  toFun := H3Octonion.rankOne i j hij
  map_add' x y := by
    apply H3Octonion.ext
    funext p q
    change
      (if p = i ∧ q = j then x + y
        else if p = j ∧ q = i then star (x + y) else 0) =
      (if p = i ∧ q = j then x
        else if p = j ∧ q = i then star x else 0) +
      (if p = i ∧ q = j then y
        else if p = j ∧ q = i then star y else 0)
    split_ifs <;> simp_all
  map_smul' r x := by
    apply H3Octonion.ext
    funext p q
    change
      (if p = i ∧ q = j then r • x
        else if p = j ∧ q = i then star (r • x) else 0) =
      r • (if p = i ∧ q = j then x
        else if p = j ∧ q = i then star x else 0)
    split_ifs <;> simp_all

/-- The linear map from three real entries to a diagonal Hermitian matrix. -/
def diagonalLinear : (Fin 3 -> Real) →ₗ[Real] H3Octonion where
  toFun d := ∑ i : Fin 3, d i • E i
  map_add' d e := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r d := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, RingHom.id_apply, smul_smul]
    change (r * d i) • E i = (r * d i) • E i
    rfl

/-- Reconstruct a Hermitian octonion matrix from its independent coordinates. -/
def ofCoordinatesLinear : H3Coordinates →ₗ[Real] H3Octonion where
  toFun c :=
    diagonalLinear c.1 +
      rankOneLinear 0 1 fin3_01 (c.2 0) +
      rankOneLinear 0 2 fin3_02 (c.2 1) +
      rankOneLinear 1 2 fin3_12 (c.2 2)
  map_add' c d := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]
    abel
  map_smul' r c := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
      RingHom.id_apply]
    module

/-- Extract the independent coordinates of a Hermitian octonion matrix. -/
def coordinatesOfLinear : H3Octonion →ₗ[Real] H3Coordinates where
  toFun X :=
    (fun i => (X.1 i i).1.re,
      ![X.1 0 1, X.1 0 2, X.1 1 2])
  map_add' X Y := by
    apply Prod.ext
    · funext i
      rfl
    · funext i
      fin_cases i <;> rfl
  map_smul' r X := by
    apply Prod.ext
    · funext i
      rfl
    · funext i
      fin_cases i <;> rfl

theorem coordinatesOf_leftInverse :
    Function.LeftInverse coordinatesOfLinear ofCoordinatesLinear := by
  rintro ⟨d, o⟩
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [coordinatesOfLinear, ofCoordinatesLinear, diagonalLinear,
        rankOneLinear, H3Octonion.rankOne, E, Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [coordinatesOfLinear, ofCoordinatesLinear, diagonalLinear,
        rankOneLinear, H3Octonion.rankOne, E, Fin.sum_univ_three]

theorem coordinatesOf_rightInverse :
    Function.RightInverse coordinatesOfLinear ofCoordinatesLinear := by
  intro X
  have hdiag0 := Octonion.eq_smul_one_of_star_self
    (X.1 0 0) (H3Octonion.diag_star X 0)
  have hdiag1 := Octonion.eq_smul_one_of_star_self
    (X.1 1 1) (H3Octonion.diag_star X 1)
  have hdiag2 := Octonion.eq_smul_one_of_star_self
    (X.1 2 2) (H3Octonion.diag_star X 2)
  have hdiag :
      diagonalLinear (fun i => (X.1 i i).1.re) = H3Octonion.diagPart X := by
    apply H3Octonion.ext
    funext i j
    fin_cases i <;> fin_cases j
    · simpa [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E] using hdiag0.symm
    · simp [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E]
    · simp [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E]
    · simp [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E]
    · simpa [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E] using hdiag1.symm
    · simp [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E]
    · simp [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E]
    · simp [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E]
    · simpa [diagonalLinear, Fin.sum_univ_three,
        H3Octonion.diagPart_apply, E] using hdiag2.symm
  have hoff :
      H3Octonion.rankOne 0 1 fin3_01 (X.1 0 1) +
          H3Octonion.rankOne 0 2 fin3_02 (X.1 0 2) +
          H3Octonion.rankOne 1 2 fin3_12 (X.1 1 2) =
        H3Octonion.offDiagPart X :=
    (H3Octonion.offDiagPart_eq_rankOne_sum X).symm
  change
    diagonalLinear (fun i => (X.1 i i).1.re) +
        H3Octonion.rankOne 0 1 fin3_01 (X.1 0 1) +
        H3Octonion.rankOne 0 2 fin3_02 (X.1 0 2) +
        H3Octonion.rankOne 1 2 fin3_12 (X.1 1 2) = X
  rw [hdiag]
  calc
    H3Octonion.diagPart X + H3Octonion.rankOne 0 1 fin3_01 (X.1 0 1) +
          H3Octonion.rankOne 0 2 fin3_02 (X.1 0 2) +
          H3Octonion.rankOne 1 2 fin3_12 (X.1 1 2) =
        H3Octonion.diagPart X +
          (H3Octonion.rankOne 0 1 fin3_01 (X.1 0 1) +
            H3Octonion.rankOne 0 2 fin3_02 (X.1 0 2) +
            H3Octonion.rankOne 1 2 fin3_12 (X.1 1 2)) := by abel
    _ = H3Octonion.diagPart X + H3Octonion.offDiagPart X := by rw [hoff]
    _ = X := H3Octonion.diagPart_plus_offDiagPart X

/-- The real-linear equivalence between independent coordinates and `H3Octonion`. -/
def coordinateEquiv : H3Coordinates ≃ₗ[Real] H3Octonion where
  toFun := ofCoordinatesLinear
  invFun := coordinatesOfLinear
  map_add' := ofCoordinatesLinear.map_add
  map_smul' := ofCoordinatesLinear.map_smul
  left_inv := coordinatesOf_leftInverse
  right_inv := coordinatesOf_rightInverse

theorem finrank_eq_twenty_seven : Module.finrank Real H3Octonion = 27 := by
  rw [← LinearEquiv.finrank_eq coordinateEquiv]
  rw [Module.finrank_prod]
  rw [Module.finrank_pi Real, Module.finrank_pi_fintype Real]
  simp [Octonion.finrank_eq_eight]

end Albert.Coordinates
