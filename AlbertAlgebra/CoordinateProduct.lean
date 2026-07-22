import AlbertAlgebra.Coordinates

/-!
# Coordinate formula for the Albert product

The symmetrized matrix product on `H3Octonion` is expressed in the six
independent Hermitian coordinates.
-/

noncomputable section

namespace Albert.CoordinateProduct

open Albert
open Albert.Coordinates

/-- The Albert product expressed in independent Hermitian coordinates. -/
def jordanProductCoords (p q : H3Coordinates) : H3Coordinates :=
  (![
      p.1 0 * q.1 0 + Octonion.inner (p.2 0) (q.2 0) +
        Octonion.inner (p.2 1) (q.2 1),
      p.1 1 * q.1 1 + Octonion.inner (p.2 0) (q.2 0) +
        Octonion.inner (p.2 2) (q.2 2),
      p.1 2 * q.1 2 + Octonion.inner (p.2 1) (q.2 1) +
        Octonion.inner (p.2 2) (q.2 2)],
    ![
      ((q.1 0 + q.1 1) / 2) • p.2 0 +
        ((p.1 0 + p.1 1) / 2) • q.2 0 +
        (1 / 2 : ℝ) •
          (p.2 1 * star (q.2 2) + q.2 1 * star (p.2 2)),
      ((q.1 0 + q.1 2) / 2) • p.2 1 +
        ((p.1 0 + p.1 2) / 2) • q.2 1 +
        (1 / 2 : ℝ) • (p.2 0 * q.2 2 + q.2 0 * p.2 2),
      ((q.1 1 + q.1 2) / 2) • p.2 2 +
        ((p.1 1 + p.1 2) / 2) • q.2 2 +
        (1 / 2 : ℝ) •
          (star (p.2 0) * q.2 1 + star (q.2 0) * p.2 1)])

set_option maxHeartbeats 0 in
private theorem coordinatesOf_product_ofCoordinates
    (p q : H3Coordinates) :
    coordinatesOfLinear (ofCoordinatesLinear p * ofCoordinatesLinear q) =
      jordanProductCoords p q := by
  rcases p with ⟨d, o⟩
  rcases q with ⟨e, u⟩
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [coordinatesOfLinear, ofCoordinatesLinear, diagonalLinear,
        rankOneLinear, H3Octonion.rankOne, E, jordanProductCoords,
        jordan_mul_val, Matrix.mul_apply, Fin.sum_univ_three,
        Octonion.inner, Octonion.normSq] <;>
      ring
  · funext i
    fin_cases i <;>
      apply Octonion.ext' <;>
      apply Quaternion.ext <;>
      simp +decide [coordinatesOfLinear, ofCoordinatesLinear, diagonalLinear,
        rankOneLinear, H3Octonion.rankOne, E, jordanProductCoords,
        jordan_mul_val, Matrix.mul_apply, Fin.sum_univ_three,
        Octonion.inner, Octonion.normSq] <;>
      ring

theorem coordinatesOf_jordanProduct (x y : H3Octonion) :
    coordinatesOfLinear (x * y) =
      jordanProductCoords (coordinatesOfLinear x) (coordinatesOfLinear y) := by
  calc
    coordinatesOfLinear (x * y) =
        coordinatesOfLinear
          (ofCoordinatesLinear (coordinatesOfLinear x) *
            ofCoordinatesLinear (coordinatesOfLinear y)) := by
      rw [coordinatesOf_rightInverse x, coordinatesOf_rightInverse y]
    _ = jordanProductCoords (coordinatesOfLinear x) (coordinatesOfLinear y) :=
      coordinatesOf_product_ofCoordinates _ _

end Albert.CoordinateProduct
