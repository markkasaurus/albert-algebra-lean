import AlbertAlgebra.CoordinateProduct
import AlbertAlgebra.GlennieIdentity

/-!
# An explicit Glennie-identity violation in H3(O)

Three sparse elements are evaluated exactly. One coordinate of the two sides
of Glennie's identity is respectively `1` and `-1`.
-/

noncomputable section

namespace Albert.GlennieWitness

open Albert
open Albert.Coordinates
open Albert.CoordinateProduct
open Glennie

/-- Construct an octonion from its eight real coordinates. -/
def octonionOfCoords
    (a0 a1 a2 a3 a4 a5 a6 a7 : ℝ) : Octonion :=
  (⟨a0, a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩)

attribute [local simp] Octonion.inner Octonion.normSq
attribute [local ext] Octonion.ext'

/-- Construct a Hermitian matrix from three diagonal and three off-diagonal entries. -/
def ofSixCoordinates (d0 d1 d2 : ℝ)
    (o01 o02 o12 : Octonion) : H3Octonion :=
  ofCoordinatesLinear (![d0, d1, d2], ![o01, o02, o12])

@[simp] theorem coordinates_ofSixCoordinates
    (d0 d1 d2 : ℝ) (o01 o02 o12 : Octonion) :
    coordinatesOfLinear (ofSixCoordinates d0 d1 d2 o01 o02 o12) =
      (![d0, d1, d2], ![o01, o02, o12]) :=
  coordinatesOf_leftInverse _

/-- The first element in the explicit Glennie counterexample. -/
def glennieX : H3Octonion :=
  ofSixCoordinates 0 0 0
    (octonionOfCoords 0 0 0 (-1) 0 0 0 (-1)) 0 0

/-- The second element in the explicit Glennie counterexample. -/
def glennieY : H3Octonion :=
  ofSixCoordinates 0 0 0
    (octonionOfCoords 0 (-1) 0 0 0 0 0 0) 0
    (octonionOfCoords 0 0 0 0 0 0 1 0)

/-- The third element in the explicit Glennie counterexample. -/
def glennieZ : H3Octonion :=
  ofSixCoordinates 0 0 0
    (octonionOfCoords 0 0 0 0 0 0 0 (-1)) 0
    (octonionOfCoords 0 (-1) 0 0 0 0 0 0)

/-- The Jordan triple product evaluated in independent Hermitian coordinates. -/
def jordanTripleCoords (x y z : H3Coordinates) : H3Coordinates :=
  jordanProductCoords x (jordanProductCoords y z) -
    jordanProductCoords y (jordanProductCoords z x) +
    jordanProductCoords z (jordanProductCoords x y)

theorem coordinatesOf_jordanTriple (x y z : H3Octonion) :
    coordinatesOfLinear (jordanTriple x y z) =
      jordanTripleCoords (coordinatesOfLinear x) (coordinatesOfLinear y)
        (coordinatesOfLinear z) := by
  simp only [jordanTriple, map_add, map_sub, coordinatesOf_jordanProduct,
    jordanTripleCoords]

private def zx : H3Octonion :=
  ofSixCoordinates 1 1 0 0
    (octonionOfCoords 0 0 (1 / 2) 0 0 0 (-1 / 2) 0) 0

private def xyx : H3Octonion :=
  ofSixCoordinates 0 0 0
    (octonionOfCoords 0 2 0 0 0 0 0 0) 0 0

private def z_xyx_z : H3Octonion :=
  ofSixCoordinates 0 0 0
    (octonionOfCoords 0 (-2) 0 0 0 0 0 0) 0
    (octonionOfCoords 0 0 0 0 0 0 0 2)

private def leftFirst : H3Octonion :=
  ofSixCoordinates 2 2 1 0
    (octonionOfCoords 0 0 (1 / 2) (1 / 2) 0 0 (-3 / 2) (-1 / 2)) 0

private def y_zx_y : H3Octonion :=
  ofSixCoordinates 1 1 1 0
    (octonionOfCoords 0 0 0 0 0 0 0 1) 0

private def x_yzxy_x : H3Octonion :=
  ofSixCoordinates 2 2 0 0 0 0

private def leftSecond : H3Octonion :=
  ofSixCoordinates 2 2 2 0
    (octonionOfCoords 0 0 0 0 0 0 (-2) 0) 0

/-- The exact value of the left Glennie polynomial on the witness. -/
def glennieLeftValue : H3Octonion :=
  ofSixCoordinates 2 2 0 0
    (octonionOfCoords 0 0 1 1 0 0 (-1) (-1)) 0

private def zyz : H3Octonion :=
  ofSixCoordinates 0 0 0
    (octonionOfCoords 1 1 0 0 0 0 0 0) 0
    (octonionOfCoords 0 0 0 0 0 0 (-1) (-1))

private def x_zyz_x : H3Octonion :=
  ofSixCoordinates 0 0 0
    (octonionOfCoords (-2) (-2) 0 0 0 0 0 0) 0 0

private def rightFirst : H3Octonion :=
  ofSixCoordinates 3 2 0 0
    (octonionOfCoords 0 0 (1 / 2) (-1 / 2) 0 0 (-1 / 2) (-1 / 2)) 0

private def z_yzxy_z : H3Octonion :=
  ofSixCoordinates 1 2 1 0
    (octonionOfCoords 0 0 0 0 0 0 (-1) 0) 0

private def rightSecond : H3Octonion :=
  ofSixCoordinates 4 2 0 0 0 0

/-- The exact value of the right Glennie polynomial on the witness. -/
def glennieRightValue : H3Octonion :=
  ofSixCoordinates 2 2 0 0
    (octonionOfCoords 0 0 1 (-1) 0 0 (-1) (-1)) 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem z_mul_x : glennieZ * glennieX = zx := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (glennieZ * glennieX) = coordinatesOfLinear zx
  rw [coordinatesOf_jordanProduct]
  simp only [glennieX, glennieZ, zx, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanProductCoords, octonionOfCoords,
        Octonion.inner, Octonion.normSq] <;> norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanProductCoords, octonionOfCoords]; norm_num

private theorem x_mul_z : glennieX * glennieZ = zx := by
  rw [mul_comm, z_mul_x]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_xyx :
    jordanTriple glennieX glennieY glennieX = xyx := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieX glennieY glennieX) =
    coordinatesOfLinear xyx
  rw [coordinatesOf_jordanTriple]
  simp only [glennieX, glennieY, xyx, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq]
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_z_xyx_z :
    jordanTriple glennieZ xyx glennieZ = z_xyx_z := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieZ xyx glennieZ) =
    coordinatesOfLinear z_xyx_z
  rw [coordinatesOf_jordanTriple]
  simp only [glennieZ, xyx, z_xyx_z, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq]
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_leftFirst :
    jordanTriple z_xyx_z glennieY zx = leftFirst := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple z_xyx_z glennieY zx) =
    coordinatesOfLinear leftFirst
  rw [coordinatesOf_jordanTriple]
  simp only [z_xyx_z, glennieY, zx, leftFirst, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq] <;>
        norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_y_zx_y :
    jordanTriple glennieY zx glennieY = y_zx_y := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieY zx glennieY) =
    coordinatesOfLinear y_zx_y
  rw [coordinatesOf_jordanTriple]
  simp only [glennieY, zx, y_zx_y, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq] <;>
        norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_x_yzxy_x :
    jordanTriple glennieX y_zx_y glennieX = x_yzxy_x := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieX y_zx_y glennieX) =
    coordinatesOfLinear x_yzxy_x
  rw [coordinatesOf_jordanTriple]
  simp only [glennieX, y_zx_y, x_yzxy_x, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq] <;>
        norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords]; norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_leftSecond :
    jordanTriple glennieZ x_yzxy_x glennieZ = leftSecond := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieZ x_yzxy_x glennieZ) =
    coordinatesOfLinear leftSecond
  rw [coordinatesOf_jordanTriple]
  simp only [glennieZ, x_yzxy_x, leftSecond, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq] <;>
        norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords]; norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_zyz :
    jordanTriple glennieZ glennieY glennieZ = zyz := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieZ glennieY glennieZ) =
    coordinatesOfLinear zyz
  rw [coordinatesOf_jordanTriple]
  simp only [glennieZ, glennieY, zyz, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq]
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_x_zyz_x :
    jordanTriple glennieX zyz glennieX = x_zyz_x := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieX zyz glennieX) =
    coordinatesOfLinear x_zyz_x
  rw [coordinatesOf_jordanTriple]
  simp only [glennieX, zyz, x_zyz_x, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq]
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_rightFirst :
    jordanTriple zx glennieY x_zyz_x = rightFirst := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple zx glennieY x_zyz_x) =
    coordinatesOfLinear rightFirst
  rw [coordinatesOf_jordanTriple]
  simp only [zx, glennieY, x_zyz_x, rightFirst, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq] <;>
        norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_z_yzxy_z :
    jordanTriple glennieZ y_zx_y glennieZ = z_yzxy_z := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieZ y_zx_y glennieZ) =
    coordinatesOfLinear z_yzxy_z
  rw [coordinatesOf_jordanTriple]
  simp only [glennieZ, y_zx_y, z_yzxy_z, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq] <;>
        norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem triple_rightSecond :
    jordanTriple glennieX z_yzxy_z glennieX = rightSecond := by
  apply coordinateEquiv.symm.injective
  change coordinatesOfLinear (jordanTriple glennieX z_yzxy_z glennieX) =
    coordinatesOfLinear rightSecond
  rw [coordinatesOf_jordanTriple]
  simp only [glennieX, z_yzxy_z, rightSecond, coordinates_ofSixCoordinates]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords, Octonion.inner, Octonion.normSq] <;>
        norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp +decide [jordanTripleCoords, jordanProductCoords,
        octonionOfCoords]; norm_num

set_option maxHeartbeats 0 in
theorem glennieLeft_witness_eq :
    glennieLeft glennieX glennieY glennieZ = glennieLeftValue := by
  rw [glennieLeft, triple_xyx, triple_z_xyx_z, z_mul_x,
    triple_leftFirst, x_mul_z, triple_y_zx_y, triple_x_yzxy_x,
    triple_leftSecond]
  simp only [leftFirst, leftSecond, glennieLeftValue, ofSixCoordinates]
  rw [← map_nsmul, ← map_sub]
  apply congrArg ofCoordinatesLinear
  rw [two_nsmul]
  apply Prod.ext
  · funext i
    fin_cases i <;> norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp [octonionOfCoords] <;> norm_num

set_option maxHeartbeats 0 in
theorem glennieRight_witness_eq :
    glennieRight glennieX glennieY glennieZ = glennieRightValue := by
  rw [glennieRight, x_mul_z, triple_zyz, triple_x_zyz_x,
    triple_rightFirst, triple_y_zx_y, triple_z_yzxy_z,
    triple_rightSecond]
  simp only [rightFirst, rightSecond, glennieRightValue, ofSixCoordinates]
  rw [← map_nsmul, ← map_sub]
  apply congrArg ofCoordinatesLinear
  rw [two_nsmul]
  apply Prod.ext
  · funext i
    fin_cases i <;> norm_num
  · funext i
    fin_cases i <;> ext <;>
      simp [octonionOfCoords]; norm_num

theorem glennie_witness_distinguishing_coordinates :
    (((coordinatesOfLinear
        (glennieLeft glennieX glennieY glennieZ)).2 1).1.imK) = 1 ∧
      (((coordinatesOfLinear
        (glennieRight glennieX glennieY glennieZ)).2 1).1.imK) = -1 := by
  rw [glennieLeft_witness_eq, glennieRight_witness_eq]
  norm_num [glennieLeftValue, glennieRightValue,
    coordinates_ofSixCoordinates, octonionOfCoords]

theorem violates_glennie_identity :
    glennieLeft glennieX glennieY glennieZ ≠
      glennieRight glennieX glennieY glennieZ := by
  rw [glennieLeft_witness_eq, glennieRight_witness_eq]
  intro h
  have hk := congrArg
    (fun w : H3Octonion => (((coordinatesOfLinear w).2 1).1.imK)) h
  norm_num [glennieLeftValue, glennieRightValue,
    coordinates_ofSixCoordinates, octonionOfCoords] at hk

theorem no_injective_associative_realization
    {A : Type*} [Ring A] [Algebra ℝ A]
    (f : H3Octonion →ₗ[ℝ] A)
    (hmul : ∀ x y,
      f (x * y) = associativeJordanProduct (f x) (f y)) :
    ¬ Function.Injective f := by
  intro hf
  apply violates_glennie_identity
  exact glennie_identity_of_injective_associative_realization
    f hmul hf glennieX glennieY glennieZ

theorem associative_realization_has_nonzero_kernel
    {A : Type*} [Ring A] [Algebra ℝ A]
    (f : H3Octonion →ₗ[ℝ] A)
    (hmul : ∀ x y,
      f (x * y) = associativeJordanProduct (f x) (f y)) :
    ∃ x : H3Octonion, x ≠ 0 ∧ f x = 0 := by
  have hnot : ¬ Function.Injective f :=
    no_injective_associative_realization f hmul
  rcases Function.not_injective_iff.mp hnot with ⟨x, y, hxy, hne⟩
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  simp only [map_sub, hxy, sub_self]

end Albert.GlennieWitness
