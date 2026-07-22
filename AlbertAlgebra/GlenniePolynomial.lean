import Mathlib.Algebra.Jordan.Basic
import Mathlib.Data.Real.Basic

/-!
# Glennie's degree-eight polynomials

The polynomial definitions are separated from both the associative identity
proof and the counterexample in the Albert algebra.
-/

noncomputable section

namespace Glennie

/-- The Jordan triple product used in Glennie's degree-eight identity. -/
def jordanTriple {J : Type*} [AddGroup J] [Mul J]
    (x y z : J) : J :=
  x * (y * z) - y * (z * x) + z * (x * y)

/-- The left-hand side of Glennie's degree-eight identity. -/
def glennieLeft {J : Type*} [AddGroup J] [Mul J]
    (x y z : J) : J :=
  2 • jordanTriple (jordanTriple z (jordanTriple x y x) z) y (z * x) -
    jordanTriple z (jordanTriple x (jordanTriple y (x * z) y) x) z

/-- The right-hand side of Glennie's degree-eight identity. -/
def glennieRight {J : Type*} [AddGroup J] [Mul J]
    (x y z : J) : J :=
  2 • jordanTriple (x * z) y
      (jordanTriple x (jordanTriple z y z) x) -
    jordanTriple x (jordanTriple z (jordanTriple y (x * z) y) z) x

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The symmetrized Jordan product on an associative real algebra. -/
def associativeJordanProduct (x y : A) : A :=
  (1 / 2 : ℝ) • (x * y + y * x)

/-- The Jordan triple product induced by `associativeJordanProduct`. -/
def associativeJordanTriple (x y z : A) : A :=
  associativeJordanProduct x (associativeJordanProduct y z) -
    associativeJordanProduct y (associativeJordanProduct z x) +
    associativeJordanProduct z (associativeJordanProduct x y)

/-- The left Glennie polynomial evaluated using the associative symmetrization. -/
def associativeGlennieLeft (x y z : A) : A :=
  2 • associativeJordanTriple
      (associativeJordanTriple z (associativeJordanTriple x y x) z) y
      (associativeJordanProduct z x) -
    associativeJordanTriple z
      (associativeJordanTriple x
        (associativeJordanTriple y (associativeJordanProduct x z) y) x) z

/-- The right Glennie polynomial evaluated using the associative symmetrization. -/
def associativeGlennieRight (x y z : A) : A :=
  2 • associativeJordanTriple (associativeJordanProduct x z) y
      (associativeJordanTriple x (associativeJordanTriple z y z) x) -
    associativeJordanTriple x
      (associativeJordanTriple z
        (associativeJordanTriple y (associativeJordanProduct x z) y) z) x

end Glennie
