import Mathlib.Analysis.Quaternion
import Mathlib.Tactic

/-!
# Real octonions

The real octonions are implemented by Cayley-Dickson doubling of the real
quaternions. Multiplication and conjugation are defined explicitly.
-/

noncomputable section

set_option autoImplicit false

/-- The real octonions, represented by Cayley-Dickson pairs of real quaternions. -/
def Octonion := Quaternion ℝ × Quaternion ℝ

instance : Add Octonion := inferInstanceAs (Add (Quaternion ℝ × Quaternion ℝ))
instance : Neg Octonion := inferInstanceAs (Neg (Quaternion ℝ × Quaternion ℝ))
instance : Zero Octonion := inferInstanceAs (Zero (Quaternion ℝ × Quaternion ℝ))
instance : One Octonion := ⟨(1, 0)⟩
instance : SMul ℝ Octonion := inferInstanceAs (SMul ℝ (Quaternion ℝ × Quaternion ℝ))

noncomputable instance : Mul Octonion where
  mul x y :=
    let (a, b) := x
    let (c, d) := y
    (a * c - star d * b, d * a + b * star c)

theorem Octonion.zero_mul (a : Octonion) : 0 * a = 0 := by
  have h_mul :
      (0 : Octonion) * a =
        (0 * a.1 - star a.2 * 0, a.2 * 0 + 0 * star a.1) := by
    rfl
  aesop

theorem Octonion.mul_zero (a : Octonion) : a * 0 = 0 := by
  have h_mul_def :
      a * 0 = (a.1 * 0 - star 0 * a.2, 0 * a.1 + a.2 * star 0) := by
    rfl
  aesop

theorem Octonion.mul_one (a : Octonion) : a * 1 = a := by
  obtain ⟨x, y⟩ := a
  have h_simp : (x * 1 - star 0 * y, 0 * x + y * star 1) = (x, y) := by
    norm_num [Quaternion.ext_iff]
  exact h_simp

theorem Octonion.one_mul (a : Octonion) : 1 * a = a := by
  have h_mul :
      ∀ a : Octonion,
        (1 : Octonion) * a =
          (1 * a.1 - star a.2 * 0, a.2 * 1 + 0 * star a.1) := by
    intro a
    rfl
  simp [h_mul]

theorem Octonion.left_distrib (a b c : Octonion) : a * (b + c) = a * b + a * c := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  have h_distrib :
      a1 * (b1 + c1) - star (b2 + c2) * a2 =
          (a1 * b1 - star b2 * a2) + (a1 * c1 - star c2 * a2) ∧
        (b2 + c2) * a1 + a2 * star (b1 + c1) =
          (b2 * a1 + a2 * star b1) + (c2 * a1 + a2 * star c1) := by
    simp +decide [mul_add, add_mul, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
  exact Prod.ext h_distrib.1 h_distrib.2

theorem Octonion.right_distrib (a b c : Octonion) : (a + b) * c = a * c + b * c := by
  have h_expand :
      (a + b) * c =
        ((a.1 + b.1) * c.1 - star c.2 * (a.2 + b.2),
          c.2 * (a.1 + b.1) + (a.2 + b.2) * star c.1) := by
    rfl
  have h_expand_rhs :
      a * c + b * c =
        ((a.1 * c.1 - star c.2 * a.2) +
            (b.1 * c.1 - star c.2 * b.2),
          (c.2 * a.1 + a.2 * star c.1) +
            (c.2 * b.1 + b.2 * star c.1)) := by
    rfl
  simp_all +decide [add_mul, mul_add, add_assoc, add_left_comm,
    sub_eq_add_neg]
  ac_rfl

instance : AddCommGroup Octonion := inferInstanceAs (AddCommGroup (Quaternion ℝ × Quaternion ℝ))

noncomputable instance : NonAssocRing Octonion :=
  { inferInstanceAs (AddCommGroup Octonion),
    inferInstanceAs (One Octonion),
    inferInstanceAs (Mul Octonion) with
    zero_mul := Octonion.zero_mul
    mul_zero := Octonion.mul_zero
    mul_one := Octonion.mul_one
    one_mul := Octonion.one_mul
    left_distrib := Octonion.left_distrib
    right_distrib := Octonion.right_distrib }

instance : Module ℝ Octonion := inferInstanceAs (Module ℝ (Quaternion ℝ × Quaternion ℝ))

instance : Star Octonion where
  star x := let (a, b) := x; (star a, -b)

private lemma quat_star_star (a : Quaternion ℝ) : star (star a) = a := by
  ext <;> simp

private lemma quat_star_add (a b : Quaternion ℝ) : star (a + b) = star a + star b := by
  ext <;> simp

private lemma quat_star_zero : star (0 : Quaternion ℝ) = 0 := by
  ext <;> simp

private lemma quat_star_smul (r : ℝ) (a : Quaternion ℝ) : star (r • a) = r • star a := by
  ext <;> simp

private lemma quat_star_one : star (1 : Quaternion ℝ) = 1 := by
  ext <;> simp

private lemma quat_star_neg (a : Quaternion ℝ) : star (-a) = -star a := by
  ext <;> simp

private lemma quat_star_sub (a b : Quaternion ℝ) : star (a - b) = star a - star b := by
  ext <;> simp

private lemma quat_star_mul (a b : Quaternion ℝ) : star (a * b) = star b * star a := by
  ext <;> simp

lemma Octonion.star_star (x : Octonion) : star (star x) = x := by
  obtain ⟨a, b⟩ := x
  apply Prod.ext
  · exact quat_star_star a
  · exact neg_neg b

lemma Octonion.star_add (x y : Octonion) : star (x + y) = star x + star y := by
  obtain ⟨a1, a2⟩ := x
  obtain ⟨b1, b2⟩ := y
  apply Prod.ext
  · exact quat_star_add a1 b1
  · exact neg_add a2 b2

lemma Octonion.star_zero : star (0 : Octonion) = 0 := by
  apply Prod.ext
  · exact quat_star_zero
  · exact neg_zero

instance : StarAddMonoid Octonion where
  star_involutive := Octonion.star_star
  star_add := Octonion.star_add

instance : StarModule ℝ Octonion where
  star_smul := by
    intro r x
    obtain ⟨a, b⟩ := x
    apply Prod.ext
    · exact quat_star_smul r a
    · exact (smul_neg r b).symm

lemma Octonion.star_one : star (1 : Octonion) = 1 := by
  apply Prod.ext
  · exact quat_star_one
  · exact neg_zero

lemma Octonion.ext' {x y : Octonion} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y :=
  Prod.ext h1 h2

@[simp] lemma Octonion.star_fst (x : Octonion) : (star x).1 = star x.1 := rfl
@[simp] lemma Octonion.star_snd (x : Octonion) : (star x).2 = -x.2 := rfl
@[simp] lemma Octonion.mul_fst (x y : Octonion) : (x * y).1 = x.1 * y.1 - star y.2 * x.2 := rfl
@[simp] lemma Octonion.mul_snd (x y : Octonion) : (x * y).2 = y.2 * x.1 + x.2 * star y.1 := rfl
@[simp] lemma Octonion.fst_zero : (0 : Octonion).1 = 0 := rfl
@[simp] lemma Octonion.snd_zero : (0 : Octonion).2 = 0 := rfl
@[simp] lemma Octonion.fst_one : (1 : Octonion).1 = 1 := rfl
@[simp] lemma Octonion.snd_one : (1 : Octonion).2 = 0 := rfl
@[simp] lemma Octonion.fst_add (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
@[simp] lemma Octonion.snd_add (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
@[simp] lemma Octonion.fst_sub (x y : Octonion) : (x - y).1 = x.1 - y.1 := rfl
@[simp] lemma Octonion.snd_sub (x y : Octonion) : (x - y).2 = x.2 - y.2 := rfl
@[simp] lemma Octonion.fst_neg (x : Octonion) : (-x).1 = -x.1 := rfl
@[simp] lemma Octonion.snd_neg (x : Octonion) : (-x).2 = -x.2 := rfl
@[simp] lemma Octonion.fst_smul (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
@[simp] lemma Octonion.snd_smul (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl

lemma Octonion.star_mul (x y : Octonion) : star (x * y) = star y * star x := by
  apply Prod.ext
  ·
    simp only [Octonion.star_fst, Octonion.star_snd, Octonion.mul_fst]

    rw [quat_star_sub, quat_star_mul, quat_star_mul, quat_star_star, quat_star_neg]
    apply congrArg (fun q : Quaternion ℝ => star y.1 * star x.1 - q)
    exact (neg_mul_neg (star x.2) y.2).symm
  ·
    simp only [Octonion.star_fst, Octonion.star_snd, Octonion.mul_snd]

    rw [quat_star_star]
    rw [neg_add_rev]
    exact congrArg₂ (· + ·)
      (neg_mul x.2 (star y.1)).symm
      (neg_mul y.2 x.1).symm

/-- The squared Euclidean norm in the eight real Cayley-Dickson coordinates. -/
def Octonion.normSq (x : Octonion) : ℝ :=
  x.1.re^2 + x.1.imI^2 + x.1.imJ^2 + x.1.imK^2 +
  x.2.re^2 + x.2.imI^2 + x.2.imJ^2 + x.2.imK^2

instance : FiniteDimensional ℝ Octonion := by
  show FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ)
  infer_instance

theorem Octonion.finrank_eq_eight : Module.finrank ℝ Octonion = 8 := by
  show Module.finrank ℝ (Quaternion ℝ × Quaternion ℝ) = 8
  rw [Module.finrank_prod, Quaternion.finrank_eq_four]
