import AlbertAlgebra.Basic
import AlbertAlgebra.OctonionIdentities
import Mathlib.Algebra.Jordan.Basic

/-!
# The Jordan identity for H3(O)

Hermitian three-by-three matrices over the real octonions satisfy the Jordan
identity under the symmetrized matrix product.
-/

noncomputable section

namespace Albert

open Matrix

/-! ## A diagonal Jordan frame -/

/-- The diagonal matrix unit in position `(k, k)`. -/
def diagUnit (k : Fin 3) : Matrix (Fin 3) (Fin 3) Octonion :=
  fun i j => if i = k ∧ j = k then (1 : Octonion) else 0

@[simp] lemma diagUnit_apply (k i j : Fin 3) :
    diagUnit k i j = if i = k ∧ j = k then (1 : Octonion) else 0 := rfl

lemma diagUnit_hermitian (k : Fin 3) :
    (diagUnit k).conjTranspose = diagUnit k := by
  funext i j
  simp only [Matrix.conjTranspose_apply, diagUnit_apply]
  by_cases hij : i = k ∧ j = k
  · rw [if_pos hij, if_pos ⟨hij.2, hij.1⟩]
    exact Octonion.star_one
  · rw [if_neg hij]
    by_cases hji : j = k ∧ i = k
    · exfalso; exact hij ⟨hji.2, hji.1⟩
    · rw [if_neg hji]; exact Octonion.star_zero

/-- The `k`th diagonal idempotent in the standard Jordan frame. -/
def E (k : Fin 3) : H3Octonion := ⟨diagUnit k, diagUnit_hermitian k⟩

@[simp] lemma E_val (k : Fin 3) : (E k).1 = diagUnit k := rfl

private lemma diagUnit_mul_apply (j k i l : Fin 3) :
    (diagUnit j * diagUnit k) i l =
      if j = k ∧ i = j ∧ l = k then (1 : Octonion) else 0 := by
  rw [Matrix.mul_apply]

  have hsum :
      (Finset.univ.sum fun m : Fin 3 =>
        diagUnit j i m * diagUnit k m l)
      = if j = k ∧ i = j ∧ l = k then (1 : Octonion) else 0 := by
    by_cases hjk : j = k ∧ i = j ∧ l = k
    · obtain ⟨hjk1, hij, hlk⟩ := hjk
      rw [if_pos ⟨hjk1, hij, hlk⟩]

      rw [Finset.sum_eq_single j]
      · simp only [diagUnit_apply]
        simp [hij, hjk1, hlk]
      · intro b _ hbj
        simp only [diagUnit_apply]
        rw [if_neg (fun h => hbj h.2), zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    · rw [if_neg hjk]
      rw [Finset.sum_eq_zero]
      intro m _
      simp only [diagUnit_apply]
      by_cases h1 : i = j ∧ m = j
      · by_cases h2 : m = k ∧ l = k
        ·
          exfalso
          exact hjk ⟨h1.2.symm.trans h2.1, h1.1, h2.2⟩
        · rw [if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  exact hsum

private lemma diagUnit_mul_self (k : Fin 3) :
    diagUnit k * diagUnit k = diagUnit k := by
  funext i l
  rw [diagUnit_mul_apply]
  simp only [diagUnit_apply]
  by_cases h : i = k ∧ l = k
  · simp [h.1, h.2]
  · simp only [true_and]

private lemma diagUnit_mul_diff (j k : Fin 3) (hjk : j ≠ k) :
    diagUnit j * diagUnit k = 0 := by
  funext i l
  rw [diagUnit_mul_apply]
  rw [if_neg (fun h => hjk h.1)]
  rfl

lemma jordan_mul_val (A B : H3Octonion) :
    (A * B).1 = (1/2 : ℝ) • (A.1 * B.1 + B.1 * A.1) := rfl

theorem E_sq (k : Fin 3) : E k * E k = E k := by
  apply H3Octonion.ext
  rw [jordan_mul_val]
  simp only [E_val, diagUnit_mul_self]

  rw [show diagUnit k + diagUnit k = (2 : ℝ) • diagUnit k from (two_smul ℝ _).symm]
  rw [smul_smul, show (1/2 : ℝ) * 2 = 1 from by ring, one_smul]

theorem E_orthogonal (j k : Fin 3) (hjk : j ≠ k) : E j * E k = 0 := by
  apply H3Octonion.ext
  rw [jordan_mul_val]
  simp only [E_val, diagUnit_mul_diff j k hjk, diagUnit_mul_diff k j (Ne.symm hjk)]
  show (1/2 : ℝ) • (0 + 0 : Matrix (Fin 3) (Fin 3) Octonion) = (0 : H3Octonion).1
  rw [add_zero, smul_zero]; rfl

lemma sum_diagUnit_eq_one :
    diagUnit 0 + diagUnit 1 + diagUnit 2 = (1 : Matrix (Fin 3) (Fin 3) Octonion) := by
  funext i j
  simp only [Matrix.add_apply, diagUnit_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    fin_cases i <;> simp
  · rw [if_neg hij]
    have h0 : ¬ (i = 0 ∧ j = 0) := fun h => hij (h.1.trans h.2.symm)
    have h1 : ¬ (i = 1 ∧ j = 1) := fun h => hij (h.1.trans h.2.symm)
    have h2 : ¬ (i = 2 ∧ j = 2) := fun h => hij (h.1.trans h.2.symm)
    rw [if_neg h0, if_neg h1, if_neg h2]
    simp

theorem E_sum_eq_one : E 0 + E 1 + E 2 = (1 : H3Octonion) := by
  apply H3Octonion.ext
  show (E 0).1 + (E 1).1 + (E 2).1 = (1 : H3Octonion).1
  show diagUnit 0 + diagUnit 1 + diagUnit 2 = (1 : Matrix (Fin 3) (Fin 3) Octonion)
  exact sum_diagUnit_eq_one

theorem exists_three_orthogonal_idempotents :
    ∃ (f : Fin 3 → H3Octonion),
      (∀ k, f k * f k = f k) ∧
      (∀ j k, j ≠ k → f j * f k = 0) ∧
      (f 0 + f 1 + f 2 = (1 : H3Octonion)) := by
  refine ⟨E, E_sq, E_orthogonal, E_sum_eq_one⟩

theorem jordan_mul_one (A : H3Octonion) : A * (1 : H3Octonion) = A := by
  apply H3Octonion.ext
  rw [jordan_mul_val]
  show (1/2 : ℝ) • (A.1 * (1 : H3Octonion).1 + (1 : H3Octonion).1 * A.1) = A.1
  show (1/2 : ℝ) • (A.1 * (1 : Matrix (Fin 3) (Fin 3) Octonion)
                    + (1 : Matrix (Fin 3) (Fin 3) Octonion) * A.1) = A.1
  rw [Matrix.mul_one, Matrix.one_mul]
  rw [show A.1 + A.1 = (2 : ℝ) • A.1 from (two_smul ℝ _).symm]
  rw [smul_smul, show (1/2 : ℝ) * 2 = 1 from by ring, one_smul]

theorem jordan_mul_add (A B C : H3Octonion) : A * (B + C) = A * B + A * C := by
  apply H3Octonion.ext
  show ((1/2 : ℝ) • (A.1 * (B + C).1 + (B + C).1 * A.1) : Matrix (Fin 3) (Fin 3) Octonion)
      = ((1/2 : ℝ) • (A.1 * B.1 + B.1 * A.1) + (1/2 : ℝ) • (A.1 * C.1 + C.1 * A.1))
  show ((1/2 : ℝ) • (A.1 * (B.1 + C.1) + (B.1 + C.1) * A.1) : Matrix (Fin 3) (Fin 3) Octonion) = _
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [show A.1 * B.1 + A.1 * C.1 + (B.1 * A.1 + C.1 * A.1)
        = (A.1 * B.1 + B.1 * A.1) + (A.1 * C.1 + C.1 * A.1) from by abel]
  rw [smul_add]

theorem E_frame_maximal (F : H3Octonion)
    (h0 : F * E 0 = 0) (h1 : F * E 1 = 0) (h2 : F * E 2 = 0) :
    F = 0 := by
  have h_step : F * (E 0 + E 1 + E 2) = F := by
    rw [E_sum_eq_one, jordan_mul_one]
  rw [jordan_mul_add, jordan_mul_add] at h_step
  rw [h0, h1, h2, zero_add, zero_add] at h_step
  exact h_step.symm

theorem no_fourth_orthogonal_idempotent :
    ¬ ∃ F : H3Octonion, F ≠ 0 ∧ F * F = F ∧
      (∀ k : Fin 3, F * E k = 0) := by
  rintro ⟨F, hF_ne, _, hF_orth⟩
  exact hF_ne (E_frame_maximal F (hF_orth 0) (hF_orth 1) (hF_orth 2))

/-- A Hermitian octonion matrix whose off-diagonal entries vanish. -/
def H3Octonion.IsDiagonal (A : H3Octonion) : Prop :=
  (∀ i j, i ≠ j → A.1 i j = 0)
  ∧ (∀ i, A.1 i i = (A.1 i i).1.re • (1 : Octonion))

theorem E_isDiagonal (k : Fin 3) : H3Octonion.IsDiagonal (E k) := by
  refine ⟨?_, ?_⟩
  ·
    intro i j hij
    show diagUnit k i j = 0
    rw [diagUnit_apply]
    by_cases h : i = k ∧ j = k
    · exfalso; exact hij (h.1.trans h.2.symm)
    · rw [if_neg h]
  ·
    intro i
    show diagUnit k i i = (diagUnit k i i).1.re • (1 : Octonion)
    rw [diagUnit_apply]
    by_cases h : i = k ∧ i = k
    · rw [if_pos h]
      show (1 : Octonion) = (1 : Octonion).1.re • (1 : Octonion)
      rw [show (1 : Octonion).1.re = 1 from rfl, one_smul]
    · rw [if_neg h]
      show (0 : Octonion) = (0 : Octonion).1.re • (1 : Octonion)
      rw [show (0 : Octonion).1.re = 0 from rfl, zero_smul]

private lemma real_octonion_mul_left (r : ℝ) (b : Octonion) :
    (r • (1 : Octonion)) * b = r • b := by
  rw [Octonion.smul_mul, one_mul]

private lemma real_octonion_mul_right (r : ℝ) (b : Octonion) :
    b * (r • (1 : Octonion)) = r • b := by
  rw [Octonion.mul_smul, mul_one]

instance : IsScalarTower ℝ Octonion Octonion where
  smul_assoc r x y := by
    show (r • x) * y = r • (x * y)
    exact Octonion.smul_mul r x y

instance : SMulCommClass ℝ Octonion Octonion where
  smul_comm r x y := by
    show r • (x * y) = x * (r • y)
    rw [Octonion.mul_smul]

theorem jordan_prod_diagonal_apply (A B : H3Octonion) (hA : H3Octonion.IsDiagonal A)
    (i j : Fin 3) :
    (A * B).1 i j =
      (((A.1 i i).1.re + (A.1 j j).1.re) * (1/2 : ℝ)) • B.1 i j := by

  show ((1/2 : ℝ) • (A.1 * B.1 + B.1 * A.1)) i j = _
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]

  have h_AB : (Finset.univ.sum fun k => A.1 i k * B.1 k j) = A.1 i i * B.1 i j := by
    rw [Finset.sum_eq_single i]
    · intro k _ hk_ne_i
      rw [hA.1 i k (Ne.symm hk_ne_i), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

  have h_BA : (Finset.univ.sum fun k => B.1 i k * A.1 k j) = B.1 i j * A.1 j j := by
    rw [Finset.sum_eq_single j]
    · intro k _ hk_ne_j
      rw [hA.1 k j hk_ne_j, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [h_AB, h_BA]

  have h1 : A.1 i i * B.1 i j = (A.1 i i).1.re • B.1 i j := by
    conv_lhs => rw [hA.2 i]
    exact real_octonion_mul_left _ _
  have h2 : B.1 i j * A.1 j j = (A.1 j j).1.re • B.1 i j := by
    conv_lhs => rw [hA.2 j]
    exact real_octonion_mul_right _ _
  rw [h1, h2, ← add_smul, smul_smul, mul_comm]

theorem jordanSq_diagonal_isDiagonal (x : H3Octonion) (hx : H3Octonion.IsDiagonal x) :
    H3Octonion.IsDiagonal (x * x) := by
  refine ⟨?_, ?_⟩
  ·
    intro i j hij
    rw [jordan_prod_diagonal_apply x x hx i j]
    rw [hx.1 i j hij, smul_zero]
  ·

    intro i
    have h_ij := jordan_prod_diagonal_apply x x hx i i

    set r := (x.1 i i).1.re with hr_def

    have h_expand : (x * x).1 i i = ((r + r) * (1/2) * r) • (1 : Octonion) := by
      rw [h_ij]

      conv_lhs => rw [hx.2 i]
      rw [smul_smul]
    rw [h_expand]

    have h_re : (((r + r) * (1/2) * r) • (1 : Octonion)).1.re = (r + r) * (1/2) * r := by
      show ((r + r) * (1/2) * r) • (1 : Octonion).1.re = _
      rw [show (1 : Octonion).1.re = (1 : ℝ) from rfl]
      show ((r + r) * (1/2) * r) * (1 : ℝ) = _
      ring
    rw [h_re]

theorem jordan_mul_comm (A B : H3Octonion) : A * B = B * A := by
  apply H3Octonion.ext
  show ((1/2 : ℝ) • (A.1 * B.1 + B.1 * A.1)) = ((1/2 : ℝ) • (B.1 * A.1 + A.1 * B.1))
  rw [add_comm]

theorem jordan_identity_of_diagonal (x y : H3Octonion) (hx : H3Octonion.IsDiagonal x) :
    (x * x * y) * x = (x * x) * (y * x) := by
  have hxx : H3Octonion.IsDiagonal (x * x) := jordanSq_diagonal_isDiagonal x hx

  rw [jordan_mul_comm (x * x * y) x]
  rw [jordan_mul_comm y x]

  apply H3Octonion.ext
  funext i j

  rw [jordan_prod_diagonal_apply x (x * x * y) hx i j]
  rw [jordan_prod_diagonal_apply (x * x) (x * y) hxx i j]

  rw [jordan_prod_diagonal_apply (x * x) y hxx i j]
  rw [jordan_prod_diagonal_apply x y hx i j]

  rw [smul_smul, smul_smul, mul_comm]

theorem jordan_identity_at_E (k : Fin 3) (y : H3Octonion) :
    (E k * E k * y) * E k = (E k * E k) * (y * E k) :=
  jordan_identity_of_diagonal (E k) y (E_isDiagonal k)

/-! ## Octonion and matrix associators -/

/-- The associator `(a * b) * c - a * (b * c)` of three octonions. -/
def octAssoc (a b c : Octonion) : Octonion := (a * b) * c - a * (b * c)

@[simp] lemma octAssoc_eq (a b c : Octonion) :
    octAssoc a b c = (a * b) * c - a * (b * c) := rfl

theorem octAssoc_alt_left (a b : Octonion) : octAssoc a a b = 0 := by
  show (a * a) * b - a * (a * b) = 0
  rw [Octonion.left_alternative, sub_self]

theorem octAssoc_alt_right (a b : Octonion) : octAssoc a b b = 0 := by
  show (a * b) * b - a * (b * b) = 0
  rw [Octonion.right_alternative, sub_self]

theorem octAssoc_flex (a b : Octonion) : octAssoc a b a = 0 := by
  show (a * b) * a - a * (b * a) = 0
  rw [Octonion.flexible, sub_self]

theorem octAssoc_star_mid_same (a b : Octonion) : octAssoc a (star b) b = 0 := by
  show (a * star b) * b - a * (star b * b) = 0
  rw [Octonion.mul_star_mul, sub_self]

theorem octAssoc_star_right_same (a b : Octonion) : octAssoc a b (star b) = 0 := by
  show (a * b) * star b - a * (b * star b) = 0
  rw [Octonion.mul_mul_star, sub_self]

theorem octAssoc_b_starb_a (a b : Octonion) : octAssoc b (star b) a = 0 := by
  show (b * star b) * a - b * (star b * a) = 0
  rw [Octonion.mul_star_assoc, sub_self]

theorem octAssoc_starb_b_a (a b : Octonion) : octAssoc (star b) b a = 0 := by
  show (star b * b) * a - star b * (b * a) = 0
  rw [Octonion.star_mul_assoc, sub_self]

theorem octAssoc_one_left (a b : Octonion) : octAssoc 1 a b = 0 := by
  unfold octAssoc
  rw [one_mul, one_mul, sub_self]

theorem octAssoc_one_mid (a b : Octonion) : octAssoc a 1 b = 0 := by
  unfold octAssoc
  rw [mul_one, one_mul, sub_self]

theorem octAssoc_one_right (a b : Octonion) : octAssoc a b 1 = 0 := by
  unfold octAssoc
  rw [mul_one, mul_one, sub_self]

theorem octAssoc_zero_left (a b : Octonion) : octAssoc 0 a b = 0 := by
  unfold octAssoc
  simp

theorem octAssoc_zero_mid (a b : Octonion) : octAssoc a 0 b = 0 := by
  unfold octAssoc
  simp

theorem octAssoc_zero_right (a b : Octonion) : octAssoc a b 0 = 0 := by
  unfold octAssoc
  simp

theorem octAssoc_smul_one_left (r : ℝ) (a b : Octonion) :
    octAssoc (r • (1 : Octonion)) a b = 0 := by
  show (r • (1 : Octonion)) * a * b - (r • (1 : Octonion)) * (a * b) = 0
  rw [smul_one_mul, smul_one_mul, smul_mul_assoc, sub_self]

theorem octAssoc_smul_one_mid (r : ℝ) (a b : Octonion) :
    octAssoc a (r • (1 : Octonion)) b = 0 := by
  show a * (r • (1 : Octonion)) * b - a * ((r • (1 : Octonion)) * b) = 0
  rw [mul_smul_one, smul_mul_assoc, smul_one_mul, mul_smul_comm, sub_self]

theorem octAssoc_smul_one_right (r : ℝ) (a b : Octonion) :
    octAssoc a b (r • (1 : Octonion)) = 0 := by
  show a * b * (r • (1 : Octonion)) - a * (b * (r • (1 : Octonion))) = 0
  rw [mul_smul_one, mul_smul_one, mul_smul_comm, sub_self]

lemma Octonion.eq_smul_one_of_star_self (u : Octonion) (h : star u = u) :
    u = (u.1.re : ℝ) • (1 : Octonion) := by
  have h_fst : u.1 = star u.1 := by
    have := congrArg Prod.fst h.symm
    simpa [Octonion.star_fst] using this
  have h_snd : u.2 = -u.2 := by
    have := congrArg Prod.snd h.symm
    simpa [Octonion.star_snd] using this
  have h_snd_zero : u.2 = 0 := by
    have eq1 : u.2 + u.2 = 0 := by
      nth_rewrite 2 [h_snd]
      exact add_neg_cancel u.2
    have h2 : (2 : ℝ) • u.2 = 0 := by rw [two_smul]; exact eq1
    have h2ne : (2 : ℝ) ≠ 0 := by norm_num
    exact (smul_eq_zero_iff_right h2ne).mp h2
  apply Octonion.ext'
  ·
    apply Quaternion.ext
    · simp [Octonion.fst_smul, Octonion.fst_one]
    ·
      have := congrArg (fun q => q.imI) h_fst
      simp [Quaternion.imI_star] at this
      simp [Octonion.fst_smul, Octonion.fst_one]
      linarith
    · have := congrArg (fun q => q.imJ) h_fst
      simp [Quaternion.imJ_star] at this
      simp [Octonion.fst_smul, Octonion.fst_one]
      linarith
    · have := congrArg (fun q => q.imK) h_fst
      simp [Quaternion.imK_star] at this
      simp [Octonion.fst_smul, Octonion.fst_one]
      linarith
  · simp [Octonion.snd_smul, Octonion.snd_one, h_snd_zero]

theorem octAssoc_of_star_self_left (u a b : Octonion) (h : star u = u) :
    octAssoc u a b = 0 := by
  rw [Octonion.eq_smul_one_of_star_self u h]
  exact octAssoc_smul_one_left _ _ _

theorem octAssoc_of_star_self_mid (u a b : Octonion) (h : star u = u) :
    octAssoc a u b = 0 := by
  rw [Octonion.eq_smul_one_of_star_self u h]
  exact octAssoc_smul_one_mid _ _ _

theorem octAssoc_of_star_self_right (u a b : Octonion) (h : star u = u) :
    octAssoc a b u = 0 := by
  rw [Octonion.eq_smul_one_of_star_self u h]
  exact octAssoc_smul_one_right _ _ _

theorem octAssoc_add_left (a₁ a₂ b c : Octonion) :
    octAssoc (a₁ + a₂) b c = octAssoc a₁ b c + octAssoc a₂ b c := by
  show ((a₁ + a₂) * b) * c - (a₁ + a₂) * (b * c)
      = ((a₁ * b) * c - a₁ * (b * c)) + ((a₂ * b) * c - a₂ * (b * c))
  rw [add_mul, add_mul, add_mul]
  abel

theorem octAssoc_add_mid (a b₁ b₂ c : Octonion) :
    octAssoc a (b₁ + b₂) c = octAssoc a b₁ c + octAssoc a b₂ c := by
  show (a * (b₁ + b₂)) * c - a * ((b₁ + b₂) * c)
      = ((a * b₁) * c - a * (b₁ * c)) + ((a * b₂) * c - a * (b₂ * c))
  rw [mul_add, add_mul]
  rw [add_mul]
  rw [mul_add]
  abel

theorem octAssoc_add_right (a b c₁ c₂ : Octonion) :
    octAssoc a b (c₁ + c₂) = octAssoc a b c₁ + octAssoc a b c₂ := by
  show (a * b) * (c₁ + c₂) - a * (b * (c₁ + c₂))
      = ((a * b) * c₁ - a * (b * c₁)) + ((a * b) * c₂ - a * (b * c₂))
  rw [mul_add, mul_add, mul_add]
  abel

theorem octAssoc_antisymm_12 (a b c : Octonion) :
    octAssoc a b c + octAssoc b a c = 0 := by
  have h := octAssoc_alt_left (a + b) c
  rw [octAssoc_add_left, octAssoc_add_mid, octAssoc_add_mid] at h
  rw [octAssoc_alt_left, octAssoc_alt_left, zero_add, add_zero] at h
  exact h

theorem octAssoc_antisymm_23 (a b c : Octonion) :
    octAssoc a b c + octAssoc a c b = 0 := by
  have h := octAssoc_alt_right a (b + c)
  rw [octAssoc_add_mid, octAssoc_add_right, octAssoc_add_right] at h
  rw [octAssoc_alt_right, octAssoc_alt_right, zero_add, add_zero] at h
  exact h

theorem octAssoc_antisymm_13 (a b c : Octonion) :
    octAssoc a b c + octAssoc c b a = 0 := by
  have h := octAssoc_flex (a + c) b
  rw [octAssoc_add_left, octAssoc_add_right, octAssoc_add_right] at h
  rw [octAssoc_flex, octAssoc_flex, zero_add, add_zero] at h
  exact h

theorem octAssoc_swap_12 (a b c : Octonion) : octAssoc a b c = -octAssoc b a c :=
  eq_neg_of_add_eq_zero_left (octAssoc_antisymm_12 a b c)

theorem octAssoc_swap_23 (a b c : Octonion) : octAssoc a b c = -octAssoc a c b :=
  eq_neg_of_add_eq_zero_left (octAssoc_antisymm_23 a b c)

theorem octAssoc_swap_13 (a b c : Octonion) : octAssoc a b c = -octAssoc c b a :=
  eq_neg_of_add_eq_zero_left (octAssoc_antisymm_13 a b c)

theorem octAssoc_cyclic (a b c : Octonion) :
    octAssoc a b c = octAssoc b c a := by

  rw [octAssoc_swap_12]
  rw [octAssoc_swap_23 b a c]
  rw [neg_neg]

/-- The associator of three octonion matrices under matrix multiplication. -/
def matAssoc (A B C : Matrix (Fin 3) (Fin 3) Octonion) :
    Matrix (Fin 3) (Fin 3) Octonion :=
  A * B * C - A * (B * C)

theorem matAssoc_apply (A B C : Matrix (Fin 3) (Fin 3) Octonion) (i j : Fin 3) :
    (matAssoc A B C) i j = Finset.univ.sum (fun k : Fin 3 =>
      Finset.univ.sum (fun l : Fin 3 => octAssoc (A i k) (B k l) (C l j))) := by
  show ((A * B) * C - A * (B * C)) i j = _
  rw [Matrix.sub_apply]

  show (Finset.univ.sum fun l => (A * B) i l * C l j) -
       (Finset.univ.sum fun k => A i k * (B * C) k j)
     = _
  rw [show (fun l => (A * B) i l * C l j) =
        (fun l => (Finset.univ.sum fun k => A i k * B k l) * C l j) from rfl]
  rw [show (fun k => A i k * (B * C) k j) =
        (fun k => A i k * (Finset.univ.sum fun l => B k l * C l j)) from rfl]

  have h1 : (Finset.univ.sum fun l => (Finset.univ.sum fun k => A i k * B k l) * C l j)
          = Finset.univ.sum (fun l =>
              Finset.univ.sum (fun k => A i k * B k l * C l j)) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_mul]
  have h2 : (Finset.univ.sum fun k => A i k * (Finset.univ.sum fun l => B k l * C l j))
          = Finset.univ.sum (fun k =>
              Finset.univ.sum (fun l => A i k * (B k l * C l j))) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
  rw [h1, h2]

  rw [Finset.sum_comm]

  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  show (A i k * B k l) * C l j - A i k * (B k l * C l j) = octAssoc (A i k) (B k l) (C l j)
  rfl

theorem jordan_square_apply (A : H3Octonion) : (A * A).1 = A.1 * A.1 := by
  show (1/2 : ℝ) • (A.1 * A.1 + A.1 * A.1) = A.1 * A.1
  rw [show A.1 * A.1 + A.1 * A.1 = (2 : ℝ) • (A.1 * A.1) from (two_smul ℝ _).symm]
  rw [smul_smul, show (1/2 : ℝ) * 2 = 1 from by ring, one_smul]

theorem octonion_jordan_term_one (x y : Octonion) :
    (x * x * y) * x = (x * x) * (y * x) := by
  rw [Octonion.left_alternative]
  rw [Octonion.flexible]
  rw [Octonion.flexible]
  rw [← Octonion.left_alternative]

theorem octonion_jordan_term_two (x y : Octonion) :
    (y * (x * x)) * x = (y * x) * (x * x) := by
  rw [← Octonion.right_alternative]
  exact Octonion.right_alternative x (y * x)

theorem octonion_jordan_term_three (x y : Octonion) :
    x * (x * x * y) = (x * x) * (x * y) := by
  rw [Octonion.left_alternative]
  rw [Octonion.left_alternative]

theorem octonion_jordan_term_four (x y : Octonion) :
    x * (y * (x * x)) = (x * y) * (x * x) := by
  rw [← Octonion.right_alternative]
  rw [Octonion.moufang_middle]
  rw [Octonion.flexible]

theorem jordan_identity_octonion (x y : Octonion) :
    (x * x * y) * x + (y * (x * x)) * x + x * (x * x * y) + x * (y * (x * x))
      = (x * x) * (y * x) + (x * x) * (x * y)
        + (y * x) * (x * x) + (x * y) * (x * x) := by
  rw [octonion_jordan_term_one, octonion_jordan_term_two, octonion_jordan_term_three,
      octonion_jordan_term_four]
  abel

theorem octonion_moufang_left_polarized (x x' y z : Octonion) :
    (x * y * x') * z + (x' * y * x) * z = x * (y * (x' * z)) + x' * (y * (x * z)) := by
  have h := Octonion.moufang_left (x + x') y z
  have hx := Octonion.moufang_left x y z
  have hx' := Octonion.moufang_left x' y z
  have e1 : (x + x') * y = x * y + x' * y := add_mul _ _ _
  have e2 : (x + x') * z = x * z + x' * z := add_mul _ _ _
  rw [e1] at h
  have e3 : (x * y + x' * y) * (x + x') = x * y * x + x * y * x' + x' * y * x + x' * y * x' := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [e3] at h
  have e4 : (x * y * x + x * y * x' + x' * y * x + x' * y * x') * z
          = (x * y * x) * z + (x * y * x') * z + (x' * y * x) * z + (x' * y * x') * z := by
    rw [add_mul, add_mul, add_mul]
  rw [e4] at h
  rw [e2] at h
  have e5 : y * (x * z + x' * z) = y * (x * z) + y * (x' * z) := mul_add _ _ _
  rw [e5] at h
  have e6 : (x + x') * (y * (x * z) + y * (x' * z))
          = x * (y * (x * z)) + x * (y * (x' * z)) + x' * (y * (x * z)) + x' * (y * (x' * z)) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [e6] at h
  rw [hx, hx'] at h
  have goal_form :
      ((x * y * x') * z + (x' * y * x) * z) -
      (x * (y * (x' * z)) + x' * (y * (x * z))) = 0 := by
    have rearr :
        ((x * y * x') * z + (x' * y * x) * z) -
        (x * (y * (x' * z)) + x' * (y * (x * z)))
        = (x * (y * (x * z)) + (x * y * x') * z + (x' * y * x) * z + x' * (y * (x' * z)))
          - (x * (y * (x * z)) + x * (y * (x' * z)) + x' * (y * (x * z)) + x' * (y * (x' * z))) := by
      abel
    rw [rearr, h, sub_self]
  exact sub_eq_zero.mp goal_form

theorem octonion_moufang_right_polarized (x x' y z : Octonion) :
    z * (x * y * x') + z * (x' * y * x) = z * x * y * x' + z * x' * y * x := by
  have h := Octonion.moufang_right (x + x') y z
  have hx := Octonion.moufang_right x y z
  have hx' := Octonion.moufang_right x' y z
  have e1 : (x + x') * y = x * y + x' * y := add_mul _ _ _
  rw [e1] at h
  have e2 : (x * y + x' * y) * (x + x') = x * y * x + x * y * x' + x' * y * x + x' * y * x' := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [e2] at h
  have e3 : z * (x * y * x + x * y * x' + x' * y * x + x' * y * x')
          = z * (x * y * x) + z * (x * y * x') + z * (x' * y * x) + z * (x' * y * x') := by
    rw [mul_add, mul_add, mul_add]
  rw [e3] at h
  have e4 : z * (x + x') = z * x + z * x' := mul_add _ _ _
  rw [e4] at h
  have e5 : (z * x + z * x') * y = z * x * y + z * x' * y := add_mul _ _ _
  rw [e5] at h
  have e6 : (z * x * y + z * x' * y) * (x + x')
          = z * x * y * x + z * x * y * x' + z * x' * y * x + z * x' * y * x' := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [e6] at h
  rw [hx, hx'] at h
  have goal_form :
      (z * (x * y * x') + z * (x' * y * x)) -
      (z * x * y * x' + z * x' * y * x) = 0 := by
    have rearr :
        (z * (x * y * x') + z * (x' * y * x)) -
        (z * x * y * x' + z * x' * y * x)
        = (z * x * y * x + z * (x * y * x') + z * (x' * y * x) + z * x' * y * x')
          - (z * x * y * x + z * x * y * x' + z * x' * y * x + z * x' * y * x') := by
      abel
    rw [rearr, h, sub_self]
  exact sub_eq_zero.mp goal_form

theorem octAssoc_triple_x (x y z : Octonion) :
    octAssoc (x * y) z x = octAssoc x y z * x := by
  unfold octAssoc
  rw [Octonion.moufang_middle x y z]
  rw [sub_mul]

theorem octAssoc_x_xy_z (x y z : Octonion) :
    octAssoc x (x * y) z = octAssoc x y z * x := by
  rw [show octAssoc x (x * y) z = octAssoc (x * y) z x from (octAssoc_cyclic x (x*y) z)]
  exact octAssoc_triple_x x y z

theorem octAssoc_x_y_xz (x y z : Octonion) :
    octAssoc x y (x * z) = octAssoc x y z * x := by
  have h1 : octAssoc (x * y) x z = -octAssoc x y (x * z) := by
    unfold octAssoc
    show (x * y * x) * z - (x * y) * (x * z) = -((x * y) * (x * z) - x * (y * (x * z)))
    rw [Octonion.moufang_left x y z]
    abel
  have h3 : octAssoc (x * y) x z = -(octAssoc x y z * x) := by
    rw [octAssoc_swap_12 (x*y) x z]
    rw [octAssoc_x_xy_z]
  rw [← neg_neg (octAssoc x y (x * z))]
  rw [← h1, h3, neg_neg]

theorem octAssoc_chain (x y z t : Octonion) :
    octAssoc (x * y) z t - octAssoc x (y * z) t + octAssoc x y (z * t)
      = x * octAssoc y z t + octAssoc x y z * t := by
  unfold octAssoc
  rw [mul_sub, sub_mul]
  abel

theorem octAssoc_x_y_za (a y z : Octonion) :
    octAssoc a y (z * a) = a * octAssoc a y z := by
  have h := octAssoc_chain a y z a
  have h_flex : octAssoc a (y * z) a = 0 := octAssoc_flex a (y * z)
  have h_triple := octAssoc_triple_x a y z

  have h_cyc : octAssoc y z a = octAssoc a y z := by
    have := octAssoc_cyclic a y z
    exact this.symm
  rw [h_triple, h_flex, h_cyc] at h

  have key : octAssoc a y (z * a) - a * octAssoc a y z = 0 := by
    have h' : octAssoc a y z * a - 0 + octAssoc a y (z * a)
            = a * octAssoc a y z + octAssoc a y z * a := h
    have rearr : octAssoc a y (z * a) - a * octAssoc a y z
               = (octAssoc a y z * a - 0 + octAssoc a y (z * a))
                 - (a * octAssoc a y z + octAssoc a y z * a) := by abel
    rw [rearr, h', sub_self]
  exact sub_eq_zero.mp key

theorem octAssoc_comm_specific (a y z : Octonion) :
    octAssoc a y (a * z - z * a) = octAssoc a y z * a - a * octAssoc a y z := by

  show (a * y) * (a * z - z * a) - a * (y * (a * z - z * a))
       = octAssoc a y z * a - a * octAssoc a y z

  rw [mul_sub, mul_sub, mul_sub]

  show (a * y) * (a * z) - (a * y) * (z * a) - (a * (y * (a * z)) - a * (y * (z * a)))
       = octAssoc a y z * a - a * octAssoc a y z
  have h1 : (a * y) * (a * z) - a * (y * (a * z)) = octAssoc a y (a * z) := rfl
  have h2 : (a * y) * (z * a) - a * (y * (z * a)) = octAssoc a y (z * a) := rfl
  have h3 : octAssoc a y (a * z) = octAssoc a y z * a := octAssoc_x_y_xz a y z
  have h4 : octAssoc a y (z * a) = a * octAssoc a y z := octAssoc_x_y_za a y z

  have rearr : (a * y) * (a * z) - (a * y) * (z * a) - (a * (y * (a * z)) - a * (y * (z * a)))
            = ((a * y) * (a * z) - a * (y * (a * z))) - ((a * y) * (z * a) - a * (y * (z * a))) := by
    abel
  rw [rearr, h1, h2, h3, h4]

theorem octAssoc_pm1_form (x x' y z : Octonion) :
    octAssoc (x * y) x' z + octAssoc x y (x' * z)
      + octAssoc (x' * y) x z + octAssoc x' y (x * z) = 0 := by
  have h := octonion_moufang_left_polarized x x' y z
  unfold octAssoc
  have h' : (x * y * x') * z + (x' * y * x) * z
         - (x * (y * (x' * z)) + x' * (y * (x * z))) = 0 := by
    rw [h]; abel
  have goal_rearr :
      ((x * y) * x') * z - (x * y) * (x' * z) + ((x * y) * (x' * z) - x * (y * (x' * z))) +
      (((x' * y) * x) * z - (x' * y) * (x * z)) + ((x' * y) * (x * z) - x' * (y * (x * z)))
      = (x * y * x') * z + (x' * y * x) * z
         - (x * (y * (x' * z)) + x' * (y * (x * z))) := by abel
  rw [goal_rearr, h']

theorem octAssoc_x_y_xz_polarized (x x' y z : Octonion) :
    octAssoc x y (x' * z) + octAssoc x' y (x * z)
      = octAssoc x y z * x' + octAssoc x' y z * x := by
  have h := octAssoc_x_y_xz (x + x') y z
  have hx := octAssoc_x_y_xz x y z
  have hx' := octAssoc_x_y_xz x' y z
  rw [add_mul] at h
  rw [octAssoc_add_left] at h
  rw [octAssoc_add_right] at h
  rw [octAssoc_add_right] at h
  rw [octAssoc_add_left] at h
  rw [add_mul, mul_add, mul_add] at h
  rw [hx, hx'] at h
  have key : (octAssoc x y (x' * z) + octAssoc x' y (x * z))
         - (octAssoc x y z * x' + octAssoc x' y z * x) = 0 := by
    have h_sub : (octAssoc x y (x' * z) + octAssoc x' y (x * z))
           - (octAssoc x y z * x' + octAssoc x' y z * x)
           = (octAssoc x y z * x + octAssoc x y (x' * z)
             + (octAssoc x' y (x * z) + octAssoc x' y z * x'))
             - (octAssoc x y z * x + octAssoc x y z * x'
             + (octAssoc x' y z * x + octAssoc x' y z * x')) := by abel
    rw [h_sub, sub_eq_zero.mpr h]
  exact sub_eq_zero.mp key

theorem octAssoc_x_y_za_polarized (a a' y z : Octonion) :
    octAssoc a y (z * a') + octAssoc a' y (z * a)
      = a * octAssoc a' y z + a' * octAssoc a y z := by
  have h := octAssoc_x_y_za (a + a') y z
  have ha := octAssoc_x_y_za a y z
  have ha' := octAssoc_x_y_za a' y z
  rw [mul_add] at h
  rw [octAssoc_add_left] at h
  rw [octAssoc_add_right] at h
  rw [octAssoc_add_right] at h
  rw [octAssoc_add_left] at h
  rw [mul_add, add_mul, add_mul] at h
  rw [ha, ha'] at h
  have key : (octAssoc a y (z * a') + octAssoc a' y (z * a))
         - (a * octAssoc a' y z + a' * octAssoc a y z) = 0 := by
    have h_sub : (octAssoc a y (z * a') + octAssoc a' y (z * a))
           - (a * octAssoc a' y z + a' * octAssoc a y z)
           = (a * octAssoc a y z + octAssoc a y (z * a')
             + (octAssoc a' y (z * a) + a' * octAssoc a' y z))
             - (a * octAssoc a y z + a' * octAssoc a y z
             + (a * octAssoc a' y z + a' * octAssoc a' y z)) := by abel
    rw [h_sub, sub_eq_zero.mpr h]
  exact sub_eq_zero.mp key

private theorem octAssoc_square_split (x y z : Octonion) :
    (x * (x * y)) * z - x * (x * (y * z))
      = octAssoc x (x * y) z + x * octAssoc x y z := by
  unfold octAssoc
  rw [mul_sub]
  abel

theorem octAssoc_xsq_y_z (x y z : Octonion) :
    octAssoc (x * x) y z = x * octAssoc x y z + octAssoc x y z * x := by
  show (x * x * y) * z - (x * x) * (y * z) = x * octAssoc x y z + octAssoc x y z * x
  rw [Octonion.left_alternative, Octonion.left_alternative]
  rw [octAssoc_square_split]
  rw [octAssoc_x_xy_z]
  abel

theorem octAssoc_teich_sum (x x' y z : Octonion) :
    octAssoc (x * x') y z + octAssoc (x' * x) y z
      = x * octAssoc x' y z + x' * octAssoc x y z
        + octAssoc x y z * x' + octAssoc x' y z * x := by
  have h := octAssoc_xsq_y_z (x + x') y z
  have hx := octAssoc_xsq_y_z x y z
  have hx' := octAssoc_xsq_y_z x' y z
  have h_sq : (x + x') * (x + x') = x * x + x * x' + x' * x + x' * x' := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [h_sq] at h
  simp only [octAssoc_add_left] at h
  rw [hx, hx'] at h
  simp only [mul_add, add_mul] at h

  have h_sub : (octAssoc (x * x') y z + octAssoc (x' * x) y z
         - (x * octAssoc x' y z + x' * octAssoc x y z
            + octAssoc x y z * x' + octAssoc x' y z * x))
      = (x * octAssoc x y z + octAssoc x y z * x + octAssoc (x * x') y z
          + octAssoc (x' * x) y z + (x' * octAssoc x' y z + octAssoc x' y z * x'))
        - (x * octAssoc x y z + x' * octAssoc x y z
          + (x * octAssoc x' y z + x' * octAssoc x' y z)
          + (octAssoc x y z * x + octAssoc x' y z * x
            + (octAssoc x y z * x' + octAssoc x' y z * x'))) := by abel
  have key : octAssoc (x * x') y z + octAssoc (x' * x) y z
         - (x * octAssoc x' y z + x' * octAssoc x y z
            + octAssoc x y z * x' + octAssoc x' y z * x) = 0 := by
    rw [h_sub, sub_eq_zero.mpr h]
  exact sub_eq_zero.mp key

theorem octAssoc_triple_x_polarized (x x' y z : Octonion) :
    octAssoc (x * y) z x' + octAssoc (x' * y) z x =
      octAssoc x y z * x' + octAssoc x' y z * x := by
  have h := octAssoc_triple_x (x + x') y z

  have hx := octAssoc_triple_x x y z
  have hx' := octAssoc_triple_x x' y z

  rw [add_mul] at h
  rw [octAssoc_add_left] at h

  rw [octAssoc_add_right, octAssoc_add_right] at h

  rw [octAssoc_add_left] at h
  rw [add_mul] at h
  rw [mul_add, mul_add] at h

  rw [hx, hx'] at h

  have h_flat : octAssoc x y z * x + octAssoc (x * y) z x' + octAssoc (x' * y) z x
                  + octAssoc x' y z * x'
              = octAssoc x y z * x + octAssoc x y z * x' + octAssoc x' y z * x
                  + octAssoc x' y z * x' := by
    rw [show octAssoc x y z * x + octAssoc (x * y) z x' + octAssoc (x' * y) z x
          + octAssoc x' y z * x'
          = octAssoc x y z * x + octAssoc (x * y) z x'
            + (octAssoc (x' * y) z x + octAssoc x' y z * x') from by abel]
    rw [show octAssoc x y z * x + octAssoc x y z * x' + octAssoc x' y z * x
          + octAssoc x' y z * x'
          = octAssoc x y z * x + octAssoc x y z * x'
            + (octAssoc x' y z * x + octAssoc x' y z * x') from by abel]
    exact h

  have goal_form :
      (octAssoc (x * y) z x' + octAssoc (x' * y) z x) -
      (octAssoc x y z * x' + octAssoc x' y z * x) = 0 := by
    have rearr :
        (octAssoc (x * y) z x' + octAssoc (x' * y) z x) -
        (octAssoc x y z * x' + octAssoc x' y z * x)
        = (octAssoc x y z * x + octAssoc (x * y) z x' + octAssoc (x' * y) z x + octAssoc x' y z * x')
          - (octAssoc x y z * x + octAssoc x y z * x' + octAssoc x' y z * x + octAssoc x' y z * x') := by
      abel
    rw [rearr, h_flat, sub_self]
  exact sub_eq_zero.mp goal_form

theorem octonion_moufang_middle_polarized (a a' b c : Octonion) :
    (a * b) * (c * a') + (a' * b) * (c * a) = a * (b * c) * a' + a' * (b * c) * a := by
  have h := Octonion.moufang_middle (a + a') b c
  have ha := Octonion.moufang_middle a b c
  have ha' := Octonion.moufang_middle a' b c
  have h_expand :
      (a * b) * (c * a) + (a * b) * (c * a') + (a' * b) * (c * a) + (a' * b) * (c * a')
      = a * (b * c) * a + a * (b * c) * a' + a' * (b * c) * a + a' * (b * c) * a' := by
    rw [show (a + a') * b = a * b + a' * b from add_mul _ _ _] at h
    rw [show c * (a + a') = c * a + c * a' from mul_add _ _ _] at h
    rw [show (a + a') * (b * c) = a * (b * c) + a' * (b * c) from add_mul _ _ _] at h
    have e4 : (a * b + a' * b) * (c * a + c * a')
          = (a * b) * (c * a) + (a * b) * (c * a') + (a' * b) * (c * a) + (a' * b) * (c * a') := by
      rw [add_mul, mul_add, mul_add]; abel
    have e5 : (a * (b * c) + a' * (b * c)) * (a + a')
          = a * (b * c) * a + a * (b * c) * a' + a' * (b * c) * a + a' * (b * c) * a' := by
      rw [add_mul, mul_add, mul_add]; abel
    rw [e4, e5] at h
    exact h
  rw [ha, ha'] at h_expand

  have goal_form :
      ((a * b) * (c * a') + (a' * b) * (c * a)) -
      (a * (b * c) * a' + a' * (b * c) * a) = 0 := by
    have rearr :
        ((a * b) * (c * a') + (a' * b) * (c * a)) -
        (a * (b * c) * a' + a' * (b * c) * a)
        = (a * (b * c) * a + (a * b) * (c * a') + (a' * b) * (c * a) + a' * (b * c) * a')
          - (a * (b * c) * a + a * (b * c) * a' + a' * (b * c) * a + a' * (b * c) * a') := by
      abel
    rw [rearr, h_expand, sub_self]
  exact sub_eq_zero.mp goal_form

/-! ## Reduction of the Jordan identity to associator sums -/

theorem jordan_lhs_matrix (x y : H3Octonion) :
    ((x * x * y) * x).1 =
      (1/4 : ℝ) • ((x.1 * x.1 * y.1) * x.1
                  + (y.1 * (x.1 * x.1)) * x.1
                  + x.1 * (x.1 * x.1 * y.1)
                  + x.1 * (y.1 * (x.1 * x.1))) := by
  show (1/2 : ℝ) • ((x * x * y).1 * x.1 + x.1 * (x * x * y).1) = _
  rw [show (x * x * y).1 = (1/2 : ℝ) • ((x * x).1 * y.1 + y.1 * (x * x).1) from rfl]
  rw [jordan_square_apply]

  rw [smul_mul_assoc, mul_smul_comm]
  rw [← smul_add, smul_smul]
  rw [show (1/2 : ℝ) * (1/2 : ℝ) = (1/4 : ℝ) from by norm_num]
  congr 1
  rw [add_mul, Matrix.mul_add]
  abel

theorem jordan_rhs_matrix (x y : H3Octonion) :
    ((x * x) * (y * x)).1 =
      (1/4 : ℝ) • ((x.1 * x.1) * (y.1 * x.1)
                  + (x.1 * x.1) * (x.1 * y.1)
                  + (y.1 * x.1) * (x.1 * x.1)
                  + (x.1 * y.1) * (x.1 * x.1)) := by
  show (1/2 : ℝ) • ((x * x).1 * (y * x).1 + (y * x).1 * (x * x).1) = _
  rw [jordan_square_apply]
  rw [show (y * x).1 = (1/2 : ℝ) • (y.1 * x.1 + x.1 * y.1) from rfl]
  rw [mul_smul_comm, smul_mul_assoc]
  rw [← smul_add, smul_smul]
  rw [show (1/2 : ℝ) * (1/2 : ℝ) = (1/4 : ℝ) from by norm_num]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul]
  abel

theorem matrix_associator_expansion_one (X Y : Matrix (Fin 3) (Fin 3) Octonion) :
    (X * X * Y) * X - (X * X) * (Y * X) = matAssoc (X * X) Y X := by
  unfold matAssoc

  rfl

theorem matrix_associator_expansion_two (X Y : Matrix (Fin 3) (Fin 3) Octonion) :
    (Y * (X * X)) * X - (Y * X) * (X * X)
      = matAssoc Y (X * X) X - matAssoc Y X (X * X) + Y * matAssoc X X X := by
  unfold matAssoc
  rw [mul_sub]

  abel

theorem matrix_associator_expansion_three (X Y : Matrix (Fin 3) (Fin 3) Octonion) :
    X * (X * X * Y) - (X * X) * (X * Y)
      = -matAssoc X (X * X) Y + matAssoc (X * X) X Y - matAssoc X X X * Y := by
  unfold matAssoc

  rw [sub_mul]
  abel

theorem matrix_associator_expansion_four (X Y : Matrix (Fin 3) (Fin 3) Octonion) :
    X * (Y * (X * X)) - (X * Y) * (X * X) = -matAssoc X Y (X * X) := by
  unfold matAssoc

  abel

theorem jordan_identity_diff_matrix_form (x y : H3Octonion) :
    ((x * x * y) * x).1 - ((x * x) * (y * x)).1
      = (1/4 : ℝ) • (matAssoc (x.1 * x.1) y.1 x.1
                   + matAssoc (x.1 * x.1) x.1 y.1
                   + matAssoc y.1 (x.1 * x.1) x.1
                   - matAssoc y.1 x.1 (x.1 * x.1)
                   - matAssoc x.1 (x.1 * x.1) y.1
                   - matAssoc x.1 y.1 (x.1 * x.1)
                   + y.1 * matAssoc x.1 x.1 x.1
                   - matAssoc x.1 x.1 x.1 * y.1) := by
  rw [jordan_lhs_matrix, jordan_rhs_matrix]
  rw [← smul_sub]
  congr 1

  have h1 := matrix_associator_expansion_one x.1 y.1
  have h2 := matrix_associator_expansion_two x.1 y.1
  have h3 := matrix_associator_expansion_three x.1 y.1
  have h4 := matrix_associator_expansion_four x.1 y.1

  have heq : (x.1 * x.1 * y.1) * x.1 + (y.1 * (x.1 * x.1)) * x.1
             + x.1 * (x.1 * x.1 * y.1) + x.1 * (y.1 * (x.1 * x.1))
             - ((x.1 * x.1) * (y.1 * x.1) + (x.1 * x.1) * (x.1 * y.1)
                + (y.1 * x.1) * (x.1 * x.1) + (x.1 * y.1) * (x.1 * x.1))
           = ((x.1 * x.1 * y.1) * x.1 - (x.1 * x.1) * (y.1 * x.1))
             + ((y.1 * (x.1 * x.1)) * x.1 - (y.1 * x.1) * (x.1 * x.1))
             + (x.1 * (x.1 * x.1 * y.1) - (x.1 * x.1) * (x.1 * y.1))
             + (x.1 * (y.1 * (x.1 * x.1)) - (x.1 * y.1) * (x.1 * x.1)) := by abel
  rw [heq, h1, h2, h3, h4]
  abel

theorem jordan_identity_of_matAssoc_sum
    (x y : H3Octonion)
    (h_sum : matAssoc (x.1 * x.1) y.1 x.1
           + matAssoc (x.1 * x.1) x.1 y.1
           + matAssoc y.1 (x.1 * x.1) x.1
           - matAssoc y.1 x.1 (x.1 * x.1)
           - matAssoc x.1 (x.1 * x.1) y.1
           - matAssoc x.1 y.1 (x.1 * x.1)
           + y.1 * matAssoc x.1 x.1 x.1
           - matAssoc x.1 x.1 x.1 * y.1 = 0) :
    (x * x * y) * x = (x * x) * (y * x) := by
  apply H3Octonion.ext
  have h := jordan_identity_diff_matrix_form x y

  rw [h_sum, smul_zero] at h
  exact sub_eq_zero.mp h

/-! ## Associators of Hermitian matrices -/

lemma H3Octonion.entry_hermitian (x : H3Octonion) (i j : Fin 3) :
    x.1 i j = star (x.1 j i) := by
  have := congr_fun₂ x.2 i j
  rw [Matrix.conjTranspose_apply] at this
  exact this.symm

lemma H3Octonion.diag_star (x : H3Octonion) (i : Fin 3) : star (x.1 i i) = x.1 i i :=
  (H3Octonion.entry_hermitian x i i).symm

theorem matAssoc_self_01_of_hermitian (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 0 1 = 0 := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]

  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1

  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_left _ _ _ h00]
  rw [octAssoc_of_star_self_left _ _ _ h00]
  rw [octAssoc_of_star_self_left _ _ _ h00]

  rw [octAssoc_flex]

  rw [octAssoc_of_star_self_mid _ _ _ h11]

  rw [octAssoc_star_right_same]

  rw [octAssoc_b_starb_a]

  rw [octAssoc_of_star_self_right _ _ _ h11]

  rw [octAssoc_of_star_self_mid _ _ _ h22]

  abel

theorem matAssoc_self_02_of_hermitian (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 0 2 = 0 := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]
  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1
  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_left _ _ _ h00]
  rw [octAssoc_of_star_self_left _ _ _ h00]
  rw [octAssoc_of_star_self_left _ _ _ h00]

  rw [octAssoc_b_starb_a]

  rw [octAssoc_of_star_self_mid _ _ _ h11]

  rw [octAssoc_of_star_self_right _ _ _ h22]

  rw [octAssoc_flex]

  rw [octAssoc_star_mid_same]

  rw [octAssoc_of_star_self_mid _ _ _ h22]
  abel

theorem matAssoc_self_10_of_hermitian (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 1 0 = 0 := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]
  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1
  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_right _ _ _ h00]

  rw [octAssoc_flex]

  rw [octAssoc_star_right_same]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_of_star_self_right _ _ _ h00]

  rw [octAssoc_b_starb_a]

  rw [octAssoc_of_star_self_mid _ _ _ h22]
  abel

theorem matAssoc_self_12_of_hermitian (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 1 2 = 0 := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]
  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1
  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_mid _ _ _ h00]

  rw [octAssoc_starb_b_a]

  rw [octAssoc_of_star_self_right _ _ _ h22]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_star_mid_same]

  rw [octAssoc_flex]

  rw [octAssoc_of_star_self_mid _ _ _ h22]
  abel

theorem matAssoc_self_20_of_hermitian (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 2 0 = 0 := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]
  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1
  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_mid _ _ _ h00]

  rw [octAssoc_star_right_same]

  rw [octAssoc_flex]

  rw [octAssoc_of_star_self_right _ _ _ h00]

  rw [octAssoc_of_star_self_mid _ _ _ h11]

  rw [octAssoc_starb_b_a]

  rw [octAssoc_of_star_self_left _ _ _ h22]

  rw [octAssoc_of_star_self_left _ _ _ h22]

  rw [octAssoc_of_star_self_left _ _ _ h22]
  abel

theorem matAssoc_self_21_of_hermitian (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 2 1 = 0 := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]
  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1
  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_mid _ _ _ h00]

  rw [octAssoc_of_star_self_right _ _ _ h11]

  rw [octAssoc_starb_b_a]

  rw [octAssoc_star_mid_same]

  rw [octAssoc_of_star_self_mid _ _ _ h11]

  rw [octAssoc_flex]

  rw [octAssoc_of_star_self_left _ _ _ h22]

  rw [octAssoc_of_star_self_left _ _ _ h22]

  rw [octAssoc_of_star_self_left _ _ _ h22]
  abel

theorem matAssoc_self_off_diagonal_hermitian (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) :
    matAssoc x.1 x.1 x.1 i j = 0 := by
  fin_cases i <;> fin_cases j <;> (first | (exfalso; exact hij rfl) | skip)
  · exact matAssoc_self_01_of_hermitian x
  · exact matAssoc_self_02_of_hermitian x
  · exact matAssoc_self_10_of_hermitian x
  · exact matAssoc_self_12_of_hermitian x
  · exact matAssoc_self_20_of_hermitian x
  · exact matAssoc_self_21_of_hermitian x

theorem matAssoc_self_00_reduction (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 0 0
      = octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2))
        + octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1)) := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]
  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1
  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_left _ _ _ h00]

  rw [octAssoc_of_star_self_left _ _ _ h00]

  rw [octAssoc_of_star_self_left _ _ _ h00]

  rw [octAssoc_of_star_self_right _ _ _ h00]

  rw [octAssoc_of_star_self_mid _ _ _ h11]

  rw [octAssoc_of_star_self_right _ _ _ h00]

  rw [octAssoc_of_star_self_mid _ _ _ h22]
  abel

theorem matAssoc_self_11_reduction (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 1 1
      = octAssoc (star (x.1 0 1)) (x.1 0 2) (star (x.1 1 2))
        + octAssoc (x.1 1 2) (star (x.1 0 2)) (x.1 0 1) := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]
  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1
  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_mid _ _ _ h00]

  rw [octAssoc_of_star_self_right _ _ _ h11]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_of_star_self_left _ _ _ h11]

  rw [octAssoc_of_star_self_right _ _ _ h11]

  rw [octAssoc_of_star_self_mid _ _ _ h22]
  abel

theorem matAssoc_self_22_reduction (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 2 2
      = octAssoc (star (x.1 0 2)) (x.1 0 1) (x.1 1 2)
        + octAssoc (star (x.1 1 2)) (star (x.1 0 1)) (x.1 0 2) := by
  rw [matAssoc_apply]
  simp only [Fin.sum_univ_three]
  have h00 := H3Octonion.diag_star x 0
  have h11 := H3Octonion.diag_star x 1
  have h22 := H3Octonion.diag_star x 2
  have h10 := H3Octonion.entry_hermitian x 1 0
  have h20 := H3Octonion.entry_hermitian x 2 0
  have h21 := H3Octonion.entry_hermitian x 2 1
  rw [h10, h20, h21]

  rw [octAssoc_of_star_self_mid _ _ _ h00]

  rw [octAssoc_of_star_self_right _ _ _ h22]

  rw [octAssoc_of_star_self_mid _ _ _ h11]

  rw [octAssoc_of_star_self_right _ _ _ h22]

  rw [octAssoc_of_star_self_left _ _ _ h22]

  rw [octAssoc_of_star_self_left _ _ _ h22]

  rw [octAssoc_of_star_self_left _ _ _ h22]
  abel

theorem matAssoc_self_diag_equal_00_11 (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 0 0 = matAssoc x.1 x.1 x.1 1 1 := by
  rw [matAssoc_self_00_reduction, matAssoc_self_11_reduction]

  rw [octAssoc_cyclic (star (x.1 0 1)) (x.1 0 2) (star (x.1 1 2))]
  rw [octAssoc_cyclic (x.1 1 2) (star (x.1 0 2)) (x.1 0 1)]
  rw [octAssoc_cyclic (star (x.1 0 2)) (x.1 0 1) (x.1 1 2)]
  abel

theorem matAssoc_self_diag_equal_00_22 (x : H3Octonion) :
    matAssoc x.1 x.1 x.1 0 0 = matAssoc x.1 x.1 x.1 2 2 := by
  rw [matAssoc_self_00_reduction, matAssoc_self_22_reduction]

  rw [octAssoc_cyclic (x.1 0 1) (x.1 1 2) (star (x.1 0 2))]
  rw [octAssoc_cyclic (x.1 1 2) (star (x.1 0 2)) (x.1 0 1)]
  rw [octAssoc_cyclic (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))]

theorem matAssoc_self_diag_all_equal (x : H3Octonion) (i j : Fin 3) :
    matAssoc x.1 x.1 x.1 i i = matAssoc x.1 x.1 x.1 j j := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact matAssoc_self_diag_equal_00_11 x
  · exact matAssoc_self_diag_equal_00_22 x
  · exact (matAssoc_self_diag_equal_00_11 x).symm
  · rfl
  · exact (matAssoc_self_diag_equal_00_11 x).symm.trans (matAssoc_self_diag_equal_00_22 x)
  · exact (matAssoc_self_diag_equal_00_22 x).symm
  · exact (matAssoc_self_diag_equal_00_22 x).symm.trans (matAssoc_self_diag_equal_00_11 x)
  · rfl

theorem matAssoc_self_scalar_identity (x : H3Octonion) (i j : Fin 3) :
    matAssoc x.1 x.1 x.1 i j
      = if i = j then matAssoc x.1 x.1 x.1 0 0 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    exact matAssoc_self_diag_all_equal x i 0
  · rw [if_neg hij]
    exact matAssoc_self_off_diagonal_hermitian x i j hij

private lemma octAssoc_y_real_left (y : H3Octonion) (hy : ∀ i j, star (y.1 i j) = y.1 i j)
    (i k : Fin 3) (a b : Octonion) : octAssoc (y.1 i k) a b = 0 :=
  octAssoc_of_star_self_left (y.1 i k) a b (hy i k)

private lemma octAssoc_y_real_mid (y : H3Octonion) (hy : ∀ i j, star (y.1 i j) = y.1 i j)
    (k l : Fin 3) (a b : Octonion) : octAssoc a (y.1 k l) b = 0 :=
  octAssoc_of_star_self_mid (y.1 k l) a b (hy k l)

private lemma octAssoc_y_real_right (y : H3Octonion) (hy : ∀ i j, star (y.1 i j) = y.1 i j)
    (l j : Fin 3) (a b : Octonion) : octAssoc a b (y.1 l j) = 0 :=
  octAssoc_of_star_self_right (y.1 l j) a b (hy l j)

theorem matAssoc_left_zero_of_y_real (y : H3Octonion) (hy : ∀ i j, star (y.1 i j) = y.1 i j)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) : matAssoc y.1 A B = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.zero_apply, matAssoc_apply]
  simp only [Fin.sum_univ_three, octAssoc_y_real_left y hy, add_zero]

theorem matAssoc_mid_zero_of_y_real (y : H3Octonion) (hy : ∀ i j, star (y.1 i j) = y.1 i j)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) : matAssoc A y.1 B = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.zero_apply, matAssoc_apply]
  simp only [Fin.sum_univ_three, octAssoc_y_real_mid y hy, add_zero]

theorem matAssoc_right_zero_of_y_real (y : H3Octonion) (hy : ∀ i j, star (y.1 i j) = y.1 i j)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) : matAssoc A B y.1 = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.zero_apply, matAssoc_apply]
  simp only [Fin.sum_univ_three, octAssoc_y_real_right y hy, add_zero]

private lemma star_octAssoc_reversed (a b c : Octonion) :
    star (octAssoc a b c) = -octAssoc (star c) (star b) (star a) := by
  unfold octAssoc

  rw [star_sub]

  rw [Octonion.star_mul (a * b) c]
  rw [Octonion.star_mul a b]

  rw [Octonion.star_mul a (b * c)]
  rw [Octonion.star_mul b c]

  abel

theorem matAssoc_self_00_pure_imaginary (x : H3Octonion) :
    star (matAssoc x.1 x.1 x.1 0 0) = -(matAssoc x.1 x.1 x.1 0 0) := by
  rw [matAssoc_self_00_reduction]
  set p := x.1 0 1
  set q := x.1 0 2
  set r := x.1 1 2
  show star (octAssoc p r (star q) + octAssoc q (star r) (star p))
       = -(octAssoc p r (star q) + octAssoc q (star r) (star p))
  rw [star_add]

  rw [star_octAssoc_reversed p r (star q)]
  rw [star_star]

  rw [star_octAssoc_reversed q (star r) (star p)]
  rw [star_star, star_star]
  abel

theorem matAssoc_self_equals_scalar_one_smul (x : H3Octonion) :
    matAssoc x.1 x.1 x.1
      = (matAssoc x.1 x.1 x.1 0 0) • (1 : Matrix (Fin 3) (Fin 3) Octonion) := by
  apply Matrix.ext
  intro i j
  rw [matAssoc_self_scalar_identity x i j]
  rw [Matrix.smul_apply]
  by_cases hij : i = j
  · rw [if_pos hij]
    subst hij
    rw [Matrix.one_apply_eq]

    rw [smul_eq_mul, mul_one]
  · rw [if_neg hij]
    rw [Matrix.one_apply_ne hij]

    rw [smul_eq_mul, mul_zero]

theorem jordan_identity_of_x_real (x y : H3Octonion) (hx : ∀ i j, star (x.1 i j) = x.1 i j) :
    (x * x * y) * x = (x * x) * (y * x) := by

  have hxx : ∀ i j, star ((x * x).1 i j) = (x * x).1 i j := by
    intro i j
    rw [jordan_square_apply]
    rw [Matrix.mul_apply]
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro k _

    rw [Octonion.star_mul, hx, hx]

    obtain ⟨r1, hr1⟩ : ∃ r, x.1 i k = r • (1 : Octonion) :=
      ⟨_, Octonion.eq_smul_one_of_star_self _ (hx i k)⟩
    obtain ⟨r2, hr2⟩ : ∃ r, x.1 k j = r • (1 : Octonion) :=
      ⟨_, Octonion.eq_smul_one_of_star_self _ (hx k j)⟩
    rw [hr1, hr2]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_one, mul_comm r1 r2]
  apply jordan_identity_of_matAssoc_sum

  rw [show matAssoc (x.1 * x.1) y.1 x.1 = matAssoc (x * x).1 y.1 x.1 by rw [jordan_square_apply]]
  rw [matAssoc_left_zero_of_y_real (x * x) hxx y.1 x.1]

  rw [show matAssoc (x.1 * x.1) x.1 y.1 = matAssoc (x * x).1 x.1 y.1 by rw [jordan_square_apply]]
  rw [matAssoc_left_zero_of_y_real (x * x) hxx x.1 y.1]

  rw [matAssoc_right_zero_of_y_real x hx y.1 (x.1 * x.1)]

  rw [show matAssoc y.1 x.1 (x.1 * x.1) = matAssoc y.1 x.1 (x * x).1 by rw [jordan_square_apply]]
  rw [matAssoc_right_zero_of_y_real (x * x) hxx y.1 x.1]

  rw [show matAssoc x.1 (x.1 * x.1) y.1 = matAssoc x.1 (x * x).1 y.1 by rw [jordan_square_apply]]
  rw [matAssoc_mid_zero_of_y_real (x * x) hxx x.1 y.1]

  rw [matAssoc_left_zero_of_y_real x hx y.1 (x.1 * x.1)]

  have h_self_assoc : matAssoc x.1 x.1 x.1 = 0 := by
    apply Matrix.ext
    intro i j
    rw [matAssoc_apply]
    simp only [Fin.sum_univ_three, octAssoc_y_real_left x hx, add_zero,
               Matrix.zero_apply]
  rw [h_self_assoc, Matrix.mul_zero, Matrix.zero_mul]
  abel

/-! ## Diagonal and off-diagonal reductions -/

private lemma mul_matrix_diag_apply (M : Matrix (Fin 3) (Fin 3) Octonion)
    (hM : ∀ i j, i ≠ j → M i j = 0)
    (A : Matrix (Fin 3) (Fin 3) Octonion) (i j : Fin 3) :
    (A * M) i j = A i j * M j j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · intro k _ hk
    rw [hM k j hk, mul_zero]
  · exact fun h => absurd (Finset.mem_univ j) h

private lemma matrix_diag_mul_apply (M : Matrix (Fin 3) (Fin 3) Octonion)
    (hM : ∀ i j, i ≠ j → M i j = 0)
    (A : Matrix (Fin 3) (Fin 3) Octonion) (i j : Fin 3) :
    (M * A) i j = M i i * A i j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rw [hM i k (Ne.symm hk), zero_mul]
  · exact fun h => absurd (Finset.mem_univ i) h

private lemma y_real_matrix_scalar_commute (y : H3Octonion) (hy : ∀ i j, star (y.1 i j) = y.1 i j)
    (M : Matrix (Fin 3) (Fin 3) Octonion)
    (hM_diag : ∀ i j, i ≠ j → M i j = 0)
    (hM_eq : ∀ i j, M i i = M j j) :
    y.1 * M = M * y.1 := by
  apply Matrix.ext
  intro i j
  rw [mul_matrix_diag_apply M hM_diag y.1 i j, matrix_diag_mul_apply M hM_diag y.1 i j]

  rw [hM_eq j 0, hM_eq i 0]

  obtain ⟨r, hr⟩ : ∃ r, y.1 i j = r • (1 : Octonion) :=
    ⟨_, Octonion.eq_smul_one_of_star_self _ (hy i j)⟩
  rw [hr, smul_one_mul, mul_smul_one]

theorem jordan_identity_of_y_real (x y : H3Octonion) (hy : ∀ i j, star (y.1 i j) = y.1 i j) :
    (x * x * y) * x = (x * x) * (y * x) := by
  apply jordan_identity_of_matAssoc_sum
  rw [matAssoc_mid_zero_of_y_real y hy (x.1 * x.1) x.1]
  rw [matAssoc_right_zero_of_y_real y hy (x.1 * x.1) x.1]
  rw [matAssoc_left_zero_of_y_real y hy (x.1 * x.1) x.1]
  rw [matAssoc_left_zero_of_y_real y hy x.1 (x.1 * x.1)]
  rw [matAssoc_right_zero_of_y_real y hy x.1 (x.1 * x.1)]
  rw [matAssoc_mid_zero_of_y_real y hy x.1 (x.1 * x.1)]
  have hM_diag : ∀ i j, i ≠ j → matAssoc x.1 x.1 x.1 i j = 0 :=
    matAssoc_self_off_diagonal_hermitian x
  have hM_eq : ∀ i j, matAssoc x.1 x.1 x.1 i i = matAssoc x.1 x.1 x.1 j j :=
    matAssoc_self_diag_all_equal x
  rw [y_real_matrix_scalar_commute y hy (matAssoc x.1 x.1 x.1) hM_diag hM_eq]
  abel

private lemma octAssoc_y_entry_left_zero (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (i k : Fin 3) (a b : Octonion) : octAssoc (y.1 i k) a b = 0 := by
  by_cases hik : i = k
  · subst hik
    obtain ⟨r, hr⟩ : ∃ r, y.1 i i = r • (1 : Octonion) := ⟨(y.1 i i).1.re, hy.2 i⟩
    rw [hr]; exact octAssoc_smul_one_left _ _ _
  · rw [hy.1 i k hik]; exact octAssoc_zero_left _ _

private lemma octAssoc_y_entry_mid_zero (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (k l : Fin 3) (a b : Octonion) : octAssoc a (y.1 k l) b = 0 := by
  by_cases hkl : k = l
  · subst hkl
    obtain ⟨r, hr⟩ : ∃ r, y.1 k k = r • (1 : Octonion) := ⟨(y.1 k k).1.re, hy.2 k⟩
    rw [hr]; exact octAssoc_smul_one_mid _ _ _
  · rw [hy.1 k l hkl]; exact octAssoc_zero_mid _ _

private lemma octAssoc_y_entry_right_zero (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (l j : Fin 3) (a b : Octonion) : octAssoc a b (y.1 l j) = 0 := by
  by_cases hlj : l = j
  · subst hlj
    obtain ⟨r, hr⟩ : ∃ r, y.1 l l = r • (1 : Octonion) := ⟨(y.1 l l).1.re, hy.2 l⟩
    rw [hr]; exact octAssoc_smul_one_right _ _ _
  · rw [hy.1 l j hlj]; exact octAssoc_zero_right _ _

theorem matAssoc_left_zero_of_y_diagonal (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matAssoc y.1 A B = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.zero_apply, matAssoc_apply]
  simp only [Fin.sum_univ_three, octAssoc_y_entry_left_zero y hy, add_zero]

theorem matAssoc_mid_zero_of_y_diagonal (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matAssoc A y.1 B = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.zero_apply, matAssoc_apply]
  simp only [Fin.sum_univ_three, octAssoc_y_entry_mid_zero y hy, add_zero]

theorem matAssoc_right_zero_of_y_diagonal (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matAssoc A B y.1 = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.zero_apply, matAssoc_apply]
  simp only [Fin.sum_univ_three, octAssoc_y_entry_right_zero y hy, add_zero]

private lemma mul_y_diag_apply_left (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (M : Matrix (Fin 3) (Fin 3) Octonion) (i j : Fin 3) :
    (y.1 * M) i j = y.1 i i * M i j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rw [hy.1 i k (Ne.symm hk), zero_mul]
  · intro hnin
    exact absurd (Finset.mem_univ i) hnin

private lemma mul_y_diag_apply_right (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (M : Matrix (Fin 3) (Fin 3) Octonion) (i j : Fin 3) :
    (M * y.1) i j = M i j * y.1 j j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · intro k _ hk
    rw [hy.1 k j hk, mul_zero]
  · intro hnin
    exact absurd (Finset.mem_univ j) hnin

private lemma y_diag_matrix_diag_commute (y : H3Octonion) (hy : H3Octonion.IsDiagonal y)
    (M : Matrix (Fin 3) (Fin 3) Octonion)
    (hM : ∀ i j, i ≠ j → M i j = 0) :
    y.1 * M = M * y.1 := by
  ext i j
  rw [mul_y_diag_apply_left y hy M i j, mul_y_diag_apply_right y hy M i j]
  by_cases hij : i = j
  · subst hij
    obtain ⟨r, hr⟩ : ∃ r, y.1 i i = r • (1 : Octonion) := ⟨(y.1 i i).1.re, hy.2 i⟩
    rw [hr, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  · rw [hM i j hij, mul_zero, zero_mul]

theorem jordan_identity_of_y_diagonal (x y : H3Octonion) (hy : H3Octonion.IsDiagonal y) :
    (x * x * y) * x = (x * x) * (y * x) := by
  apply jordan_identity_of_matAssoc_sum

  rw [matAssoc_mid_zero_of_y_diagonal y hy (x.1 * x.1) x.1]
  rw [matAssoc_right_zero_of_y_diagonal y hy (x.1 * x.1) x.1]
  rw [matAssoc_left_zero_of_y_diagonal y hy (x.1 * x.1) x.1]
  rw [matAssoc_left_zero_of_y_diagonal y hy x.1 (x.1 * x.1)]
  rw [matAssoc_right_zero_of_y_diagonal y hy x.1 (x.1 * x.1)]
  rw [matAssoc_mid_zero_of_y_diagonal y hy x.1 (x.1 * x.1)]

  have hM : ∀ i j, i ≠ j → matAssoc x.1 x.1 x.1 i j = 0 :=
    matAssoc_self_off_diagonal_hermitian x
  rw [y_diag_matrix_diag_commute y hy (matAssoc x.1 x.1 x.1) hM]
  abel

theorem jordan_identity_of_real_entries (x y : H3Octonion)
    (h : (∀ i j, star (x.1 i j) = x.1 i j) ∨ (∀ i j, star (y.1 i j) = y.1 i j)) :
    (x * x * y) * x = (x * x) * (y * x) := by
  rcases h with hx | hy
  · exact jordan_identity_of_x_real x y hx
  · exact jordan_identity_of_y_real x y hy

theorem jordan_identity_of_diagonal_arg (x y : H3Octonion)
    (h : H3Octonion.IsDiagonal x ∨ H3Octonion.IsDiagonal y) :
    (x * x * y) * x = (x * x) * (y * x) := by
  rcases h with hx | hy
  · exact jordan_identity_of_diagonal x y hx
  · exact jordan_identity_of_y_diagonal x y hy

theorem jordan_add_mul (A B C : H3Octonion) : (A + B) * C = A * C + B * C := by
  calc (A + B) * C
      = C * (A + B) := jordan_mul_comm _ _
    _ = C * A + C * B := jordan_mul_add _ _ _
    _ = A * C + B * C := by rw [jordan_mul_comm C A, jordan_mul_comm C B]

theorem jordan_identity_of_add_y (x y₁ y₂ : H3Octonion)
    (h₁ : (x * x * y₁) * x = (x * x) * (y₁ * x))
    (h₂ : (x * x * y₂) * x = (x * x) * (y₂ * x)) :
    (x * x * (y₁ + y₂)) * x = (x * x) * ((y₁ + y₂) * x) := by

  rw [jordan_mul_add, jordan_add_mul, jordan_add_mul, jordan_mul_add]
  rw [h₁, h₂]

/-- A Hermitian octonion matrix with zero diagonal. -/
def H3Octonion.IsPureOffDiag (A : H3Octonion) : Prop := ∀ i, A.1 i i = 0

theorem jordan_identity_of_diag_plus_rank_one
    (x y_D y_ij : H3Octonion)
    (h_D : (x * x * y_D) * x = (x * x) * (y_D * x))
    (h_ij : (x * x * y_ij) * x = (x * x) * (y_ij * x)) :
    (x * x * (y_D + y_ij)) * x = (x * x) * ((y_D + y_ij) * x) :=
  jordan_identity_of_add_y x y_D y_ij h_D h_ij

theorem jordan_identity_of_four_summands
    (x y_D y_01 y_02 y_12 : H3Octonion)
    (h_D : (x * x * y_D) * x = (x * x) * (y_D * x))
    (h_01 : (x * x * y_01) * x = (x * x) * (y_01 * x))
    (h_02 : (x * x * y_02) * x = (x * x) * (y_02 * x))
    (h_12 : (x * x * y_12) * x = (x * x) * (y_12 * x)) :
    (x * x * (y_D + y_01 + y_02 + y_12)) * x
      = (x * x) * ((y_D + y_01 + y_02 + y_12) * x) := by
  apply jordan_identity_of_add_y
  · apply jordan_identity_of_add_y
    · apply jordan_identity_of_add_y x y_D y_01 h_D h_01
    · exact h_02
  · exact h_12

/-- The diagonal part of a Hermitian octonion matrix. -/
def H3Octonion.diagPart (y : H3Octonion) : H3Octonion :=
  ⟨fun i j => if i = j then y.1 i j else 0, by
    funext i j
    simp only [Matrix.conjTranspose_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact H3Octonion.diag_star y i
    · have hji : j ≠ i := fun h => hij h.symm
      simp only [if_neg hij, if_neg hji]
      exact star_zero _⟩

/-- The off-diagonal part of a Hermitian octonion matrix. -/
def H3Octonion.offDiagPart (y : H3Octonion) : H3Octonion :=
  ⟨fun i j => if i = j then 0 else y.1 i j, by
    funext i j
    simp only [Matrix.conjTranspose_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact star_zero _
    · have hji : j ≠ i := fun h => hij h.symm
      simp only [if_neg hij, if_neg hji]
      exact (H3Octonion.entry_hermitian y i j).symm⟩

@[simp] lemma H3Octonion.diagPart_apply (y : H3Octonion) (i j : Fin 3) :
    (H3Octonion.diagPart y).1 i j = if i = j then y.1 i j else 0 := rfl

@[simp] lemma H3Octonion.offDiagPart_apply (y : H3Octonion) (i j : Fin 3) :
    (H3Octonion.offDiagPart y).1 i j = if i = j then 0 else y.1 i j := rfl

theorem H3Octonion.diagPart_plus_offDiagPart (y : H3Octonion) :
    H3Octonion.diagPart y + H3Octonion.offDiagPart y = y := by
  apply H3Octonion.ext
  funext i j
  show (H3Octonion.diagPart y).1 i j + (H3Octonion.offDiagPart y).1 i j = y.1 i j
  rw [H3Octonion.diagPart_apply, H3Octonion.offDiagPart_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, add_zero]
  · rw [if_neg hij, if_neg hij, zero_add]

theorem H3Octonion.diagPart_isDiagonal (y : H3Octonion) :
    H3Octonion.IsDiagonal (H3Octonion.diagPart y) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    rw [H3Octonion.diagPart_apply, if_neg hij]
  · intro i
    rw [H3Octonion.diagPart_apply, if_pos rfl]

    exact Octonion.eq_smul_one_of_star_self (y.1 i i) (H3Octonion.diag_star y i)

theorem H3Octonion.offDiagPart_isPureOffDiag (y : H3Octonion) :
    H3Octonion.IsPureOffDiag (H3Octonion.offDiagPart y) := by
  intro i
  rw [H3Octonion.offDiagPart_apply, if_pos rfl]

theorem H3Octonion.offDiagPart_of_isPureOffDiag (y : H3Octonion)
    (hy : H3Octonion.IsPureOffDiag y) : H3Octonion.offDiagPart y = y := by
  apply H3Octonion.ext
  funext i j
  rw [H3Octonion.offDiagPart_apply]
  by_cases hij : i = j
  · rw [if_pos hij, hij]; exact (hy j).symm
  · rw [if_neg hij]

theorem jordan_identity_of_offDiag_case
    (x : H3Octonion)
    (h_offDiag : ∀ (y' : H3Octonion), H3Octonion.IsPureOffDiag y' →
      (x * x * y') * x = (x * x) * (y' * x)) :
    ∀ y : H3Octonion, (x * x * y) * x = (x * x) * (y * x) := by
  intro y
  rw [← H3Octonion.diagPart_plus_offDiagPart y]
  apply jordan_identity_of_add_y
  · exact jordan_identity_of_y_diagonal x _ (H3Octonion.diagPart_isDiagonal y)
  · exact h_offDiag _ (H3Octonion.offDiagPart_isPureOffDiag y)

/-- The conjugation-invariant part of the off-diagonal entries. -/
noncomputable def H3Octonion.offDiagRealPart (y : H3Octonion) : H3Octonion :=
  ⟨fun i j => if i = j then 0
              else (1/2 : ℝ) • (y.1 i j + star (y.1 i j)), by
    funext i j
    simp only [Matrix.conjTranspose_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact star_zero _
    · have hji : j ≠ i := fun h => hij h.symm
      simp only [if_neg hij, if_neg hji]
      rw [star_smul, star_trivial, star_add, star_star]
      rw [H3Octonion.entry_hermitian y j i, star_star]⟩

/-- The conjugation-anti-invariant part of the off-diagonal entries. -/
noncomputable def H3Octonion.offDiagImagPart (y : H3Octonion) : H3Octonion :=
  ⟨fun i j => if i = j then 0
              else (1/2 : ℝ) • (y.1 i j - star (y.1 i j)), by
    funext i j
    simp only [Matrix.conjTranspose_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact star_zero _
    · have hji : j ≠ i := fun h => hij h.symm
      simp only [if_neg hij, if_neg hji]
      rw [star_smul, star_trivial, star_sub, star_star]
      rw [H3Octonion.entry_hermitian y j i, star_star]⟩

@[simp] lemma H3Octonion.offDiagRealPart_apply (y : H3Octonion) (i j : Fin 3) :
    (H3Octonion.offDiagRealPart y).1 i j =
      if i = j then 0 else (1/2 : ℝ) • (y.1 i j + star (y.1 i j)) := rfl

@[simp] lemma H3Octonion.offDiagImagPart_apply (y : H3Octonion) (i j : Fin 3) :
    (H3Octonion.offDiagImagPart y).1 i j =
      if i = j then 0 else (1/2 : ℝ) • (y.1 i j - star (y.1 i j)) := rfl

theorem H3Octonion.offDiagPart_decompose (y : H3Octonion) :
    H3Octonion.offDiagRealPart y + H3Octonion.offDiagImagPart y = H3Octonion.offDiagPart y := by
  apply H3Octonion.ext
  funext i j
  show (H3Octonion.offDiagRealPart y).1 i j + (H3Octonion.offDiagImagPart y).1 i j =
       (H3Octonion.offDiagPart y).1 i j
  rw [H3Octonion.offDiagRealPart_apply, H3Octonion.offDiagImagPart_apply,
      H3Octonion.offDiagPart_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, if_pos hij, add_zero]
  · rw [if_neg hij, if_neg hij, if_neg hij]
    rw [← smul_add, show (1/2 : ℝ) • ((y.1 i j + star (y.1 i j)) +
                           (y.1 i j - star (y.1 i j))) =
                     (1/2 : ℝ) • ((2 : ℝ) • y.1 i j) from by
      congr 1; rw [two_smul]; abel]
    rw [smul_smul, show (1/2 : ℝ) * 2 = 1 from by norm_num, one_smul]

theorem H3Octonion.offDiagRealPart_star_self (y : H3Octonion) :
    ∀ i j, star ((H3Octonion.offDiagRealPart y).1 i j) =
           (H3Octonion.offDiagRealPart y).1 i j := by
  intro i j
  rw [H3Octonion.offDiagRealPart_apply]
  by_cases hij : i = j
  · rw [if_pos hij]
    exact star_zero _
  · rw [if_neg hij]
    rw [star_smul, star_trivial, star_add, star_star, add_comm]

theorem H3Octonion.offDiagImagPart_star_neg (y : H3Octonion) :
    ∀ i j, star ((H3Octonion.offDiagImagPart y).1 i j) =
           -((H3Octonion.offDiagImagPart y).1 i j) := by
  intro i j
  rw [H3Octonion.offDiagImagPart_apply]
  by_cases hij : i = j
  · rw [if_pos hij]
    rw [star_zero, neg_zero]
  · rw [if_neg hij]
    rw [star_smul, star_trivial, star_sub, star_star, ← neg_sub]
    rw [smul_neg]

theorem jordan_identity_of_pureImag_case
    (x : H3Octonion)
    (h_imag : ∀ (y' : H3Octonion),
      (∀ i j, star (y'.1 i j) = -(y'.1 i j)) →
      (x * x * y') * x = (x * x) * (y' * x)) :
    ∀ y : H3Octonion, (x * x * y) * x = (x * x) * (y * x) := by
  apply jordan_identity_of_offDiag_case
  intro y' hy'
  rw [← H3Octonion.offDiagPart_of_isPureOffDiag y' hy',
      ← H3Octonion.offDiagPart_decompose y']
  apply jordan_identity_of_add_y
  ·
    exact jordan_identity_of_y_real x _ (H3Octonion.offDiagRealPart_star_self y')
  ·
    exact h_imag _ (H3Octonion.offDiagImagPart_star_neg y')

theorem jordan_smul_right (a b : H3Octonion) (r : ℝ) :
    a * (r • b) = r • (a * b) := by
  apply H3Octonion.ext

  show ((a * (r • b)).1) = ((r • (a * b)).1)

  simp only [jordan_mul_val]

  show (1/2 : ℝ) • (a.1 * (r • b.1) + (r • b.1) * a.1) =
       r • ((1/2 : ℝ) • (a.1 * b.1 + b.1 * a.1))
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_add]
  rw [smul_comm r (1/2 : ℝ)]

theorem jordan_smul_left (a b : H3Octonion) (r : ℝ) :
    (r • a) * b = r • (a * b) := by
  rw [jordan_mul_comm, jordan_smul_right, jordan_mul_comm b a]

theorem jordan_identity_of_smul_y (x y : H3Octonion) (r : ℝ)
    (h : (x * x * y) * x = (x * x) * (y * x)) :
    (x * x * (r • y)) * x = (x * x) * ((r • y) * x) := by
  rw [jordan_smul_right, jordan_smul_left,
      jordan_smul_left, jordan_smul_right, h]

/-- The Hermitian matrix supported at `(i, j)` and `(j, i)`. -/
noncomputable def H3Octonion.rankOne
    (i j : Fin 3) (hij : i ≠ j) (β : Octonion) : H3Octonion :=
  ⟨fun p q =>
    if (p = i ∧ q = j) then β
    else if (p = j ∧ q = i) then star β
    else 0, by
    funext p q
    simp only [Matrix.conjTranspose_apply]

    by_cases h1 : p = i ∧ q = j
    ·
      rw [if_pos h1]
      have h2' : q = j ∧ p = i := ⟨h1.2, h1.1⟩
      have h1' : ¬ (q = i ∧ p = j) := fun ⟨hqi, hpj⟩ => hij (h1.1.symm.trans hpj)
      rw [if_neg h1', if_pos h2', star_star]
    · by_cases h2 : p = j ∧ q = i
      · rw [if_neg h1, if_pos h2]
        have h1' : q = i ∧ p = j := ⟨h2.2, h2.1⟩
        rw [if_pos h1']
      ·
        rw [if_neg h1, if_neg h2]
        have h1' : ¬ (q = i ∧ p = j) := fun ⟨hqi, hpj⟩ => h2 ⟨hpj, hqi⟩
        have h2' : ¬ (q = j ∧ p = i) := fun ⟨hqj, hpi⟩ => h1 ⟨hpi, hqj⟩
        rw [if_neg h1', if_neg h2']
        exact star_zero _⟩

@[simp] lemma H3Octonion.rankOne_apply_ij (i j : Fin 3) (hij : i ≠ j) (β : Octonion) :
    (H3Octonion.rankOne i j hij β).1 i j = β := by
  show (if (i = i ∧ j = j) then β else if (i = j ∧ j = i) then star β else 0) = β
  simp only [and_self, ↓reduceIte]

@[simp] lemma H3Octonion.rankOne_apply_ji (i j : Fin 3) (hij : i ≠ j) (β : Octonion) :
    (H3Octonion.rankOne i j hij β).1 j i = star β := by
  show (if (j = i ∧ i = j) then β else if (j = j ∧ i = i) then star β else 0) = star β
  have : ¬ (j = i ∧ i = j) := fun h => hij h.2
  rw [if_neg this]
  simp only [and_self, ↓reduceIte]

/-! ## Rank-one off-diagonal terms -/

lemma H3Octonion.rankOne_apply_other (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (p q : Fin 3) (h1 : ¬ (p = i ∧ q = j)) (h2 : ¬ (p = j ∧ q = i)) :
    (H3Octonion.rankOne i j hij β).1 p q = 0 := by
  show (if (p = i ∧ q = j) then β else if (p = j ∧ q = i) then star β else 0) = 0
  rw [if_neg h1, if_neg h2]

lemma H3Octonion.rankOne_isPureOffDiag (i j : Fin 3) (hij : i ≠ j) (β : Octonion) :
    H3Octonion.IsPureOffDiag (H3Octonion.rankOne i j hij β) := by
  intro p
  apply H3Octonion.rankOne_apply_other
  · intro ⟨hpi, hpj⟩; exact hij (hpi.symm.trans hpj)
  · intro ⟨hpj, hpi⟩; exact hij (hpi.symm.trans hpj)

theorem H3Octonion.rankOne_pureImag (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (hβ : star β = -β) (p q : Fin 3) :
    star ((H3Octonion.rankOne i j hij β).1 p q) = -((H3Octonion.rankOne i j hij β).1 p q) := by
  by_cases h1 : p = i ∧ q = j
  · obtain ⟨hpi, hqj⟩ := h1
    subst hpi; subst hqj
    rw [H3Octonion.rankOne_apply_ij]
    exact hβ
  · by_cases h2 : p = j ∧ q = i
    · obtain ⟨hpj, hqi⟩ := h2
      subst hpj; subst hqi
      rw [H3Octonion.rankOne_apply_ji, star_star, hβ, neg_neg]
    · rw [H3Octonion.rankOne_apply_other i j hij β p q h1 h2]
      rw [star_zero, neg_zero]

private lemma fin3_01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide

private lemma fin3_02 : (0 : Fin 3) ≠ (2 : Fin 3) := by decide

private lemma fin3_12 : (1 : Fin 3) ≠ (2 : Fin 3) := by decide

private lemma H3Octonion.rankOne_apply_entry (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (p q : Fin 3) :
    (H3Octonion.rankOne i j hij β).1 p q =
      if p = i ∧ q = j then β
      else if p = j ∧ q = i then star β
      else 0 := rfl

theorem H3Octonion.offDiagPart_eq_rankOne_sum (y : H3Octonion) :
    H3Octonion.offDiagPart y =
      H3Octonion.rankOne 0 1 fin3_01 (y.1 0 1)
    + H3Octonion.rankOne 0 2 fin3_02 (y.1 0 2)
    + H3Octonion.rankOne 1 2 fin3_12 (y.1 1 2) := by
  apply H3Octonion.ext
  funext p q
  show (H3Octonion.offDiagPart y).1 p q =
       (H3Octonion.rankOne 0 1 fin3_01 (y.1 0 1)).1 p q
     + (H3Octonion.rankOne 0 2 fin3_02 (y.1 0 2)).1 p q
     + (H3Octonion.rankOne 1 2 fin3_12 (y.1 1 2)).1 p q
  rw [H3Octonion.offDiagPart_apply,
      H3Octonion.rankOne_apply_entry 0 1 fin3_01 (y.1 0 1) p q,
      H3Octonion.rankOne_apply_entry 0 2 fin3_02 (y.1 0 2) p q,
      H3Octonion.rankOne_apply_entry 1 2 fin3_12 (y.1 1 2) p q]

  have hy10 : star (y.1 0 1) = y.1 1 0 := (H3Octonion.entry_hermitian y 1 0).symm
  have hy20 : star (y.1 0 2) = y.1 2 0 := (H3Octonion.entry_hermitian y 2 0).symm
  have hy21 : star (y.1 1 2) = y.1 2 1 := (H3Octonion.entry_hermitian y 2 1).symm
  fin_cases p <;> fin_cases q <;>
    simp_all (config := { decide := true })

theorem jordan_identity_of_rankOne_pureImag_case
    (x : H3Octonion)
    (h_rankOne : ∀ (i j : Fin 3) (hij : i ≠ j) (β : Octonion),
      star β = -β →
      (x * x * H3Octonion.rankOne i j hij β) * x =
        (x * x) * (H3Octonion.rankOne i j hij β * x)) :
    ∀ y : H3Octonion, (x * x * y) * x = (x * x) * (y * x) := by
  apply jordan_identity_of_pureImag_case
  intro y' hy'

  have hy'_pure : H3Octonion.IsPureOffDiag y' := by
    intro i
    have h := hy' i i

    have h2 : star (y'.1 i i) = y'.1 i i := H3Octonion.diag_star y' i
    rw [h] at h2

    have hplus : y'.1 i i + y'.1 i i = 0 := by
      have := h2

      have hstep : -(y'.1 i i) + y'.1 i i = 0 := by abel
      rw [this] at hstep
      exact hstep

    have h2smul : (2 : ℝ) • y'.1 i i = 0 := by rw [two_smul]; exact hplus
    have : (2 : ℝ) • y'.1 i i = (2 : ℝ) • (0 : Octonion) := by rw [h2smul, smul_zero]
    exact smul_right_injective Octonion (by norm_num : (2 : ℝ) ≠ 0) this
  rw [← H3Octonion.offDiagPart_of_isPureOffDiag y' hy'_pure,
      H3Octonion.offDiagPart_eq_rankOne_sum]

  apply jordan_identity_of_add_y
  · apply jordan_identity_of_add_y
    · apply h_rankOne 0 1 fin3_01 (y'.1 0 1)
      exact hy' 0 1
    · apply h_rankOne 0 2 fin3_02 (y'.1 0 2)
      exact hy' 0 2
  · apply h_rankOne 1 2 fin3_12 (y'.1 1 2)
    exact hy' 1 2

theorem matAssoc_rankOne_mid_apply (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) (a b : Fin 3) :
    matAssoc A (H3Octonion.rankOne i j hij β).1 B a b =
      octAssoc (A a i) β (B j b) + octAssoc (A a j) (star β) (B i b) := by
  rw [matAssoc_apply]

  simp only [Fin.sum_univ_three, H3Octonion.rankOne_apply_entry]

  fin_cases i <;> fin_cases j <;>
    (first
      | (exfalso; revert hij; decide)
      | (simp_all (config := { decide := true })

         try (simp only [octAssoc_zero_mid, add_zero, zero_add])))
  all_goals (try abel)

theorem matAssoc_rankOne_left_apply_i (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) (b : Fin 3) :
    matAssoc (H3Octonion.rankOne i j hij β).1 A B i b =
      ∑ l, octAssoc β (A j l) (B l b) := by
  rw [matAssoc_apply]

  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _

  simp only [Fin.sum_univ_three, H3Octonion.rankOne_apply_entry]

  fin_cases i <;> fin_cases j <;>
    (first
      | (exfalso; revert hij; decide)
      | (simp_all (config := { decide := true })
         try (simp only [octAssoc_zero_left, add_zero, zero_add])))

theorem matAssoc_rankOne_left_apply_j (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) (b : Fin 3) :
    matAssoc (H3Octonion.rankOne i j hij β).1 A B j b =
      ∑ l, octAssoc (star β) (A i l) (B l b) := by
  rw [matAssoc_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fin.sum_univ_three, H3Octonion.rankOne_apply_entry]
  fin_cases i <;> fin_cases j <;>
    (first
      | (exfalso; revert hij; decide)
      | (simp_all (config := { decide := true })
         try (simp only [octAssoc_zero_left, add_zero, zero_add])))

theorem matAssoc_rankOne_left_apply_third (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) (a b : Fin 3)
    (hai : a ≠ i) (haj : a ≠ j) :
    matAssoc (H3Octonion.rankOne i j hij β).1 A B a b = 0 := by
  rw [matAssoc_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _

  rw [H3Octonion.rankOne_apply_other i j hij β a k
      (fun ⟨h, _⟩ => hai h) (fun ⟨h, _⟩ => haj h)]
  exact octAssoc_zero_left _ _

theorem matAssoc_rankOne_right_apply_j (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) (a : Fin 3) :
    matAssoc A B (H3Octonion.rankOne i j hij β).1 a j =
      ∑ k, octAssoc (A a k) (B k i) β := by
  rw [matAssoc_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fin.sum_univ_three, H3Octonion.rankOne_apply_entry]
  fin_cases i <;> fin_cases j <;>
    (first
      | (exfalso; revert hij; decide)
      | (simp_all (config := { decide := true })
         try (simp only [octAssoc_zero_right, add_zero, zero_add])))

theorem matAssoc_rankOne_right_apply_i (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) (a : Fin 3) :
    matAssoc A B (H3Octonion.rankOne i j hij β).1 a i =
      ∑ k, octAssoc (A a k) (B k j) (star β) := by
  rw [matAssoc_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fin.sum_univ_three, H3Octonion.rankOne_apply_entry]
  fin_cases i <;> fin_cases j <;>
    (first
      | (exfalso; revert hij; decide)
      | (simp_all (config := { decide := true })
         try (simp only [octAssoc_zero_right, add_zero, zero_add])))

theorem matAssoc_rankOne_right_apply_third (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) (a b : Fin 3)
    (hbi : b ≠ i) (hbj : b ≠ j) :
    matAssoc A B (H3Octonion.rankOne i j hij β).1 a b = 0 := by
  rw [matAssoc_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  rw [H3Octonion.rankOne_apply_other i j hij β l b
      (fun ⟨_, h⟩ => hbj h) (fun ⟨_, h⟩ => hbi h)]
  exact octAssoc_zero_right _ _

/-! ## Rank-one associator cancellation -/

lemma Octonion.add_star_eq_zero_of_fst_re_zero (z : Octonion) (hz : z.1.re = 0) :
    z + star z = 0 := by
  apply Octonion.ext'
  · apply Quaternion.ext <;>
    · simp only [Octonion.fst_add, Octonion.fst_zero, Octonion.star_fst,
                 Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
                 Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
                 Quaternion.re_zero, Quaternion.imI_zero,
                 Quaternion.imJ_zero, Quaternion.imK_zero]
      linarith [hz]
  · apply Quaternion.ext <;>
    · simp only [Octonion.snd_add, Octonion.snd_zero, Octonion.star_snd,
                 Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
                 Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
                 Quaternion.re_zero, Quaternion.imI_zero,
                 Quaternion.imJ_zero, Quaternion.imK_zero]
      ring

lemma octAssoc_fst_re_eq_zero (a b c : Octonion) : (octAssoc a b c).1.re = 0 := by
  show ((a * b) * c - a * (b * c)).1.re = 0
  rw [show (((a * b) * c - a * (b * c)) : Octonion).1 = ((a * b) * c).1 - (a * (b * c)).1
      from by rfl]
  rw [Quaternion.re_sub, sub_eq_zero]
  exact Octonion.real_part_assoc a b c

lemma octAssoc_add_star_eq_zero (a b c : Octonion) :
    octAssoc a b c + star (octAssoc a b c) = 0 :=
  Octonion.add_star_eq_zero_of_fst_re_zero _ (octAssoc_fst_re_eq_zero a b c)

lemma star_octAssoc_eq_neg (a b c : Octonion) :
    star (octAssoc a b c) = -octAssoc a b c :=
  eq_neg_of_add_eq_zero_right (octAssoc_add_star_eq_zero a b c)

lemma octAssoc_eq_star_reversed (a b c : Octonion) :
    octAssoc a b c = octAssoc (star c) (star b) (star a) := by
  have h1 := star_octAssoc_reversed a b c
  have h2 := star_octAssoc_eq_neg a b c

  rw [h1] at h2

  exact (neg_injective h2).symm

lemma fin3_third_unique (i j a b : Fin 3) (hij : i ≠ j)
    (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j) :
    a = b := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (exfalso; revert hij hai haj hbi hbj; decide)

lemma H3Octonion.sq_hermitian (x : H3Octonion) :
    ∀ p q : Fin 3, (x.1 * x.1) p q = star ((x.1 * x.1) q p) := by
  intro p q
  simp only [Matrix.mul_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Octonion.star_mul]
  rw [← H3Octonion.entry_hermitian x k q, ← H3Octonion.entry_hermitian x p k]

lemma octAssoc_neg_mid_eq (a b c : Octonion) :
    octAssoc a (-b) c = -octAssoc a b c := by
  show (a * (-b)) * c - a * ((-b) * c) = -((a * b) * c - a * (b * c))
  rw [mul_neg, neg_mul, neg_mul, mul_neg]
  abel

lemma octAssoc_neg_right_eq (a b c : Octonion) :
    octAssoc a b (-c) = -octAssoc a b c := by
  show (a * b) * (-c) - a * (b * (-c)) = -((a * b) * c - a * (b * c))
  rw [mul_neg, mul_neg, mul_neg]
  abel

lemma octAssoc_neg_left_eq (a b c : Octonion) :
    octAssoc (-a) b c = -octAssoc a b c := by
  show ((-a) * b) * c - (-a) * (b * c) = -((a * b) * c - a * (b * c))
  rw [neg_mul, neg_mul, neg_mul]
  abel

lemma octAssoc_hermitian_pair_vanish (a b β : Octonion) (hβ : star β = -β) :
    octAssoc a β b + octAssoc (star b) β (star a) = 0 := by
  have h := octAssoc_eq_star_reversed a β b

  rw [h, hβ, octAssoc_neg_mid_eq]
  abel

lemma mul_scalar_smul_one_apply {n : ℕ} (Y : Matrix (Fin n) (Fin n) Octonion) (c : Octonion)
    (a b : Fin n) :
    (Y * (c • (1 : Matrix (Fin n) (Fin n) Octonion))) a b = Y a b * c := by
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl, mul_one]
  · intros k _ hk
    rw [if_neg hk, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

lemma scalar_smul_one_mul_apply {n : ℕ} (Y : Matrix (Fin n) (Fin n) Octonion) (c : Octonion)
    (a b : Fin n) :
    ((c • (1 : Matrix (Fin n) (Fin n) Octonion)) * Y) a b = c * Y a b := by
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl, mul_one]
  · intros k _ hk
    rw [if_neg (Ne.symm hk), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem seven_term_sum_third_third_vanishes
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (hβ : star β = -β)
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) k k = 0 := by
  simp only [Matrix.add_apply, Matrix.sub_apply]

  rw [matAssoc_rankOne_left_apply_third i j hij β (x.1 * x.1) x.1 k k hki hkj]
  rw [matAssoc_rankOne_left_apply_third i j hij β x.1 (x.1 * x.1) k k hki hkj]

  rw [matAssoc_rankOne_right_apply_third i j hij β (x.1 * x.1) x.1 k k hki hkj]
  rw [matAssoc_rankOne_right_apply_third i j hij β x.1 (x.1 * x.1) k k hki hkj]

  rw [matAssoc_self_equals_scalar_one_smul x]
  rw [mul_scalar_smul_one_apply, scalar_smul_one_mul_apply]
  have hY_kk : (H3Octonion.rankOne i j hij β).1 k k = 0 :=
    H3Octonion.rankOne_isPureOffDiag i j hij β k
  rw [hY_kk, zero_mul, mul_zero]

  rw [matAssoc_rankOne_mid_apply i j hij β (x.1 * x.1) x.1 k k]
  rw [matAssoc_rankOne_mid_apply i j hij β x.1 (x.1 * x.1) k k]

  simp only [add_zero, sub_zero]

  rw [hβ]

  rw [show x.1 j k = star (x.1 k j) from H3Octonion.entry_hermitian x j k]
  rw [show x.1 i k = star (x.1 k i) from H3Octonion.entry_hermitian x i k]
  rw [show (x.1 * x.1) j k = star ((x.1 * x.1) k j) from H3Octonion.sq_hermitian x j k]
  rw [show (x.1 * x.1) i k = star ((x.1 * x.1) k i) from H3Octonion.sq_hermitian x i k]

  rw [octAssoc_neg_mid_eq, octAssoc_neg_mid_eq]

  have p1 := octAssoc_hermitian_pair_vanish ((x.1 * x.1) k i) (star (x.1 k j)) β hβ
  rw [star_star] at p1
  have p2 := octAssoc_hermitian_pair_vanish ((x.1 * x.1) k j) (star (x.1 k i)) β hβ
  rw [star_star] at p2

  have goal_rearr :
    (octAssoc ((x.1 * x.1) k i) β (star (x.1 k j)) +
       -octAssoc ((x.1 * x.1) k j) β (star (x.1 k i))) -
    (octAssoc (x.1 k i) β (star ((x.1 * x.1) k j)) +
       -octAssoc (x.1 k j) β (star ((x.1 * x.1) k i))) =
    (octAssoc ((x.1 * x.1) k i) β (star (x.1 k j)) +
       octAssoc (x.1 k j) β (star ((x.1 * x.1) k i))) -
    (octAssoc ((x.1 * x.1) k j) β (star (x.1 k i)) +
       octAssoc (x.1 k i) β (star ((x.1 * x.1) k j))) := by abel
  rw [goal_rearr, p1, p2, sub_self]

lemma ii_entry_residual_vanishes (U V q r β : Octonion) (hβ : star β = -β) :
    -octAssoc U (star r) β + octAssoc β V (star q) -
     octAssoc β r (star U) + octAssoc q (star V) β = 0 := by
  rw [show octAssoc U (star r) β = -octAssoc U β (star r) from octAssoc_swap_23 U (star r) β]
  rw [show octAssoc q (star V) β = -octAssoc q β (star V) from octAssoc_swap_23 q (star V) β]
  rw [show octAssoc β V (star q) = -octAssoc V β (star q) from octAssoc_swap_12 β V (star q)]
  rw [show octAssoc β r (star U) = -octAssoc r β (star U) from octAssoc_swap_12 β r (star U)]
  have p1 := octAssoc_hermitian_pair_vanish U (star r) β hβ
  rw [star_star] at p1
  have p2 := octAssoc_hermitian_pair_vanish V (star q) β hβ
  rw [star_star] at p2
  have rearr :
    -(-octAssoc U β (star r)) + -octAssoc V β (star q) -
    -octAssoc r β (star U) + -octAssoc q β (star V) =
    (octAssoc U β (star r) + octAssoc r β (star U)) -
    (octAssoc V β (star q) + octAssoc q β (star V)) := by abel
  rw [rearr, p1, p2, sub_self]

lemma fin3_sum_three (i j m : Fin 3) (hij : i ≠ j) (hmi : m ≠ i) (hmj : m ≠ j)
    {α : Type*} [AddCommMonoid α] (f : Fin 3 → α) :
    Finset.univ.sum f = f i + f j + f m := by
  fin_cases i <;> fin_cases j <;> fin_cases m
  all_goals first
    | (exfalso; revert hij hmi hmj; decide)
    | (simp [Fin.sum_univ_three]; try abel)

lemma octAssoc_pair_star_vanish (a b β : Octonion) (hβ : star β = -β) :
    octAssoc a β (star b) + octAssoc b β (star a) = 0 := by
  have h := octAssoc_hermitian_pair_vanish a (star b) β hβ
  rw [star_star] at h
  exact h

lemma Octonion.add_star_eq_smul_one (u : Octonion) :
    u + star u = (2 * u.1.re) • (1 : Octonion) := by
  apply Octonion.ext'
  ·
    apply Quaternion.ext <;>
      (simp only [Octonion.fst_add, Octonion.star_fst, Octonion.fst_smul,
                  Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
                  Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
                  Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
                  smul_eq_mul]
       show _ = _
       rw [show ((1 : Octonion).1 : Quaternion ℝ) = 1 from rfl]
       simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
                  mul_zero, mul_one]
       ring)
  ·
    apply Quaternion.ext <;>
      (simp only [Octonion.snd_add, Octonion.star_snd, Octonion.snd_smul,
                  Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
                  Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
                  Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
                  smul_eq_mul]
       show _ = _
       rw [show ((1 : Octonion).2 : Quaternion ℝ) = 0 from rfl]
       simp only [Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero,
         Quaternion.imK_zero, mul_zero]
       ring)

lemma octAssoc_add_star_left_vanish (u β q : Octonion) :
    octAssoc u β q + octAssoc (star u) β q = 0 := by
  rw [← octAssoc_add_left]
  rw [Octonion.add_star_eq_smul_one]
  exact octAssoc_smul_one_left _ _ _

lemma octAssoc_add_star_right_vanish (q β u : Octonion) :
    octAssoc q β u + octAssoc q β (star u) = 0 := by
  rw [← octAssoc_add_right]
  rw [Octonion.add_star_eq_smul_one]
  exact octAssoc_smul_one_right _ _ _

lemma octAssoc_add_star_mid_vanish (q u β : Octonion) :
    octAssoc q u β + octAssoc q (star u) β = 0 := by
  rw [← octAssoc_add_mid]
  rw [Octonion.add_star_eq_smul_one]
  exact octAssoc_smul_one_mid _ _ _

theorem seven_term_sum_ii_vanishes
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (hβ : star β = -β)
    (m : Fin 3) (hmi : m ≠ i) (hmj : m ≠ j) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) i i = 0 := by
  simp only [Matrix.add_apply, Matrix.sub_apply]

  rw [matAssoc_rankOne_left_apply_i i j hij β (x.1 * x.1) x.1 i]
  rw [matAssoc_rankOne_left_apply_i i j hij β x.1 (x.1 * x.1) i]

  rw [matAssoc_rankOne_right_apply_i i j hij β (x.1 * x.1) x.1 i]
  rw [matAssoc_rankOne_right_apply_i i j hij β x.1 (x.1 * x.1) i]

  rw [matAssoc_self_equals_scalar_one_smul x]
  rw [mul_scalar_smul_one_apply, scalar_smul_one_mul_apply]
  have hY_ii : (H3Octonion.rankOne i j hij β).1 i i = 0 :=
    H3Octonion.rankOne_isPureOffDiag i j hij β i
  rw [hY_ii, zero_mul, mul_zero]

  rw [matAssoc_rankOne_mid_apply i j hij β (x.1 * x.1) x.1 i i]
  rw [matAssoc_rankOne_mid_apply i j hij β x.1 (x.1 * x.1) i i]

  have hXii : x.1 i i = (x.1 i i).1.re • (1 : Octonion) :=
    Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x i)
  have hX2ii : (x.1 * x.1) i i = ((x.1 * x.1) i i).1.re • (1 : Octonion) := by
    apply Octonion.eq_smul_one_of_star_self
    exact (H3Octonion.sq_hermitian x i i).symm
  have hXjj : x.1 j j = (x.1 j j).1.re • (1 : Octonion) :=
    Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x j)
  have hX2jj : (x.1 * x.1) j j = ((x.1 * x.1) j j).1.re • (1 : Octonion) := by
    apply Octonion.eq_smul_one_of_star_self
    exact (H3Octonion.sq_hermitian x j j).symm

  rw [show octAssoc ((x.1 * x.1) i i) β (x.1 j i) = 0 from by
    rw [hX2ii]; exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc ((x.1 * x.1) i j) (star β) (x.1 i i) = 0 from by
    rw [hXii]; exact octAssoc_smul_one_right _ _ _]

  rw [show octAssoc (x.1 i i) β ((x.1 * x.1) j i) = 0 from by
    rw [hXii]; exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc (x.1 i j) (star β) ((x.1 * x.1) i i) = 0 from by
    rw [hX2ii]; exact octAssoc_smul_one_right _ _ _]

  simp only [zero_add, add_zero, sub_zero]

  rw [fin3_sum_three i j m hij hmi hmj fun k => octAssoc ((x.1 * x.1) i k) (x.1 k j) (star β)]
  rw [fin3_sum_three i j m hij hmi hmj fun l => octAssoc β ((x.1 * x.1) j l) (x.1 l i)]
  rw [fin3_sum_three i j m hij hmi hmj fun l => octAssoc β (x.1 j l) ((x.1 * x.1) l i)]
  rw [fin3_sum_three i j m hij hmi hmj fun k => octAssoc (x.1 i k) ((x.1 * x.1) k j) (star β)]

  rw [show octAssoc ((x.1 * x.1) i i) (x.1 i j) (star β) = 0 from by
    rw [hX2ii]; exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc ((x.1 * x.1) i j) (x.1 j j) (star β) = 0 from by
    rw [hXjj]; exact octAssoc_smul_one_mid _ _ _]

  rw [show octAssoc β ((x.1 * x.1) j i) (x.1 i i) = 0 from by
    rw [hXii]; exact octAssoc_smul_one_right _ _ _]
  rw [show octAssoc β ((x.1 * x.1) j j) (x.1 j i) = 0 from by
    rw [hX2jj]; exact octAssoc_smul_one_mid _ _ _]

  rw [show octAssoc β (x.1 j i) ((x.1 * x.1) i i) = 0 from by
    rw [hX2ii]; exact octAssoc_smul_one_right _ _ _]
  rw [show octAssoc β (x.1 j j) ((x.1 * x.1) j i) = 0 from by
    rw [hXjj]; exact octAssoc_smul_one_mid _ _ _]

  rw [show octAssoc (x.1 i i) ((x.1 * x.1) i j) (star β) = 0 from by
    rw [hXii]; exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc (x.1 i j) ((x.1 * x.1) j j) (star β) = 0 from by
    rw [hX2jj]; exact octAssoc_smul_one_mid _ _ _]

  simp only [zero_add, add_zero]

  rw [show x.1 m j = star (x.1 j m) from H3Octonion.entry_hermitian x m j]
  rw [show x.1 m i = star (x.1 i m) from H3Octonion.entry_hermitian x m i]
  rw [show (x.1 * x.1) m j = star ((x.1 * x.1) j m) from H3Octonion.sq_hermitian x m j]
  rw [show (x.1 * x.1) m i = star ((x.1 * x.1) i m) from H3Octonion.sq_hermitian x m i]

  rw [hβ, octAssoc_neg_right_eq, octAssoc_neg_right_eq]

  have rearr :
    -octAssoc ((x.1 * x.1) i m) (star (x.1 j m)) β +
    octAssoc β ((x.1 * x.1) j m) (star (x.1 i m)) -
    octAssoc β (x.1 j m) (star ((x.1 * x.1) i m)) -
    -octAssoc (x.1 i m) (star ((x.1 * x.1) j m)) β =
    -octAssoc ((x.1 * x.1) i m) (star (x.1 j m)) β +
    octAssoc β ((x.1 * x.1) j m) (star (x.1 i m)) -
    octAssoc β (x.1 j m) (star ((x.1 * x.1) i m)) +
    octAssoc (x.1 i m) (star ((x.1 * x.1) j m)) β := by abel
  rw [rearr]
  exact ii_entry_residual_vanishes ((x.1 * x.1) i m) ((x.1 * x.1) j m)
                                   (x.1 i m) (x.1 j m) β hβ

lemma H3Octonion.rankOne_swap (i j : Fin 3) (hij : i ≠ j) (β : Octonion) :
    H3Octonion.rankOne i j hij β = H3Octonion.rankOne j i (Ne.symm hij) (star β) := by
  apply H3Octonion.ext
  funext p q
  rw [H3Octonion.rankOne_apply_entry, H3Octonion.rankOne_apply_entry, star_star]

  by_cases h1 : p = i ∧ q = j
  · have h2 : ¬ (p = j ∧ q = i) := fun h => hij (h1.1.symm.trans h.1)
    rw [if_pos h1, if_neg h2, if_pos h1]
  · by_cases h2 : p = j ∧ q = i
    · rw [if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

theorem seven_term_sum_ik_vanishes
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (hβ : star β = -β)
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) i k = 0 := by
  simp only [Matrix.add_apply, Matrix.sub_apply]

  rw [matAssoc_rankOne_left_apply_i i j hij β (x.1 * x.1) x.1 k]
  rw [matAssoc_rankOne_left_apply_i i j hij β x.1 (x.1 * x.1) k]

  rw [matAssoc_rankOne_right_apply_third i j hij β (x.1 * x.1) x.1 i k hki hkj]
  rw [matAssoc_rankOne_right_apply_third i j hij β x.1 (x.1 * x.1) i k hki hkj]

  rw [matAssoc_self_equals_scalar_one_smul x]
  rw [mul_scalar_smul_one_apply, scalar_smul_one_mul_apply]
  have hY_ik : (H3Octonion.rankOne i j hij β).1 i k = 0 :=
    H3Octonion.rankOne_apply_other i j hij β i k
      (fun ⟨_, h⟩ => hkj h) (fun ⟨h, _⟩ => hij h)
  rw [hY_ik, zero_mul, mul_zero]

  rw [matAssoc_rankOne_mid_apply i j hij β (x.1 * x.1) x.1 i k]
  rw [matAssoc_rankOne_mid_apply i j hij β x.1 (x.1 * x.1) i k]

  have hXii : x.1 i i = (x.1 i i).1.re • (1 : Octonion) :=
    Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x i)
  have hX2ii : (x.1 * x.1) i i = ((x.1 * x.1) i i).1.re • (1 : Octonion) := by
    apply Octonion.eq_smul_one_of_star_self
    exact (H3Octonion.sq_hermitian x i i).symm
  rw [show octAssoc ((x.1 * x.1) i i) β (x.1 j k) = 0 from by
    rw [hX2ii]; exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc (x.1 i i) β ((x.1 * x.1) j k) = 0 from by
    rw [hXii]; exact octAssoc_smul_one_left _ _ _]

  simp only [zero_add, add_zero, sub_zero]

  rw [fin3_sum_three i j k hij hki hkj fun l => octAssoc β ((x.1 * x.1) j l) (x.1 l k)]
  rw [fin3_sum_three i j k hij hki hkj fun l => octAssoc β (x.1 j l) ((x.1 * x.1) l k)]

  rw [show octAssoc β ((x.1 * x.1) j j) (x.1 j k) = 0 from by
    have hX2jj : (x.1 * x.1) j j = ((x.1 * x.1) j j).1.re • (1 : Octonion) := by
      apply Octonion.eq_smul_one_of_star_self
      exact (H3Octonion.sq_hermitian x j j).symm
    rw [hX2jj]; exact octAssoc_smul_one_mid _ _ _]

  rw [show octAssoc β ((x.1 * x.1) j k) (x.1 k k) = 0 from by
    have hXkk : x.1 k k = (x.1 k k).1.re • (1 : Octonion) :=
      Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x k)
    rw [hXkk]; exact octAssoc_smul_one_right _ _ _]

  rw [show octAssoc β (x.1 j j) ((x.1 * x.1) j k) = 0 from by
    have hXjj : x.1 j j = (x.1 j j).1.re • (1 : Octonion) :=
      Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x j)
    rw [hXjj]; exact octAssoc_smul_one_mid _ _ _]

  rw [show octAssoc β (x.1 j k) ((x.1 * x.1) k k) = 0 from by
    have hX2kk : (x.1 * x.1) k k = ((x.1 * x.1) k k).1.re • (1 : Octonion) := by
      apply Octonion.eq_smul_one_of_star_self
      exact (H3Octonion.sq_hermitian x k k).symm
    rw [hX2kk]; exact octAssoc_smul_one_right _ _ _]

  simp only [add_zero]

  rw [hβ, octAssoc_neg_mid_eq, octAssoc_neg_mid_eq]

  rw [show (x.1 * x.1) j i = star ((x.1 * x.1) i j) from H3Octonion.sq_hermitian x j i]
  rw [show x.1 j i = star (x.1 i j) from H3Octonion.entry_hermitian x j i]

  rw [show octAssoc β (star ((x.1 * x.1) i j)) (x.1 i k) =
        -octAssoc (star ((x.1 * x.1) i j)) β (x.1 i k) from
      octAssoc_swap_12 _ _ _]
  rw [show octAssoc β (star (x.1 i j)) ((x.1 * x.1) i k) =
        -octAssoc (star (x.1 i j)) β ((x.1 * x.1) i k) from
      octAssoc_swap_12 _ _ _]

  have p1 := octAssoc_add_star_left_vanish ((x.1 * x.1) i j) β (x.1 i k)
  have p2 := octAssoc_add_star_left_vanish (x.1 i j) β ((x.1 * x.1) i k)

  have rearr :
    -octAssoc ((x.1 * x.1) i j) β (x.1 i k) + -octAssoc (star ((x.1 * x.1) i j)) β (x.1 i k) -
      -octAssoc (star (x.1 i j)) β ((x.1 * x.1) i k) -
      -octAssoc (x.1 i j) β ((x.1 * x.1) i k) =
    -(octAssoc ((x.1 * x.1) i j) β (x.1 i k) + octAssoc (star ((x.1 * x.1) i j)) β (x.1 i k)) +
    (octAssoc (x.1 i j) β ((x.1 * x.1) i k) + octAssoc (star (x.1 i j)) β ((x.1 * x.1) i k)) := by abel
  rw [rearr, p1, p2, neg_zero, add_zero]

theorem seven_term_sum_jj_vanishes
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (hβ : star β = -β)
    (m : Fin 3) (hmi : m ≠ i) (hmj : m ≠ j) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) j j = 0 := by

  rw [H3Octonion.rankOne_swap i j hij β]

  have hβ' : star (star β) = -(star β) := by
    rw [star_star, hβ, neg_neg]
  exact seven_term_sum_ii_vanishes x j i (Ne.symm hij) (star β) hβ' m hmj hmi

lemma seven_term_sum_hermitian (x y : H3Octonion) (a b : Fin 3) :
    (matAssoc (x.1 * x.1) y.1 x.1
     + matAssoc (x.1 * x.1) x.1 y.1
     + matAssoc y.1 (x.1 * x.1) x.1
     - matAssoc y.1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) y.1
     - matAssoc x.1 y.1 (x.1 * x.1)
     + y.1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * y.1) a b =
    star ((matAssoc (x.1 * x.1) y.1 x.1
     + matAssoc (x.1 * x.1) x.1 y.1
     + matAssoc y.1 (x.1 * x.1) x.1
     - matAssoc y.1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) y.1
     - matAssoc x.1 y.1 (x.1 * x.1)
     + y.1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * y.1) b a) := by

  have hform := jordan_identity_diff_matrix_form x y

  have hform' : (matAssoc (x.1 * x.1) y.1 x.1
         + matAssoc (x.1 * x.1) x.1 y.1
         + matAssoc y.1 (x.1 * x.1) x.1
         - matAssoc y.1 x.1 (x.1 * x.1)
         - matAssoc x.1 (x.1 * x.1) y.1
         - matAssoc x.1 y.1 (x.1 * x.1)
         + y.1 * matAssoc x.1 x.1 x.1
         - matAssoc x.1 x.1 x.1 * y.1) =
      (4 : ℝ) • (((x * x * y) * x).1 - ((x * x) * (y * x)).1) := by
    rw [hform, smul_smul]
    rw [show (4 : ℝ) * (1/4) = 1 from by norm_num, one_smul]
  rw [hform']

  simp only [Matrix.smul_apply, Matrix.sub_apply]
  rw [show star ((4 : ℝ) • (((x * x * y) * x).1 b a - ((x * x) * (y * x)).1 b a)) =
         (4 : ℝ) • star (((x * x * y) * x).1 b a - ((x * x) * (y * x)).1 b a) from by
      rw [star_smul, star_trivial]]
  rw [show star (((x * x * y) * x).1 b a - ((x * x) * (y * x)).1 b a) =
         star (((x * x * y) * x).1 b a) - star (((x * x) * (y * x)).1 b a) from star_sub _ _]

  rw [show star (((x * x * y) * x).1 b a) = ((x * x * y) * x).1 a b from
      (H3Octonion.entry_hermitian ((x * x * y) * x) a b).symm]
  rw [show star (((x * x) * (y * x)).1 b a) = ((x * x) * (y * x)).1 a b from
      (H3Octonion.entry_hermitian ((x * x) * (y * x)) a b).symm]

theorem seven_term_sum_ki_vanishes
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (hβ : star β = -β)
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) k i = 0 := by
  rw [seven_term_sum_hermitian x (H3Octonion.rankOne i j hij β) k i]
  rw [seven_term_sum_ik_vanishes x i j hij β hβ k hki hkj]
  exact star_zero _

theorem seven_term_sum_jk_vanishes
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (hβ : star β = -β)
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) j k = 0 := by
  rw [H3Octonion.rankOne_swap i j hij β]
  have hβ' : star (star β) = -(star β) := by
    rw [star_star, hβ, neg_neg]
  exact seven_term_sum_ik_vanishes x j i (Ne.symm hij) (star β) hβ' k hkj hki

theorem seven_term_sum_kj_vanishes
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (hβ : star β = -β)
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) k j = 0 := by
  rw [seven_term_sum_hermitian x (H3Octonion.rankOne i j hij β) k j]
  rw [seven_term_sum_jk_vanishes x i j hij β hβ k hki hkj]
  exact star_zero _

lemma octAssoc_self_star_vanish (u β : Octonion) (hβ : star β = -β) :
    octAssoc u β (star u) = 0 := by
  have h := octAssoc_pair_star_vanish u u β hβ

  have h2 : (2 : ℝ) • (octAssoc u β (star u)) = 0 := by
    rw [two_smul]; exact h
  have := smul_right_injective Octonion (by norm_num : (2 : ℝ) ≠ 0)
    (show (2 : ℝ) • (octAssoc u β (star u)) = (2 : ℝ) • (0 : Octonion) from by
      rw [h2, smul_zero])
  exact this

set_option maxHeartbeats 4000000 in

lemma associator_commutator_identity (p q r β : Octonion) :
    (octAssoc (q * star r) β (star p) + octAssoc (p * r) β (star q)
     + octAssoc (star p * q) β (star r)) +
    (octAssoc (q * star r) β (star p) + octAssoc (p * r) β (star q)
     + octAssoc (star p * q) β (star r)) =
    β * (octAssoc p r (star q) + octAssoc q (star r) (star p)) -
    (octAssoc p r (star q) + octAssoc q (star r) (star p)) * β := by
  unfold octAssoc
  octo_expand_ring_add

set_option maxHeartbeats 4000000 in

lemma x_sq_01_eq (x : H3Octonion) :
    (x.1 * x.1) 0 1 = x.1 0 0 * x.1 0 1 + x.1 0 1 * x.1 1 1 + x.1 0 2 * star (x.1 1 2) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  rw [show x.1 2 1 = star (x.1 1 2) from H3Octonion.entry_hermitian x 2 1]

lemma x_sq_02_eq (x : H3Octonion) :
    (x.1 * x.1) 0 2 = x.1 0 0 * x.1 0 2 + x.1 0 1 * x.1 1 2 + x.1 0 2 * x.1 2 2 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]

lemma x_sq_12_eq (x : H3Octonion) :
    (x.1 * x.1) 1 2 = star (x.1 0 1) * x.1 0 2 + x.1 1 1 * x.1 1 2 + x.1 1 2 * x.1 2 2 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  rw [show x.1 1 0 = star (x.1 0 1) from H3Octonion.entry_hermitian x 1 0]

lemma seven_term_sum_ij_residual_identity (p q r β : Octonion) :
    -(octAssoc (q * star r) β (star p) + octAssoc (p * r) β (star q)
      + octAssoc (star p * q) β (star r)) -
    (octAssoc (q * star r) β (star p) + octAssoc (p * r) β (star q)
     + octAssoc (star p * q) β (star r)) +
    (β * (octAssoc p r (star q) + octAssoc q (star r) (star p)) -
     (octAssoc p r (star q) + octAssoc q (star r) (star p)) * β) = 0 := by
  have h := associator_commutator_identity p q r β

  have rearr : -(octAssoc (q * star r) β (star p) + octAssoc (p * r) β (star q)
          + octAssoc (star p * q) β (star r)) -
        (octAssoc (q * star r) β (star p) + octAssoc (p * r) β (star q)
         + octAssoc (star p * q) β (star r)) =
        -((octAssoc (q * star r) β (star p) + octAssoc (p * r) β (star q)
           + octAssoc (star p * q) β (star r)) +
          (octAssoc (q * star r) β (star p) + octAssoc (p * r) β (star q)
           + octAssoc (star p * q) β (star r))) := by abel
  rw [rearr, h]
  abel

lemma Octonion.fst_re_zero_of_star_neg (β : Octonion) (hβ : star β = -β) : β.1.re = 0 := by
  have h := congr_arg (fun z : Octonion => z.1.re) hβ
  simp only [Octonion.star_fst, Quaternion.re_star, Octonion.fst_neg, Quaternion.re_neg] at h
  linarith

lemma group_a_structural_identity (p P β : Octonion) (hβ : star β = -β) :
    -octAssoc P β p + octAssoc P (star p) β + octAssoc β (star P) p -
    octAssoc β (star p) P - octAssoc p (star P) β + octAssoc p β P =
    -2 * octAssoc P β (star p) := by

  have e1 : octAssoc P β p = -octAssoc (star p) β (star P) := by
    rw [octAssoc_eq_star_reversed P β p, hβ, octAssoc_neg_mid_eq]
  have e2 : octAssoc P (star p) β = -octAssoc P β (star p) := octAssoc_swap_23 P (star p) β
  have e3 : octAssoc β (star P) p = -octAssoc (star P) β p := octAssoc_swap_12 β (star P) p
  have e4 : octAssoc β (star p) P = -octAssoc (star p) β P := octAssoc_swap_12 β (star p) P
  have e5 : octAssoc p (star P) β = -octAssoc p β (star P) := octAssoc_swap_23 p (star P) β
  have e6 : octAssoc p β P = -octAssoc (star P) β (star p) := by
    rw [octAssoc_eq_star_reversed p β P, hβ, octAssoc_neg_mid_eq]
  rw [e1, e2, e3, e4, e5, e6]

  have p1 : octAssoc (star p) β (star P) + octAssoc (star p) β P = 0 := by
    rw [add_comm]
    exact octAssoc_add_star_right_vanish (star p) β P
  have p2 : octAssoc (star P) β p + octAssoc (star P) β (star p) = 0 :=
    octAssoc_add_star_right_vanish (star P) β p
  have p3 : octAssoc P β (star p) + octAssoc p β (star P) = 0 :=
    octAssoc_pair_star_vanish P p β hβ
  have h3 : octAssoc p β (star P) = -octAssoc P β (star p) :=
    eq_neg_of_add_eq_zero_right p3
  have rearr :
    - -octAssoc (star p) β (star P) + -octAssoc P β (star p) + -octAssoc (star P) β p -
      -octAssoc (star p) β P - -octAssoc p β (star P) + -octAssoc (star P) β (star p) =
    (octAssoc (star p) β (star P) + octAssoc (star p) β P) -
    (octAssoc (star P) β p + octAssoc (star P) β (star p)) +
    (octAssoc p β (star P) - octAssoc P β (star p)) := by abel
  rw [rearr, p1, p2, h3]
  rw [show ((-2 : Octonion) * octAssoc P β (star p)) =
        -octAssoc P β (star p) - octAssoc P β (star p) from by
    rw [neg_mul, two_mul, neg_add_rev]; abel]
  abel

lemma group_b_structural_identity (q Q β : Octonion) (hβ : star β = -β) :
    octAssoc Q (star q) β - octAssoc q (star Q) β = -2 * octAssoc Q β (star q) := by
  rw [octAssoc_swap_23 Q (star q) β, octAssoc_swap_23 q (star Q) β]
  have p := octAssoc_pair_star_vanish Q q β hβ
  have h : octAssoc q β (star Q) = -octAssoc Q β (star q) := eq_neg_of_add_eq_zero_right p
  rw [h]
  rw [show ((-2 : Octonion) * octAssoc Q β (star q)) =
        -octAssoc Q β (star q) - octAssoc Q β (star q) from by
    rw [neg_mul, two_mul, neg_add_rev]; abel]
  abel

lemma group_c_structural_identity (r R β : Octonion) (hβ : star β = -β) :
    octAssoc β R (star r) - octAssoc β r (star R) = -2 * octAssoc R β (star r) := by
  rw [octAssoc_swap_12 β R (star r), octAssoc_swap_12 β r (star R)]
  have p := octAssoc_pair_star_vanish R r β hβ
  have h : octAssoc r β (star R) = -octAssoc R β (star r) := eq_neg_of_add_eq_zero_right p
  rw [h]
  rw [show ((-2 : Octonion) * octAssoc R β (star r)) =
        -octAssoc R β (star r) - octAssoc R β (star r) from by
    rw [neg_mul, two_mul, neg_add_rev]; abel]
  abel

lemma octAssoc_smul_left (r : ℝ) (a b c : Octonion) :
    octAssoc (r • a) b c = r • octAssoc a b c := by
  show ((r • a) * b) * c - (r • a) * (b * c) = r • ((a * b) * c - a * (b * c))
  rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_sub]

lemma octAssoc_smul_p_plus_add_star (r : ℝ) (p s β : Octonion) (hβ : star β = -β) :
    octAssoc (r • p + s) β (star p) = octAssoc s β (star p) := by
  rw [octAssoc_add_left, octAssoc_smul_left]
  rw [octAssoc_self_star_vanish p β hβ, smul_zero, zero_add]

lemma octAssoc_diag_p_expansion (a b : ℝ) (p q β : Octonion) (hβ : star β = -β) :
    octAssoc ((a + b) • p + q) β (star p) = octAssoc q β (star p) :=
  octAssoc_smul_p_plus_add_star (a + b) p q β hβ

lemma octAssoc_add_smul_diag_expansion (a b : ℝ) (p q β : Octonion) (hβ : star β = -β) :
    octAssoc (q + (a + b) • p) β (star p) = octAssoc q β (star p) := by
  rw [add_comm]
  exact octAssoc_diag_p_expansion a b p q β hβ

lemma H3Octonion.diag_mul_eq_smul (x : H3Octonion) (i : Fin 3) (z : Octonion) :
    x.1 i i * z = (x.1 i i).1.re • z := by
  conv_lhs => rw [Octonion.eq_smul_one_of_star_self (x.1 i i) (H3Octonion.diag_star x i)]
  rw [smul_one_mul]

lemma H3Octonion.mul_diag_eq_smul (x : H3Octonion) (i : Fin 3) (z : Octonion) :
    z * x.1 i i = (x.1 i i).1.re • z := by
  conv_lhs => rw [Octonion.eq_smul_one_of_star_self (x.1 i i) (H3Octonion.diag_star x i)]
  rw [mul_smul_one]

lemma octAssoc_square_entry_01_expand (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    octAssoc ((x.1 * x.1) 0 1) β (star (x.1 0 1)) =
    octAssoc (x.1 0 2 * star (x.1 1 2)) β (star (x.1 0 1)) := by
  rw [x_sq_01_eq]
  rw [H3Octonion.diag_mul_eq_smul, H3Octonion.mul_diag_eq_smul]
  rw [show (x.1 0 0).1.re • x.1 0 1 + (x.1 1 1).1.re • x.1 0 1 + x.1 0 2 * star (x.1 1 2) =
       ((x.1 0 0).1.re + (x.1 1 1).1.re) • x.1 0 1 + x.1 0 2 * star (x.1 1 2) from by
      rw [add_smul]]
  exact octAssoc_diag_p_expansion (x.1 0 0).1.re (x.1 1 1).1.re
        (x.1 0 1) (x.1 0 2 * star (x.1 1 2)) β hβ

lemma octAssoc_square_entry_02_expand (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    octAssoc ((x.1 * x.1) 0 2) β (star (x.1 0 2)) =
    octAssoc (x.1 0 1 * x.1 1 2) β (star (x.1 0 2)) := by
  rw [x_sq_02_eq]
  rw [H3Octonion.diag_mul_eq_smul, H3Octonion.mul_diag_eq_smul]
  rw [show (x.1 0 0).1.re • x.1 0 2 + x.1 0 1 * x.1 1 2 + (x.1 2 2).1.re • x.1 0 2 =
       ((x.1 0 0).1.re + (x.1 2 2).1.re) • x.1 0 2 + x.1 0 1 * x.1 1 2 from by
      rw [add_smul]; abel]
  exact octAssoc_diag_p_expansion (x.1 0 0).1.re (x.1 2 2).1.re
        (x.1 0 2) (x.1 0 1 * x.1 1 2) β hβ

lemma octAssoc_square_entry_12_expand (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    octAssoc ((x.1 * x.1) 1 2) β (star (x.1 1 2)) =
    octAssoc (star (x.1 0 1) * x.1 0 2) β (star (x.1 1 2)) := by
  rw [x_sq_12_eq]
  rw [H3Octonion.diag_mul_eq_smul, H3Octonion.mul_diag_eq_smul]
  rw [show star (x.1 0 1) * x.1 0 2 + (x.1 1 1).1.re • x.1 1 2 + (x.1 2 2).1.re • x.1 1 2 =
       star (x.1 0 1) * x.1 0 2 + ((x.1 1 1).1.re + (x.1 2 2).1.re) • x.1 1 2 from by
      rw [add_smul]; abel]
  exact octAssoc_add_smul_diag_expansion (x.1 1 1).1.re (x.1 2 2).1.re
        (x.1 1 2) (star (x.1 0 1) * x.1 0 2) β hβ

set_option maxHeartbeats 8000000 in

lemma seven_term_sum_01_vanishes (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne 0 1 fin3_01 β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne 0 1 fin3_01 β).1
     + matAssoc (H3Octonion.rankOne 0 1 fin3_01 β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne 0 1 fin3_01 β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne 0 1 fin3_01 β).1
     - matAssoc x.1 (H3Octonion.rankOne 0 1 fin3_01 β).1 (x.1 * x.1)
     + (H3Octonion.rankOne 0 1 fin3_01 β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne 0 1 fin3_01 β).1) 0 1 = 0 := by

  have gA := group_a_structural_identity (x.1 0 1) ((x.1 * x.1) 0 1) β hβ
  have gB := group_b_structural_identity (x.1 0 2) ((x.1 * x.1) 0 2) β hβ
  have gC := group_c_structural_identity (x.1 1 2) ((x.1 * x.1) 1 2) β hβ
  have eP := octAssoc_square_entry_01_expand x β hβ
  have eQ := octAssoc_square_entry_02_expand x β hβ
  have eR := octAssoc_square_entry_12_expand x β hβ
  have alb := associator_commutator_identity (x.1 0 1) (x.1 0 2) (x.1 1 2) β
  have hc := matAssoc_self_00_reduction x

  simp only [Matrix.add_apply, Matrix.sub_apply]

  rw [matAssoc_rankOne_mid_apply 0 1 fin3_01 β (x.1 * x.1) x.1 0 1]
  rw [matAssoc_rankOne_right_apply_j 0 1 fin3_01 β (x.1 * x.1) x.1 0]
  rw [matAssoc_rankOne_left_apply_i 0 1 fin3_01 β (x.1 * x.1) x.1 1]
  rw [matAssoc_rankOne_left_apply_i 0 1 fin3_01 β x.1 (x.1 * x.1) 1]
  rw [matAssoc_rankOne_right_apply_j 0 1 fin3_01 β x.1 (x.1 * x.1) 0]
  rw [matAssoc_rankOne_mid_apply 0 1 fin3_01 β x.1 (x.1 * x.1) 0 1]

  rw [matAssoc_self_equals_scalar_one_smul x]
  rw [mul_scalar_smul_one_apply, scalar_smul_one_mul_apply]
  rw [H3Octonion.rankOne_apply_ij 0 1 fin3_01 β]

  rw [hc]

  simp only [Fin.sum_univ_three]

  rw [hβ]

  simp only [octAssoc_neg_mid_eq]

  rw [show x.1 1 0 = star (x.1 0 1) from H3Octonion.entry_hermitian x 1 0]
  rw [show x.1 2 0 = star (x.1 0 2) from H3Octonion.entry_hermitian x 2 0]
  rw [show x.1 2 1 = star (x.1 1 2) from H3Octonion.entry_hermitian x 2 1]
  rw [show (x.1 * x.1) 1 0 = star ((x.1 * x.1) 0 1) from H3Octonion.sq_hermitian x 1 0]
  rw [show (x.1 * x.1) 2 0 = star ((x.1 * x.1) 0 2) from H3Octonion.sq_hermitian x 2 0]
  rw [show (x.1 * x.1) 2 1 = star ((x.1 * x.1) 1 2) from H3Octonion.sq_hermitian x 2 1]

  rw [show octAssoc ((x.1 * x.1) 0 0) β (x.1 1 1) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 0 0).symm]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc ((x.1 * x.1) 0 0) (x.1 0 0) β = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 0 0).symm]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc β ((x.1 * x.1) 1 1) (x.1 1 1) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 1 1).symm]
    exact octAssoc_smul_one_mid _ _ _]
  rw [show octAssoc β (x.1 1 1) ((x.1 * x.1) 1 1) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 1)]
    exact octAssoc_smul_one_mid _ _ _]
  rw [show octAssoc (x.1 0 0) ((x.1 * x.1) 0 0) β = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 0)]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc (x.1 0 0) β ((x.1 * x.1) 1 1) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 0)]
    exact octAssoc_smul_one_left _ _ _]

  simp only [zero_add, add_zero]

  show (-octAssoc ((x.1 * x.1) 0 1) β (x.1 0 1) +
        (octAssoc ((x.1 * x.1) 0 1) (star (x.1 0 1)) β + octAssoc ((x.1 * x.1) 0 2) (star (x.1 0 2)) β) +
        (octAssoc β (star ((x.1 * x.1) 0 1)) (x.1 0 1) + octAssoc β ((x.1 * x.1) 1 2) (star (x.1 1 2))) -
        (octAssoc β (star (x.1 0 1)) ((x.1 * x.1) 0 1) + octAssoc β (x.1 1 2) (star ((x.1 * x.1) 1 2))) -
        (octAssoc (x.1 0 1) (star ((x.1 * x.1) 0 1)) β + octAssoc (x.1 0 2) (star ((x.1 * x.1) 0 2)) β) -
        -octAssoc (x.1 0 1) β ((x.1 * x.1) 0 1) +
        β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
             octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
        (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
         octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β) = 0

  have rearr :
    -octAssoc ((x.1 * x.1) 0 1) β (x.1 0 1) +
        (octAssoc ((x.1 * x.1) 0 1) (star (x.1 0 1)) β + octAssoc ((x.1 * x.1) 0 2) (star (x.1 0 2)) β) +
        (octAssoc β (star ((x.1 * x.1) 0 1)) (x.1 0 1) + octAssoc β ((x.1 * x.1) 1 2) (star (x.1 1 2))) -
        (octAssoc β (star (x.1 0 1)) ((x.1 * x.1) 0 1) + octAssoc β (x.1 1 2) (star ((x.1 * x.1) 1 2))) -
        (octAssoc (x.1 0 1) (star ((x.1 * x.1) 0 1)) β + octAssoc (x.1 0 2) (star ((x.1 * x.1) 0 2)) β) -
        -octAssoc (x.1 0 1) β ((x.1 * x.1) 0 1) +
        β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
             octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
        (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
         octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β
    =
    (-octAssoc ((x.1 * x.1) 0 1) β (x.1 0 1) + octAssoc ((x.1 * x.1) 0 1) (star (x.1 0 1)) β +
     octAssoc β (star ((x.1 * x.1) 0 1)) (x.1 0 1) -
     octAssoc β (star (x.1 0 1)) ((x.1 * x.1) 0 1) -
     octAssoc (x.1 0 1) (star ((x.1 * x.1) 0 1)) β +
     octAssoc (x.1 0 1) β ((x.1 * x.1) 0 1)) +
    (octAssoc ((x.1 * x.1) 0 2) (star (x.1 0 2)) β - octAssoc (x.1 0 2) (star ((x.1 * x.1) 0 2)) β) +
    (octAssoc β ((x.1 * x.1) 1 2) (star (x.1 1 2)) - octAssoc β (x.1 1 2) (star ((x.1 * x.1) 1 2))) +
    (β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
          octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
     (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
      octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β) := by abel
  rw [rearr]
  rw [gA, gB, gC]
  rw [eP, eQ, eR]

  have neg2_eq : ∀ (y : Octonion), (-2 : Octonion) * y = -y - y := fun y => by
    rw [neg_mul, two_mul]; abel
  rw [neg2_eq, neg2_eq, neg2_eq]
  linear_combination (norm := abel) -alb

theorem seven_term_sum_ji_vanishes_of_ij_vanishes
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion)
    (h_ij : (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) i j = 0) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) j i = 0 := by
  rw [seven_term_sum_hermitian x (H3Octonion.rankOne i j hij β) j i]
  rw [h_ij]
  exact star_zero _

lemma fin3_exists_third (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | (exfalso; revert hij; decide)
    | (exact ⟨0, by decide, by decide⟩)
    | (exact ⟨1, by decide, by decide⟩)
    | (exact ⟨2, by decide, by decide⟩)

theorem jordan_identity_of_rankOne_pureImag_of_entry
    (x : H3Octonion) (i j : Fin 3) (hij : i ≠ j) (β : Octonion) (hβ : star β = -β)
    (h_ij : (matAssoc (x.1 * x.1) (H3Octonion.rankOne i j hij β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne i j hij β).1
     + matAssoc (H3Octonion.rankOne i j hij β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne i j hij β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne i j hij β).1
     - matAssoc x.1 (H3Octonion.rankOne i j hij β).1 (x.1 * x.1)
     + (H3Octonion.rankOne i j hij β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne i j hij β).1) i j = 0) :
    (x * x * H3Octonion.rankOne i j hij β) * x =
      (x * x) * (H3Octonion.rankOne i j hij β * x) := by
  apply jordan_identity_of_matAssoc_sum
  apply Matrix.ext
  intro a b
  rw [Matrix.zero_apply]

  obtain ⟨k, hki, hkj⟩ := fin3_exists_third i j hij

  rcases eq_or_ne a i with hai | hai
  · rcases eq_or_ne b i with hbi | hbi
    ·
      rw [hai, hbi]; exact seven_term_sum_ii_vanishes x i j hij β hβ k hki hkj
    · rcases eq_or_ne b j with hbj | hbj
      ·
        rw [hai, hbj]; exact h_ij
      ·
        rw [hai]
        have hbk : b = k := fin3_third_unique i j b k hij hbi hbj hki hkj
        rw [hbk]
        exact seven_term_sum_ik_vanishes x i j hij β hβ k hki hkj
  · rcases eq_or_ne a j with haj | haj
    · rcases eq_or_ne b i with hbi | hbi
      ·
        rw [haj, hbi]; exact seven_term_sum_ji_vanishes_of_ij_vanishes x i j hij β h_ij
      · rcases eq_or_ne b j with hbj | hbj
        ·
          rw [haj, hbj]; exact seven_term_sum_jj_vanishes x i j hij β hβ k hki hkj
        ·
          rw [haj]
          have hbk : b = k := fin3_third_unique i j b k hij hbi hbj hki hkj
          rw [hbk]
          exact seven_term_sum_jk_vanishes x i j hij β hβ k hki hkj
    ·
      have hak : a = k := fin3_third_unique i j a k hij hai haj hki hkj
      rcases eq_or_ne b i with hbi | hbi
      ·
        rw [hak, hbi]; exact seven_term_sum_ki_vanishes x i j hij β hβ k hki hkj
      · rcases eq_or_ne b j with hbj | hbj
        ·
          rw [hak, hbj]; exact seven_term_sum_kj_vanishes x i j hij β hβ k hki hkj
        ·
          have hbk : b = k := fin3_third_unique i j b k hij hbi hbj hki hkj
          rw [hak, hbk]
          exact seven_term_sum_third_third_vanishes x i j hij β hβ k hki hkj

theorem jordan_identity_rankOne_01 (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (x * x * H3Octonion.rankOne 0 1 fin3_01 β) * x = (x * x) * (H3Octonion.rankOne 0 1 fin3_01 β * x) :=
  jordan_identity_of_rankOne_pureImag_of_entry x 0 1 fin3_01 β hβ
    (seven_term_sum_01_vanishes x β hβ)

theorem jordan_identity_rankOne_10 (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (x * x * H3Octonion.rankOne 1 0 (Ne.symm fin3_01) β) * x =
      (x * x) * (H3Octonion.rankOne 1 0 (Ne.symm fin3_01) β * x) := by
  have hsb : star (star β) = -(star β) := by rw [star_star, hβ, neg_neg]
  have h01 := jordan_identity_rankOne_01 x (star β) hsb
  rw [show H3Octonion.rankOne 1 0 (Ne.symm fin3_01) β = H3Octonion.rankOne 0 1 fin3_01 (star β) from by
    rw [H3Octonion.rankOne_swap 0 1 fin3_01 (star β), star_star]]
  exact h01

lemma octAssoc_square_entry_12_starred_expand (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    octAssoc (star ((x.1 * x.1) 1 2)) β (x.1 1 2) =
    octAssoc (star (x.1 0 2) * x.1 0 1) β (x.1 1 2) := by
  have heq : star ((x.1 * x.1) 1 2) =
      star (x.1 0 2) * x.1 0 1 + star (x.1 1 2) * x.1 1 1 + x.1 2 2 * star (x.1 1 2) := by
    rw [x_sq_12_eq]
    rw [star_add, star_add]
    rw [Octonion.star_mul (star (x.1 0 1)) (x.1 0 2), star_star]
    rw [Octonion.star_mul (x.1 1 1) (x.1 1 2)]
    rw [Octonion.star_mul (x.1 1 2) (x.1 2 2)]
    rw [H3Octonion.diag_star x 1, H3Octonion.diag_star x 2]
  rw [heq]
  rw [H3Octonion.mul_diag_eq_smul x 1 (star (x.1 1 2))]
  rw [H3Octonion.diag_mul_eq_smul x 2 (star (x.1 1 2))]
  rw [show star (x.1 0 2) * x.1 0 1 + (x.1 1 1).1.re • star (x.1 1 2) +
          (x.1 2 2).1.re • star (x.1 1 2) =
       star (x.1 0 2) * x.1 0 1 +
         ((x.1 1 1).1.re + (x.1 2 2).1.re) • star (x.1 1 2) from by
      rw [add_smul]; abel]
  rw [octAssoc_add_left, octAssoc_smul_left]
  rw [show octAssoc (star (x.1 1 2)) β (x.1 1 2) = 0 from by
    have h := octAssoc_self_star_vanish (star (x.1 1 2)) β hβ
    rwa [star_star] at h]
  rw [smul_zero, add_zero]

set_option maxHeartbeats 8000000 in

lemma seven_term_sum_02_vanishes (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne 0 2 fin3_02 β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne 0 2 fin3_02 β).1
     + matAssoc (H3Octonion.rankOne 0 2 fin3_02 β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne 0 2 fin3_02 β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne 0 2 fin3_02 β).1
     - matAssoc x.1 (H3Octonion.rankOne 0 2 fin3_02 β).1 (x.1 * x.1)
     + (H3Octonion.rankOne 0 2 fin3_02 β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne 0 2 fin3_02 β).1) 0 2 = 0 := by

  have gA := group_a_structural_identity (x.1 0 2) ((x.1 * x.1) 0 2) β hβ
  have gB := group_b_structural_identity (x.1 0 1) ((x.1 * x.1) 0 1) β hβ

  have gC : octAssoc β (star ((x.1 * x.1) 1 2)) (x.1 1 2)
              - octAssoc β (star (x.1 1 2)) ((x.1 * x.1) 1 2)
            = -2 * octAssoc (star ((x.1 * x.1) 1 2)) β (x.1 1 2) := by
    have h := group_c_structural_identity (star (x.1 1 2)) (star ((x.1 * x.1) 1 2)) β hβ
    simp only [star_star] at h
    exact h
  have eP := octAssoc_square_entry_02_expand x β hβ
  have eQ := octAssoc_square_entry_01_expand x β hβ
  have eR := octAssoc_square_entry_12_starred_expand x β hβ
  have alb := associator_commutator_identity (x.1 0 2) (x.1 0 1) (star (x.1 1 2)) β

  simp only [star_star] at alb
  have hc := matAssoc_self_00_reduction x
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [matAssoc_rankOne_mid_apply 0 2 fin3_02 β (x.1 * x.1) x.1 0 2]
  rw [matAssoc_rankOne_right_apply_j 0 2 fin3_02 β (x.1 * x.1) x.1 0]
  rw [matAssoc_rankOne_left_apply_i 0 2 fin3_02 β (x.1 * x.1) x.1 2]
  rw [matAssoc_rankOne_left_apply_i 0 2 fin3_02 β x.1 (x.1 * x.1) 2]
  rw [matAssoc_rankOne_right_apply_j 0 2 fin3_02 β x.1 (x.1 * x.1) 0]
  rw [matAssoc_rankOne_mid_apply 0 2 fin3_02 β x.1 (x.1 * x.1) 0 2]
  rw [matAssoc_self_equals_scalar_one_smul x]
  rw [mul_scalar_smul_one_apply, scalar_smul_one_mul_apply]
  rw [H3Octonion.rankOne_apply_ij 0 2 fin3_02 β]
  rw [hc]
  simp only [Fin.sum_univ_three]
  rw [hβ]
  simp only [octAssoc_neg_mid_eq]

  rw [show x.1 1 0 = star (x.1 0 1) from H3Octonion.entry_hermitian x 1 0]
  rw [show x.1 2 0 = star (x.1 0 2) from H3Octonion.entry_hermitian x 2 0]
  rw [show x.1 2 1 = star (x.1 1 2) from H3Octonion.entry_hermitian x 2 1]
  rw [show (x.1 * x.1) 1 0 = star ((x.1 * x.1) 0 1) from H3Octonion.sq_hermitian x 1 0]
  rw [show (x.1 * x.1) 2 0 = star ((x.1 * x.1) 0 2) from H3Octonion.sq_hermitian x 2 0]
  rw [show (x.1 * x.1) 2 1 = star ((x.1 * x.1) 1 2) from H3Octonion.sq_hermitian x 2 1]

  rw [show octAssoc ((x.1 * x.1) 0 0) β (x.1 2 2) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 0 0).symm]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc ((x.1 * x.1) 0 0) (x.1 0 0) β = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 0 0).symm]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc β ((x.1 * x.1) 2 2) (x.1 2 2) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 2 2).symm]
    exact octAssoc_smul_one_mid _ _ _]
  rw [show octAssoc β (x.1 2 2) ((x.1 * x.1) 2 2) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 2)]
    exact octAssoc_smul_one_mid _ _ _]
  rw [show octAssoc (x.1 0 0) ((x.1 * x.1) 0 0) β = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 0)]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc (x.1 0 0) β ((x.1 * x.1) 2 2) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 0)]
    exact octAssoc_smul_one_left _ _ _]
  simp only [zero_add, add_zero]
  show (-octAssoc ((x.1 * x.1) 0 2) β (x.1 0 2) +
        (octAssoc ((x.1 * x.1) 0 1) (star (x.1 0 1)) β + octAssoc ((x.1 * x.1) 0 2) (star (x.1 0 2)) β) +
        (octAssoc β (star ((x.1 * x.1) 0 2)) (x.1 0 2) + octAssoc β (star ((x.1 * x.1) 1 2)) (x.1 1 2)) -
        (octAssoc β (star (x.1 0 2)) ((x.1 * x.1) 0 2) + octAssoc β (star (x.1 1 2)) ((x.1 * x.1) 1 2)) -
        (octAssoc (x.1 0 1) (star ((x.1 * x.1) 0 1)) β + octAssoc (x.1 0 2) (star ((x.1 * x.1) 0 2)) β) -
        -octAssoc (x.1 0 2) β ((x.1 * x.1) 0 2) +
        β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
             octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
        (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
         octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β) = 0
  have rearr :
    -octAssoc ((x.1 * x.1) 0 2) β (x.1 0 2) +
        (octAssoc ((x.1 * x.1) 0 1) (star (x.1 0 1)) β + octAssoc ((x.1 * x.1) 0 2) (star (x.1 0 2)) β) +
        (octAssoc β (star ((x.1 * x.1) 0 2)) (x.1 0 2) + octAssoc β (star ((x.1 * x.1) 1 2)) (x.1 1 2)) -
        (octAssoc β (star (x.1 0 2)) ((x.1 * x.1) 0 2) + octAssoc β (star (x.1 1 2)) ((x.1 * x.1) 1 2)) -
        (octAssoc (x.1 0 1) (star ((x.1 * x.1) 0 1)) β + octAssoc (x.1 0 2) (star ((x.1 * x.1) 0 2)) β) -
        -octAssoc (x.1 0 2) β ((x.1 * x.1) 0 2) +
        β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
             octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
        (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
         octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β
    =
    (-octAssoc ((x.1 * x.1) 0 2) β (x.1 0 2) + octAssoc ((x.1 * x.1) 0 2) (star (x.1 0 2)) β +
     octAssoc β (star ((x.1 * x.1) 0 2)) (x.1 0 2) -
     octAssoc β (star (x.1 0 2)) ((x.1 * x.1) 0 2) -
     octAssoc (x.1 0 2) (star ((x.1 * x.1) 0 2)) β +
     octAssoc (x.1 0 2) β ((x.1 * x.1) 0 2)) +
    (octAssoc ((x.1 * x.1) 0 1) (star (x.1 0 1)) β - octAssoc (x.1 0 1) (star ((x.1 * x.1) 0 1)) β) +
    (octAssoc β (star ((x.1 * x.1) 1 2)) (x.1 1 2) - octAssoc β (star (x.1 1 2)) ((x.1 * x.1) 1 2)) +
    (β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
          octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
     (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
      octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β) := by abel
  rw [rearr]
  rw [gA, gB, gC]
  rw [eP, eQ, eR]
  have neg2_eq : ∀ (y : Octonion), (-2 : Octonion) * y = -y - y := fun y => by
    rw [neg_mul, two_mul]; abel
  rw [neg2_eq, neg2_eq, neg2_eq]
  linear_combination (norm := abel_nf) -alb

theorem jordan_identity_rankOne_02 (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (x * x * H3Octonion.rankOne 0 2 fin3_02 β) * x = (x * x) * (H3Octonion.rankOne 0 2 fin3_02 β * x) :=
  jordan_identity_of_rankOne_pureImag_of_entry x 0 2 fin3_02 β hβ
    (seven_term_sum_02_vanishes x β hβ)

theorem jordan_identity_rankOne_20 (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (x * x * H3Octonion.rankOne 2 0 (Ne.symm fin3_02) β) * x =
      (x * x) * (H3Octonion.rankOne 2 0 (Ne.symm fin3_02) β * x) := by
  have hsb : star (star β) = -(star β) := by rw [star_star, hβ, neg_neg]
  have h02 := jordan_identity_rankOne_02 x (star β) hsb
  rw [show H3Octonion.rankOne 2 0 (Ne.symm fin3_02) β = H3Octonion.rankOne 0 2 fin3_02 (star β) from by
    rw [H3Octonion.rankOne_swap 0 2 fin3_02 (star β), star_star]]
  exact h02

lemma octAssoc_star_reverse_pair (a b c β : Octonion) (hβ : star β = -β) :
    octAssoc (a * b) β c = octAssoc (star b * star a) β (star c) := by
  rw [octAssoc_eq_star_reversed (a * b) β c]
  rw [Octonion.star_mul a b]
  rw [hβ, octAssoc_neg_mid_eq]

  rw [octAssoc_swap_12 (star c) β (star b * star a)]
  rw [neg_neg]

  rw [octAssoc_cyclic β (star c) (star b * star a)]
  rw [octAssoc_cyclic (star c) (star b * star a) β]

lemma octAssoc_square_entry_01_starred_expand (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    octAssoc (star ((x.1 * x.1) 0 1)) β (x.1 0 1) =
    octAssoc (x.1 0 2 * star (x.1 1 2)) β (star (x.1 0 1)) := by
  have heq : star ((x.1 * x.1) 0 1) =
      star (x.1 0 1) * x.1 0 0 + x.1 1 1 * star (x.1 0 1) + x.1 1 2 * star (x.1 0 2) := by
    rw [x_sq_01_eq]
    rw [star_add, star_add]
    rw [Octonion.star_mul (x.1 0 0) (x.1 0 1)]
    rw [Octonion.star_mul (x.1 0 1) (x.1 1 1)]
    rw [Octonion.star_mul (x.1 0 2) (star (x.1 1 2)), star_star]
    rw [H3Octonion.diag_star x 0, H3Octonion.diag_star x 1]
  rw [heq]
  rw [H3Octonion.mul_diag_eq_smul x 0 (star (x.1 0 1))]
  rw [H3Octonion.diag_mul_eq_smul x 1 (star (x.1 0 1))]
  rw [show (x.1 0 0).1.re • star (x.1 0 1) + (x.1 1 1).1.re • star (x.1 0 1) +
          x.1 1 2 * star (x.1 0 2) =
        x.1 1 2 * star (x.1 0 2) +
          ((x.1 0 0).1.re + (x.1 1 1).1.re) • star (x.1 0 1) from by
      rw [add_smul]; abel]
  rw [octAssoc_add_left, octAssoc_smul_left]
  rw [show octAssoc (star (x.1 0 1)) β (x.1 0 1) = 0 from by
    have h := octAssoc_self_star_vanish (star (x.1 0 1)) β hβ
    rwa [star_star] at h]
  rw [smul_zero, add_zero]

  have h := octAssoc_star_reverse_pair (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1)) β hβ
  simp only [star_star] at h
  exact h.symm

lemma octAssoc_square_entry_02_starred_expand (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    octAssoc (star ((x.1 * x.1) 0 2)) β (x.1 0 2) =
    octAssoc (x.1 0 1 * x.1 1 2) β (star (x.1 0 2)) := by
  have heq : star ((x.1 * x.1) 0 2) =
      star (x.1 0 2) * x.1 0 0 + star (x.1 1 2) * star (x.1 0 1) + x.1 2 2 * star (x.1 0 2) := by
    rw [x_sq_02_eq]
    rw [star_add, star_add]
    rw [Octonion.star_mul (x.1 0 0) (x.1 0 2)]
    rw [Octonion.star_mul (x.1 0 1) (x.1 1 2)]
    rw [Octonion.star_mul (x.1 0 2) (x.1 2 2)]
    rw [H3Octonion.diag_star x 0, H3Octonion.diag_star x 2]
  rw [heq]
  rw [H3Octonion.mul_diag_eq_smul x 0 (star (x.1 0 2))]
  rw [H3Octonion.diag_mul_eq_smul x 2 (star (x.1 0 2))]
  rw [show (x.1 0 0).1.re • star (x.1 0 2) + star (x.1 1 2) * star (x.1 0 1) +
          (x.1 2 2).1.re • star (x.1 0 2) =
        star (x.1 1 2) * star (x.1 0 1) +
          ((x.1 0 0).1.re + (x.1 2 2).1.re) • star (x.1 0 2) from by
      rw [add_smul]; abel]
  rw [octAssoc_add_left, octAssoc_smul_left]
  rw [show octAssoc (star (x.1 0 2)) β (x.1 0 2) = 0 from by
    have h := octAssoc_self_star_vanish (star (x.1 0 2)) β hβ
    rwa [star_star] at h]
  rw [smul_zero, add_zero]

  have h := octAssoc_star_reverse_pair (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) β hβ
  simp only [star_star] at h
  exact h.symm

set_option maxHeartbeats 8000000 in

lemma seven_term_sum_12_vanishes (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (matAssoc (x.1 * x.1) (H3Octonion.rankOne 1 2 fin3_12 β).1 x.1
     + matAssoc (x.1 * x.1) x.1 (H3Octonion.rankOne 1 2 fin3_12 β).1
     + matAssoc (H3Octonion.rankOne 1 2 fin3_12 β).1 (x.1 * x.1) x.1
     - matAssoc (H3Octonion.rankOne 1 2 fin3_12 β).1 x.1 (x.1 * x.1)
     - matAssoc x.1 (x.1 * x.1) (H3Octonion.rankOne 1 2 fin3_12 β).1
     - matAssoc x.1 (H3Octonion.rankOne 1 2 fin3_12 β).1 (x.1 * x.1)
     + (H3Octonion.rankOne 1 2 fin3_12 β).1 * matAssoc x.1 x.1 x.1
     - matAssoc x.1 x.1 x.1 * (H3Octonion.rankOne 1 2 fin3_12 β).1) 1 2 = 0 := by
  have gA := group_a_structural_identity (x.1 1 2) ((x.1 * x.1) 1 2) β hβ
  have gB : octAssoc (star ((x.1 * x.1) 0 1)) (x.1 0 1) β
              - octAssoc (star (x.1 0 1)) ((x.1 * x.1) 0 1) β
            = -2 * octAssoc (star ((x.1 * x.1) 0 1)) β (x.1 0 1) := by
    have h := group_b_structural_identity (star (x.1 0 1)) (star ((x.1 * x.1) 0 1)) β hβ
    simp only [star_star] at h
    exact h
  have gC : octAssoc β (star ((x.1 * x.1) 0 2)) (x.1 0 2)
              - octAssoc β (star (x.1 0 2)) ((x.1 * x.1) 0 2)
            = -2 * octAssoc (star ((x.1 * x.1) 0 2)) β (x.1 0 2) := by
    have h := group_c_structural_identity (star (x.1 0 2)) (star ((x.1 * x.1) 0 2)) β hβ
    simp only [star_star] at h
    exact h
  have eP := octAssoc_square_entry_12_expand x β hβ
  have eQ := octAssoc_square_entry_01_starred_expand x β hβ
  have eR := octAssoc_square_entry_02_starred_expand x β hβ
  have alb := associator_commutator_identity (x.1 0 1) (x.1 0 2) (x.1 1 2) β
  have hc := matAssoc_self_00_reduction x
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [matAssoc_rankOne_mid_apply 1 2 fin3_12 β (x.1 * x.1) x.1 1 2]
  rw [matAssoc_rankOne_right_apply_j 1 2 fin3_12 β (x.1 * x.1) x.1 1]
  rw [matAssoc_rankOne_left_apply_i 1 2 fin3_12 β (x.1 * x.1) x.1 2]
  rw [matAssoc_rankOne_left_apply_i 1 2 fin3_12 β x.1 (x.1 * x.1) 2]
  rw [matAssoc_rankOne_right_apply_j 1 2 fin3_12 β x.1 (x.1 * x.1) 1]
  rw [matAssoc_rankOne_mid_apply 1 2 fin3_12 β x.1 (x.1 * x.1) 1 2]
  rw [matAssoc_self_equals_scalar_one_smul x]
  rw [mul_scalar_smul_one_apply, scalar_smul_one_mul_apply]
  rw [H3Octonion.rankOne_apply_ij 1 2 fin3_12 β]
  rw [hc]
  simp only [Fin.sum_univ_three]
  rw [hβ]
  simp only [octAssoc_neg_mid_eq]
  rw [show x.1 1 0 = star (x.1 0 1) from H3Octonion.entry_hermitian x 1 0]
  rw [show x.1 2 0 = star (x.1 0 2) from H3Octonion.entry_hermitian x 2 0]
  rw [show x.1 2 1 = star (x.1 1 2) from H3Octonion.entry_hermitian x 2 1]
  rw [show (x.1 * x.1) 1 0 = star ((x.1 * x.1) 0 1) from H3Octonion.sq_hermitian x 1 0]
  rw [show (x.1 * x.1) 2 0 = star ((x.1 * x.1) 0 2) from H3Octonion.sq_hermitian x 2 0]
  rw [show (x.1 * x.1) 2 1 = star ((x.1 * x.1) 1 2) from H3Octonion.sq_hermitian x 2 1]
  rw [show octAssoc ((x.1 * x.1) 1 1) β (x.1 2 2) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 1 1).symm]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc ((x.1 * x.1) 1 1) (x.1 1 1) β = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 1 1).symm]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc β ((x.1 * x.1) 2 2) (x.1 2 2) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.sq_hermitian x 2 2).symm]
    exact octAssoc_smul_one_mid _ _ _]
  rw [show octAssoc β (x.1 2 2) ((x.1 * x.1) 2 2) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 2)]
    exact octAssoc_smul_one_mid _ _ _]
  rw [show octAssoc (x.1 1 1) ((x.1 * x.1) 1 1) β = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 1)]
    exact octAssoc_smul_one_left _ _ _]
  rw [show octAssoc (x.1 1 1) β ((x.1 * x.1) 2 2) = 0 from by
    rw [Octonion.eq_smul_one_of_star_self _ (H3Octonion.diag_star x 1)]
    exact octAssoc_smul_one_left _ _ _]
  simp only [zero_add, add_zero]
  show (-octAssoc ((x.1 * x.1) 1 2) β (x.1 1 2) +
        (octAssoc (star ((x.1 * x.1) 0 1)) (x.1 0 1) β + octAssoc ((x.1 * x.1) 1 2) (star (x.1 1 2)) β) +
        (octAssoc β (star ((x.1 * x.1) 0 2)) (x.1 0 2) + octAssoc β (star ((x.1 * x.1) 1 2)) (x.1 1 2)) -
        (octAssoc β (star (x.1 0 2)) ((x.1 * x.1) 0 2) + octAssoc β (star (x.1 1 2)) ((x.1 * x.1) 1 2)) -
        (octAssoc (star (x.1 0 1)) ((x.1 * x.1) 0 1) β + octAssoc (x.1 1 2) (star ((x.1 * x.1) 1 2)) β) -
        -octAssoc (x.1 1 2) β ((x.1 * x.1) 1 2) +
        β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
             octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
        (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
         octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β) = 0
  have rearr :
    -octAssoc ((x.1 * x.1) 1 2) β (x.1 1 2) +
        (octAssoc (star ((x.1 * x.1) 0 1)) (x.1 0 1) β + octAssoc ((x.1 * x.1) 1 2) (star (x.1 1 2)) β) +
        (octAssoc β (star ((x.1 * x.1) 0 2)) (x.1 0 2) + octAssoc β (star ((x.1 * x.1) 1 2)) (x.1 1 2)) -
        (octAssoc β (star (x.1 0 2)) ((x.1 * x.1) 0 2) + octAssoc β (star (x.1 1 2)) ((x.1 * x.1) 1 2)) -
        (octAssoc (star (x.1 0 1)) ((x.1 * x.1) 0 1) β + octAssoc (x.1 1 2) (star ((x.1 * x.1) 1 2)) β) -
        -octAssoc (x.1 1 2) β ((x.1 * x.1) 1 2) +
        β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
             octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
        (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
         octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β
    =
    (-octAssoc ((x.1 * x.1) 1 2) β (x.1 1 2) + octAssoc ((x.1 * x.1) 1 2) (star (x.1 1 2)) β +
     octAssoc β (star ((x.1 * x.1) 1 2)) (x.1 1 2) -
     octAssoc β (star (x.1 1 2)) ((x.1 * x.1) 1 2) -
     octAssoc (x.1 1 2) (star ((x.1 * x.1) 1 2)) β +
     octAssoc (x.1 1 2) β ((x.1 * x.1) 1 2)) +
    (octAssoc (star ((x.1 * x.1) 0 1)) (x.1 0 1) β - octAssoc (star (x.1 0 1)) ((x.1 * x.1) 0 1) β) +
    (octAssoc β (star ((x.1 * x.1) 0 2)) (x.1 0 2) - octAssoc β (star (x.1 0 2)) ((x.1 * x.1) 0 2)) +
    (β * (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
          octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) -
     (octAssoc (x.1 0 1) (x.1 1 2) (star (x.1 0 2)) +
      octAssoc (x.1 0 2) (star (x.1 1 2)) (star (x.1 0 1))) * β) := by abel
  rw [rearr]
  rw [gA, gB, gC]
  rw [eP, eQ, eR]
  have neg2_eq : ∀ (y : Octonion), (-2 : Octonion) * y = -y - y := fun y => by
    rw [neg_mul, two_mul]; abel
  rw [neg2_eq, neg2_eq, neg2_eq]
  linear_combination (norm := abel) -alb

theorem jordan_identity_rankOne_12 (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (x * x * H3Octonion.rankOne 1 2 fin3_12 β) * x = (x * x) * (H3Octonion.rankOne 1 2 fin3_12 β * x) :=
  jordan_identity_of_rankOne_pureImag_of_entry x 1 2 fin3_12 β hβ
    (seven_term_sum_12_vanishes x β hβ)

theorem jordan_identity_rankOne_21 (x : H3Octonion) (β : Octonion) (hβ : star β = -β) :
    (x * x * H3Octonion.rankOne 2 1 (Ne.symm fin3_12) β) * x =
      (x * x) * (H3Octonion.rankOne 2 1 (Ne.symm fin3_12) β * x) := by
  have hsb : star (star β) = -(star β) := by rw [star_star, hβ, neg_neg]
  have h12 := jordan_identity_rankOne_12 x (star β) hsb
  rw [show H3Octonion.rankOne 2 1 (Ne.symm fin3_12) β = H3Octonion.rankOne 1 2 fin3_12 (star β) from by
    rw [H3Octonion.rankOne_swap 1 2 fin3_12 (star β), star_star]]
  exact h12

/-! ## The Albert algebra -/

set_option maxHeartbeats 8000000 in

theorem jordan_identity (x : H3Octonion) :
    ∀ y : H3Octonion, (x * x * y) * x = (x * x) * (y * x) := by
  apply jordan_identity_of_rankOne_pureImag_case x
  intro i j hij β hβ

  rcases eq_or_ne i 0 with hi0 | hi0
  · subst hi0
    rcases eq_or_ne j 1 with hj1 | hj1
    · subst hj1; exact jordan_identity_rankOne_01 x β hβ
    · rcases eq_or_ne j 2 with hj2 | hj2
      · subst hj2; exact jordan_identity_rankOne_02 x β hβ
      · exfalso; fin_cases j <;> simp_all
  · rcases eq_or_ne i 1 with hi1 | hi1
    · subst hi1
      rcases eq_or_ne j 0 with hj0 | hj0
      · subst hj0; exact jordan_identity_rankOne_10 x β hβ
      · rcases eq_or_ne j 2 with hj2 | hj2
        · subst hj2; exact jordan_identity_rankOne_12 x β hβ
        · exfalso; fin_cases j <;> simp_all
    · have hi2 : i = 2 := by fin_cases i <;> simp_all
      subst hi2
      rcases eq_or_ne j 0 with hj0 | hj0
      · subst hj0; exact jordan_identity_rankOne_20 x β hβ
      · rcases eq_or_ne j 1 with hj1 | hj1
        · subst hj1; exact jordan_identity_rankOne_21 x β hβ
        · exfalso; fin_cases j <;> simp_all

theorem jordan_zero_mul (x : H3Octonion) : (0 : H3Octonion) * x = 0 := by
  apply H3Octonion.ext
  simp [jordan_mul_val]

theorem jordan_mul_zero (x : H3Octonion) : x * (0 : H3Octonion) = 0 := by
  rw [jordan_mul_comm, jordan_zero_mul]

instance : NonUnitalNonAssocCommRing H3Octonion where
  mul_comm := jordan_mul_comm
  left_distrib := jordan_mul_add
  right_distrib := jordan_add_mul
  zero_mul := jordan_zero_mul
  mul_zero := jordan_mul_zero

instance : IsCommJordan H3Octonion where
  lmul_comm_rmul_rmul x y := by
    calc
      (x * y) * (x * x) = (x * x) * (y * x) := by
        rw [jordan_mul_comm (x * y) (x * x), jordan_mul_comm x y]
      _ = ((x * x) * y) * x := (jordan_identity x y).symm
      _ = x * (y * (x * x)) := by
        rw [jordan_mul_comm ((x * x) * y) x,
          jordan_mul_comm y (x * x)]

end Albert
