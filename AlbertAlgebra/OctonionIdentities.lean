import AlbertAlgebra.Octonion

/-!
# Octonion identities

Scalar compatibility, Euclidean inner-product identities, alternativity, and
the Moufang identities support the construction of the Albert algebra.
-/

noncomputable section

set_option autoImplicit false

theorem Quaternion.star_smul_real (r : ℝ) (q : Quaternion ℝ) :
    star (r • q) = r • star q := by
  apply Quaternion.ext <;> simp

theorem Octonion.smul_mul (r : ℝ) (x y : Octonion) : (r • x) * y = r • (x * y) := by
  apply Octonion.ext'
  · show (r • x).1 * y.1 - star y.2 * (r • x).2 = r • (x.1 * y.1 - star y.2 * x.2)
    rw [Octonion.fst_smul, Octonion.snd_smul, smul_sub]
    congr 1
    · exact smul_mul_assoc r x.1 y.1
    · rw [mul_smul_comm]
  · show y.2 * (r • x).1 + (r • x).2 * star y.1 = r • (y.2 * x.1 + x.2 * star y.1)
    rw [Octonion.fst_smul, Octonion.snd_smul, smul_add]
    congr 1
    · rw [mul_smul_comm]
    · exact smul_mul_assoc r x.2 (star y.1)

theorem Octonion.mul_smul (r : ℝ) (x y : Octonion) : x * (r • y) = r • (x * y) := by
  apply Octonion.ext'
  · show x.1 * (r • y).1 - star (r • y).2 * x.2 = r • (x.1 * y.1 - star y.2 * x.2)
    rw [Octonion.fst_smul, Octonion.snd_smul, Quaternion.star_smul_real, smul_sub]
    congr 1
    · rw [mul_smul_comm]
    · exact smul_mul_assoc r (star y.2) x.2
  · show (r • y).2 * x.1 + x.2 * star (r • y).1 = r • (y.2 * x.1 + x.2 * star y.1)
    rw [Octonion.fst_smul, Octonion.snd_smul, Quaternion.star_smul_real, smul_add]
    congr 1
    · exact smul_mul_assoc r y.2 x.1
    · rw [mul_smul_comm]

/-- The Euclidean inner product obtained by polarizing `Octonion.normSq`. -/
def Octonion.inner (x y : Octonion) : ℝ :=
  (Octonion.normSq (x + y) - Octonion.normSq x - Octonion.normSq y) / 2

lemma Octonion.inner_self (x : Octonion) : Octonion.inner x x = Octonion.normSq x := by
  unfold Octonion.inner

  have h : x + x = (2 : ℝ) • x := by rw [two_smul]
  rw [h]
  have h_fst_re : ((2 : ℝ) • x).1.re = 2 * x.1.re := rfl
  have h_fst_imI : ((2 : ℝ) • x).1.imI = 2 * x.1.imI := rfl
  have h_fst_imJ : ((2 : ℝ) • x).1.imJ = 2 * x.1.imJ := rfl
  have h_fst_imK : ((2 : ℝ) • x).1.imK = 2 * x.1.imK := rfl
  have h_snd_re : ((2 : ℝ) • x).2.re = 2 * x.2.re := rfl
  have h_snd_imI : ((2 : ℝ) • x).2.imI = 2 * x.2.imI := rfl
  have h_snd_imJ : ((2 : ℝ) • x).2.imJ = 2 * x.2.imJ := rfl
  have h_snd_imK : ((2 : ℝ) • x).2.imK = 2 * x.2.imK := rfl
  unfold Octonion.normSq
  rw [h_fst_re, h_fst_imI, h_fst_imJ, h_fst_imK,
      h_snd_re, h_snd_imI, h_snd_imJ, h_snd_imK]
  ring

lemma Octonion.inner_comm (x y : Octonion) : Octonion.inner x y = Octonion.inner y x := by
  unfold Octonion.inner
  rw [show x + y = y + x from add_comm x y]
  ring

private lemma octonion_inner_eq_real_dot (x y : Octonion) :
    Octonion.inner x y =
      x.1.re * y.1.re + x.1.imI * y.1.imI + x.1.imJ * y.1.imJ + x.1.imK * y.1.imK
      + x.2.re * y.2.re + x.2.imI * y.2.imI + x.2.imJ * y.2.imJ + x.2.imK * y.2.imK := by
  unfold Octonion.inner Octonion.normSq
  have h1 : (x + y).1.re = x.1.re + y.1.re := by
    show (x.1 + y.1).re = x.1.re + y.1.re; exact Quaternion.re_add _ _
  have h2 : (x + y).1.imI = x.1.imI + y.1.imI := by
    show (x.1 + y.1).imI = x.1.imI + y.1.imI; exact Quaternion.imI_add _ _
  have h3 : (x + y).1.imJ = x.1.imJ + y.1.imJ := by
    show (x.1 + y.1).imJ = x.1.imJ + y.1.imJ; exact Quaternion.imJ_add _ _
  have h4 : (x + y).1.imK = x.1.imK + y.1.imK := by
    show (x.1 + y.1).imK = x.1.imK + y.1.imK; exact Quaternion.imK_add _ _
  have h5 : (x + y).2.re = x.2.re + y.2.re := by
    show (x.2 + y.2).re = x.2.re + y.2.re; exact Quaternion.re_add _ _
  have h6 : (x + y).2.imI = x.2.imI + y.2.imI := by
    show (x.2 + y.2).imI = x.2.imI + y.2.imI; exact Quaternion.imI_add _ _
  have h7 : (x + y).2.imJ = x.2.imJ + y.2.imJ := by
    show (x.2 + y.2).imJ = x.2.imJ + y.2.imJ; exact Quaternion.imJ_add _ _
  have h8 : (x + y).2.imK = x.2.imK + y.2.imK := by
    show (x.2 + y.2).imK = x.2.imK + y.2.imK; exact Quaternion.imK_add _ _
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  ring

lemma Octonion.inner_add_left (x y z : Octonion) :
    Octonion.inner (x + y) z = Octonion.inner x z + Octonion.inner y z := by
  rw [octonion_inner_eq_real_dot, octonion_inner_eq_real_dot, octonion_inner_eq_real_dot]
  have h1 : (x + y).1.re = x.1.re + y.1.re := by
    show (x.1 + y.1).re = _; exact Quaternion.re_add _ _
  have h2 : (x + y).1.imI = x.1.imI + y.1.imI := by
    show (x.1 + y.1).imI = _; exact Quaternion.imI_add _ _
  have h3 : (x + y).1.imJ = x.1.imJ + y.1.imJ := by
    show (x.1 + y.1).imJ = _; exact Quaternion.imJ_add _ _
  have h4 : (x + y).1.imK = x.1.imK + y.1.imK := by
    show (x.1 + y.1).imK = _; exact Quaternion.imK_add _ _
  have h5 : (x + y).2.re = x.2.re + y.2.re := by
    show (x.2 + y.2).re = _; exact Quaternion.re_add _ _
  have h6 : (x + y).2.imI = x.2.imI + y.2.imI := by
    show (x.2 + y.2).imI = _; exact Quaternion.imI_add _ _
  have h7 : (x + y).2.imJ = x.2.imJ + y.2.imJ := by
    show (x.2 + y.2).imJ = _; exact Quaternion.imJ_add _ _
  have h8 : (x + y).2.imK = x.2.imK + y.2.imK := by
    show (x.2 + y.2).imK = _; exact Quaternion.imK_add _ _
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  ring

lemma Octonion.inner_smul_left (r : ℝ) (x z : Octonion) :
    Octonion.inner (r • x) z = r * Octonion.inner x z := by
  rw [octonion_inner_eq_real_dot, octonion_inner_eq_real_dot]
  have h1 : (r • x).1.re = r * x.1.re := by
    show (r • x.1).re = _; exact Quaternion.re_smul _ _
  have h2 : (r • x).1.imI = r * x.1.imI := by
    show (r • x.1).imI = _; exact Quaternion.imI_smul _ _
  have h3 : (r • x).1.imJ = r * x.1.imJ := by
    show (r • x.1).imJ = _; exact Quaternion.imJ_smul _ _
  have h4 : (r • x).1.imK = r * x.1.imK := by
    show (r • x.1).imK = _; exact Quaternion.imK_smul _ _
  have h5 : (r • x).2.re = r * x.2.re := by
    show (r • x.2).re = _; exact Quaternion.re_smul _ _
  have h6 : (r • x).2.imI = r * x.2.imI := by
    show (r • x.2).imI = _; exact Quaternion.imI_smul _ _
  have h7 : (r • x).2.imJ = r * x.2.imJ := by
    show (r • x.2).imJ = _; exact Quaternion.imJ_smul _ _
  have h8 : (r • x).2.imK = r * x.2.imK := by
    show (r • x.2).imK = _; exact Quaternion.imK_smul _ _
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  ring

lemma Octonion.inner_add_right (x y z : Octonion) :
    Octonion.inner x (y + z) = Octonion.inner x y + Octonion.inner x z := by
  rw [Octonion.inner_comm, Octonion.inner_add_left, Octonion.inner_comm x y, Octonion.inner_comm x z]

lemma Octonion.inner_smul_right (r : ℝ) (x y : Octonion) :
    Octonion.inner x (r • y) = r * Octonion.inner x y := by
  rw [Octonion.inner_comm, Octonion.inner_smul_left, Octonion.inner_comm x y]

theorem Octonion.real_part_mul_comm (x y : Octonion) : (x * y).1.re = (y * x).1.re := by
  show (x.1 * y.1 - star y.2 * x.2).re = (y.1 * x.1 - star x.2 * y.2).re
  rw [Quaternion.re_sub, Quaternion.re_sub]
  have h_fst : (x.1 * y.1).re = (y.1 * x.1).re := by
    rw [Quaternion.re_mul, Quaternion.re_mul]; ring
  have h_snd : (star y.2 * x.2).re = (star x.2 * y.2).re := by
    rw [Quaternion.re_mul, Quaternion.re_mul]
    show (star y.2).re * x.2.re - (star y.2).imI * x.2.imI
          - (star y.2).imJ * x.2.imJ - (star y.2).imK * x.2.imK
        = (star x.2).re * y.2.re - (star x.2).imI * y.2.imI
          - (star x.2).imJ * y.2.imJ - (star x.2).imK * y.2.imK
    rw [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
        Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
    ring
  rw [h_fst, h_snd]

private lemma quat_comm_re_zero (p q : Quaternion ℝ) : (p * q - q * p).re = 0 := by
  rw [Quaternion.re_sub, Quaternion.re_mul, Quaternion.re_mul]; ring

theorem Octonion.real_part_assoc (x y z : Octonion) :
    ((x * y) * z).1.re = (x * (y * z)).1.re := by

  set A := x.1
  set B := y.1
  set C := z.1
  set α := x.2
  set β := y.2
  set γ := z.2

  have h_lhs : ((x * y) * z).1 = A * B * C - star β * α * C - star γ * (β * A) - star γ * (α * star B) := by
    show (x * y).1 * z.1 - star z.2 * (x * y).2 = _
    show (A * B - star β * α) * C - star γ * (β * A + α * star B) = _
    noncomm_ring

  have h_rhs : (x * (y * z)).1 = A * B * C - A * (star γ * β) - star B * star γ * α - C * star β * α := by
    show x.1 * (y * z).1 - star (y * z).2 * x.2 = _
    show A * ((y * z).1) - star ((y * z).2) * α = _
    show A * (B * C - star γ * β) - star (γ * B + β * star C) * α = _
    have hstar : star (γ * B + β * star C) =
        star B * star γ + C * star β := by
      rw [StarAddMonoid.star_add (γ * B) (β * star C),
        StarMul.star_mul γ B, StarMul.star_mul β (star C),
        star_involutive C]
    rw [hstar]
    show A * (B * C - star γ * β) - (star B * star γ + C * star β) * α = _
    noncomm_ring

  have h_diff_re : (((x * y) * z).1 - (x * (y * z)).1).re = 0 := by
    rw [h_lhs, h_rhs]
    have e1 : A * B * C - star β * α * C - star γ * (β * A) - star γ * (α * star B)
            - (A * B * C - A * (star γ * β) - star B * star γ * α - C * star β * α)
          = (C * (star β * α) - (star β * α) * C)
            + (A * (star γ * β) - (star γ * β) * A)
            + (star B * (star γ * α) - (star γ * α) * star B) := by noncomm_ring
    rw [e1]
    rw [Quaternion.re_add, Quaternion.re_add]
    rw [show C * (star β * α) - star β * α * C =
      C * (star β * α) - (star β * α) * C from rfl]
    rw [show A * (star γ * β) - (star γ * β) * A = A * (star γ * β) - (star γ * β) * A from rfl]
    rw [show star B * (star γ * α) - (star γ * α) * star B
          = star B * (star γ * α) - (star γ * α) * star B from rfl]
    rw [quat_comm_re_zero C (star β * α)]
    rw [quat_comm_re_zero A (star γ * β)]
    rw [quat_comm_re_zero (star B) (star γ * α)]
    ring

  have : ((x * y) * z).1.re - (x * (y * z)).1.re = 0 := by
    rw [← Quaternion.re_sub]; exact h_diff_re
  linarith

lemma Octonion.inner_eq_mul_star_re (x y : Octonion) :
    Octonion.inner x y = (x * star y).1.re := by
  rw [octonion_inner_eq_real_dot]

  have h_fst : (x * star y).1 = x.1 * star y.1 + star y.2 * x.2 := by
    show x.1 * (star y).1 - star (star y).2 * x.2 = _
    show x.1 * star y.1 - star (-y.2) * x.2 = _
    rw [star_neg, neg_mul, sub_neg_eq_add]
  rw [h_fst, Quaternion.re_add]
  rw [Quaternion.re_mul, Quaternion.re_mul]
  rw [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  rw [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- Reduce an octonion polynomial identity to commutative real polynomial identities. -/
macro "octo_expand_ring" : tactic =>
  `(tactic| {
    try apply Octonion.ext'
    all_goals try apply Quaternion.ext
    all_goals simp only [
      Octonion.mul_fst, Octonion.mul_snd, Octonion.star_fst, Octonion.star_snd,
      Octonion.fst_smul, Octonion.snd_smul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
      Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
      star_trivial, smul_eq_mul]
    all_goals try ring
  })

/-- Reduce an additive octonion polynomial identity to real coordinate identities. -/
macro "octo_expand_ring_add" : tactic =>
  `(tactic| {
    try apply Octonion.ext'
    all_goals try apply Quaternion.ext
    all_goals (try simp only [
      Octonion.mul_fst, Octonion.mul_snd, Octonion.star_fst, Octonion.star_snd,
      Octonion.fst_smul, Octonion.snd_smul,
      Octonion.fst_add, Octonion.snd_add, Octonion.fst_sub, Octonion.snd_sub,
      Octonion.fst_neg, Octonion.snd_neg,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
      Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
      star_trivial, smul_eq_mul])
    all_goals ring
  })

theorem Octonion.left_alternative (x y : Octonion) :
    (x * x) * y = x * (x * y) := by octo_expand_ring

theorem Octonion.right_alternative (x y : Octonion) :
    (y * x) * x = y * (x * x) := by octo_expand_ring

theorem Octonion.flexible (x y : Octonion) :
    (x * y) * x = x * (y * x) := by octo_expand_ring

set_option maxHeartbeats 4000000 in

theorem Octonion.star_alternative (a b : Octonion) :
    (a * star a) * b = a * (star a * b) := by octo_expand_ring_add

set_option maxHeartbeats 4000000 in

theorem Octonion.star_alternative_right (a b : Octonion) :
    (b * a) * star a = b * (a * star a) := by octo_expand_ring_add

set_option maxHeartbeats 4000000 in

theorem Octonion.star_flexible (a b : Octonion) :
    (a * b) * star a = a * (b * star a) := by octo_expand_ring_add

set_option maxHeartbeats 4000000 in

theorem Octonion.mul_mul_star (u v : Octonion) :
    (u * v) * star v = u * (v * star v) := by octo_expand_ring_add

set_option maxHeartbeats 4000000 in

theorem Octonion.mul_star_mul (u v : Octonion) :
    (u * star v) * v = u * (star v * v) := by octo_expand_ring_add

set_option maxHeartbeats 4000000 in

theorem Octonion.mul_star_assoc (u v : Octonion) :
    (v * star v) * u = v * (star v * u) := by octo_expand_ring_add

set_option maxHeartbeats 4000000 in

theorem Octonion.star_mul_assoc (u v : Octonion) :
    (star v * v) * u = star v * (v * u) := by octo_expand_ring_add

set_option maxHeartbeats 4000000 in

theorem Octonion.moufang_left (x y z : Octonion) :
    (x * y * x) * z = x * (y * (x * z)) := by octo_expand_ring

set_option maxHeartbeats 4000000 in

theorem Octonion.moufang_right (x y z : Octonion) :
    z * (x * y * x) = ((z * x) * y) * x := by octo_expand_ring

set_option maxHeartbeats 4000000 in

theorem Octonion.moufang_middle (x y z : Octonion) :
    (x * y) * (z * x) = x * (y * z) * x := by octo_expand_ring
