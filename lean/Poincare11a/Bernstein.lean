/-
Soundness of the positivity check `Poly.posOK` (Bernstein subdivision): a polynomial that passes it is a majorant
of `|z|`.
-/
import Poincare11a.Prims

namespace Poincare11a.Cert

/-- The degree-6 Bernstein form with coefficients `b` at `τ`. -/
def B7.eval (b : B7) (τ : ℝ) : ℝ :=
  b.c0 * (1 - τ) ^ 6 + 6 * b.c1 * τ * (1 - τ) ^ 5 + 15 * b.c2 * τ ^ 2 * (1 - τ) ^ 4 +
    20 * b.c3 * τ ^ 3 * (1 - τ) ^ 3 + 15 * b.c4 * τ ^ 4 * (1 - τ) ^ 2 + 6 * b.c5 * τ ^ 5 * (1 - τ) +
    b.c6 * τ ^ 6

lemma B7.eval_left (b : B7) (τ : ℝ) : b.left.eval τ = 64 * b.eval (τ / 2) := by
  simp only [B7.left, B7.eval]; push_cast; ring

lemma B7.eval_right (b : B7) (τ : ℝ) : b.right.eval τ = 64 * b.eval ((1 + τ) / 2) := by
  simp only [B7.right, B7.eval]; push_cast; ring

lemma B7.eval_pos_of_allPos (b : B7) (h : b.allPos = true) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    0 < b.eval τ := by
  simp only [B7.allPos, Bool.and_eq_true, ipos_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h0', h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩, h6'⟩ := h
  have e0 : (1 : ℝ) ≤ b.c0 := by exact_mod_cast h0'
  have e1 : (1 : ℝ) ≤ b.c1 := by exact_mod_cast h1'
  have e2 : (1 : ℝ) ≤ b.c2 := by exact_mod_cast h2'
  have e3 : (1 : ℝ) ≤ b.c3 := by exact_mod_cast h3'
  have e4 : (1 : ℝ) ≤ b.c4 := by exact_mod_cast h4'
  have e5 : (1 : ℝ) ≤ b.c5 := by exact_mod_cast h5'
  have e6 : (1 : ℝ) ≤ b.c6 := by exact_mod_cast h6'
  have hs : 0 ≤ 1 - τ := by linarith
  have k0 : 0 ≤ (1 - τ) ^ 6 := by positivity
  have k1 : 0 ≤ τ * (1 - τ) ^ 5 := by positivity
  have k2 : 0 ≤ τ ^ 2 * (1 - τ) ^ 4 := by positivity
  have k3 : 0 ≤ τ ^ 3 * (1 - τ) ^ 3 := by positivity
  have k4 : 0 ≤ τ ^ 4 * (1 - τ) ^ 2 := by positivity
  have k5 : 0 ≤ τ ^ 5 * (1 - τ) := by positivity
  have k6 : 0 ≤ τ ^ 6 := by positivity
  have hsum : (1 - τ) ^ 6 + 6 * (τ * (1 - τ) ^ 5) + 15 * (τ ^ 2 * (1 - τ) ^ 4) + 20 * (τ ^ 3 * (1 - τ) ^ 3) +
      15 * (τ ^ 4 * (1 - τ) ^ 2) + 6 * (τ ^ 5 * (1 - τ)) + τ ^ 6 = 1 := by ring
  have : b.eval τ ≥ (1 - τ) ^ 6 + 6 * (τ * (1 - τ) ^ 5) + 15 * (τ ^ 2 * (1 - τ) ^ 4) +
      20 * (τ ^ 3 * (1 - τ) ^ 3) + 15 * (τ ^ 4 * (1 - τ) ^ 2) + 6 * (τ ^ 5 * (1 - τ)) + τ ^ 6 := by
    simp only [B7.eval]
    nlinarith [mul_le_mul_of_nonneg_right e0 k0, mul_le_mul_of_nonneg_right e1 k1,
      mul_le_mul_of_nonneg_right e2 k2, mul_le_mul_of_nonneg_right e3 k3,
      mul_le_mul_of_nonneg_right e4 k4, mul_le_mul_of_nonneg_right e5 k5,
      mul_le_mul_of_nonneg_right e6 k6]
  linarith

theorem posB_sound : ∀ (fuel : ℕ) (b : B7), posB fuel b = true →
    ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → 0 < b.eval τ
  | 0, b, h, τ, h0, h1 => B7.eval_pos_of_allPos b h τ h0 h1
  | fuel + 1, b, h, τ, h0, h1 => by
    simp only [posB] at h
    cases ha : b.allPos
    · rw [ha] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨_, hl⟩, hr⟩ := h
      rcases le_total τ (1 / 2) with hτ | hτ
      · have := posB_sound fuel b.left hl (2 * τ) (by linarith) (by linarith)
        rw [B7.eval_left, show 2 * τ / 2 = τ by ring] at this
        linarith
      · have := posB_sound fuel b.right hr (2 * τ - 1) (by linarith) (by linarith)
        rw [B7.eval_right, show (1 + (2 * τ - 1)) / 2 = τ by ring] at this
        linarith
    · exact B7.eval_pos_of_allPos b ha τ h0 h1

/-- The polynomial `h(z) = a + b z² + c z⁴ + d z⁶` with `(a, b, c, d) = (A, B, C, D)/DLIB`. -/
noncomputable def Poly.h (p : Poly) (z : ℝ) : ℝ :=
  ((p.A : ℝ) + p.B * z ^ 2 + p.C * z ^ 4 + p.D * z ^ 6) / (DLIB : ℝ)

lemma DLIB_pos : (0 : ℝ) < (DLIB : ℝ) := by norm_num [DLIB]

lemma Poly.bern_eval (p : Poly) (s : ℝ) :
    p.bern.eval s = 90 * (p.A * (1 - s) ^ 6 - DLIB * s * (1 - s) ^ 5 + p.B * s ^ 2 * (1 - s) ^ 4 +
      p.C * s ^ 4 * (1 - s) ^ 2 + p.D * s ^ 6) := by
  simp only [Poly.bern, B7.eval]; push_cast; ring

/-- A polynomial that passes `posOK` satisfies `H(u) = A - DLIB·u + B u² + C u⁴ + D u⁶ > 0` on `[0, ∞)`. -/
lemma Poly.H_pos (p : Poly) (hp : p.posOK = true) (u : ℝ) (hu : 0 ≤ u) :
    0 < (p.A : ℝ) - DLIB * u + p.B * u ^ 2 + p.C * u ^ 4 + p.D * u ^ 6 := by
  have h1u : 0 < 1 + u := by linarith
  set s := u / (1 + u) with hs
  have hs0 : 0 ≤ s := div_nonneg hu h1u.le
  have hs1 : s ≤ 1 := (div_le_one h1u).2 (by linarith)
  have hpos := posB_sound 40 p.bern hp s hs0 hs1
  rw [Poly.bern_eval] at hpos
  have h1s : 1 - s = 1 / (1 + u) := by rw [hs]; field_simp; ring
  have key : (p.A : ℝ) - DLIB * u + p.B * u ^ 2 + p.C * u ^ 4 + p.D * u ^ 6 =
      (1 + u) ^ 6 * (p.A * (1 - s) ^ 6 - DLIB * s * (1 - s) ^ 5 + p.B * s ^ 2 * (1 - s) ^ 4 +
        p.C * s ^ 4 * (1 - s) ^ 2 + p.D * s ^ 6) := by
    rw [h1s, hs]; field_simp
  rw [key]
  have : 0 < (p.A * (1 - s) ^ 6 - DLIB * s * (1 - s) ^ 5 + p.B * s ^ 2 * (1 - s) ^ 4 +
      p.C * s ^ 4 * (1 - s) ^ 2 + p.D * s ^ 6 : ℝ) := by linarith
  positivity

/-- A polynomial that passes `posOK` is a majorant of `|z|`. -/
theorem Poly.abs_le_h (p : Poly) (hp : p.posOK = true) (z : ℝ) : |z| ≤ p.h z := by
  have hH := p.H_pos hp |z| (abs_nonneg z)
  have e2 : |z| ^ 2 = z ^ 2 := sq_abs z
  have e4 : |z| ^ 4 = z ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e2, ← pow_mul]
  have e6 : |z| ^ 6 = z ^ 6 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, e2, ← pow_mul]
  rw [e2, e4, e6] at hH
  rw [Poly.h, le_div_iff₀ DLIB_pos]
  linarith

/-- The leading coefficient of a polynomial that passes `posOK` is positive. -/
theorem Poly.D_pos (p : Poly) (hp : p.posOK = true) : 0 < p.D := by
  have h := posB_sound 40 p.bern hp 1 zero_le_one le_rfl
  rw [Poly.bern_eval] at h
  norm_num at h
  exact_mod_cast h

end Poincare11a.Cert
