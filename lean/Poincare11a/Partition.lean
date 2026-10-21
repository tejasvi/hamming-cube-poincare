/-
The θ-partition: `θ = 2 arctan (T / 2^32)` has rational sine and cosine; enclosures of `v = 4/cos²θ` and lower
bounds of the interval widths that are checked by `Ivl.ok`.
-/
import Poincare11a.Checker
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace Poincare11a.Cert

open Real

/-- The partition point `θ = 2 arctan (T/2^32)`. -/
noncomputable def thetaOf (T : Int) : ℝ := 2 * Real.arctan ((T : ℝ) / (P32 : ℝ))

lemma sin_two_arctan (t : ℝ) : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have h : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  field_simp
  rw [h2]

lemma cos_two_arctan (t : ℝ) : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_arctan]
  have h : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  field_simp
  rw [h2]; ring

lemma P32_pos : (0 : ℝ) < (P32 : ℝ) := by norm_num [P32]
lemma P64_eq : (P64 : ℝ) = (P32 : ℝ) ^ 2 := by norm_num [P64, P32]

lemma thetaOf_P32 : thetaOf P32 = π / 2 := by
  rw [thetaOf, div_self P32_pos.ne', Real.arctan_one]; ring

lemma thetaOf_zero : thetaOf 0 = 0 := by simp [thetaOf]

lemma thetaOf_strictMono {T T' : Int} (h : T < T') : thetaOf T < thetaOf T' := by
  unfold thetaOf
  have : (T : ℝ) / P32 < (T' : ℝ) / P32 := div_lt_div_of_pos_right (by exact_mod_cast h) P32_pos
  linarith [Real.arctan_strictMono this]

lemma thetaOf_nonneg {T : Int} (h : 0 ≤ T) : 0 ≤ thetaOf T := by
  rw [← thetaOf_zero]; rcases h.lt_or_eq with h | h
  · exact (thetaOf_strictMono h).le
  · rw [h]

lemma thetaOf_le_pi_div_two {T : Int} (h : T ≤ P32) : thetaOf T ≤ π / 2 := by
  rw [← thetaOf_P32]; rcases h.lt_or_eq with h | h
  · exact (thetaOf_strictMono h).le
  · rw [h]

/-- `cos θ_T = (2^64 - T²)/(2^64 + T²)`. -/
lemma cos_thetaOf (T : Int) :
    Real.cos (thetaOf T) = ((P64 : ℝ) - (T : ℝ) ^ 2) / ((P64 : ℝ) + (T : ℝ) ^ 2) := by
  rw [thetaOf, cos_two_arctan, P64_eq]
  have := P32_pos
  field_simp

/-- `sin θ_T = 2 · 2^32 · T/(2^64 + T²)`. -/
lemma sin_thetaOf (T : Int) :
    Real.sin (thetaOf T) = 2 * (P32 : ℝ) * T / ((P64 : ℝ) + (T : ℝ) ^ 2) := by
  rw [thetaOf, sin_two_arctan, P64_eq]
  have := P32_pos
  field_simp

section IvlFacts

variable (iv : Ivl) (h : iv.ok = true)
include h

lemma Ivl.ok_facts :
    0 ≤ iv.TL ∧ iv.TL < iv.TR ∧ iv.TR ≤ P32 ∧
    iv.VL * ((P64 - iv.TL * iv.TL) * (P64 - iv.TL * iv.TL)) ≤ 4 * VSC * ((P64 + iv.TL * iv.TL) * (P64 + iv.TL * iv.TL)) ∧
    (iv.TR = P32 ∨ 4 * VSC * ((P64 + iv.TR * iv.TR) * (P64 + iv.TR * iv.TR)) ≤
      iv.VH * ((P64 - iv.TR * iv.TR) * (P64 - iv.TR * iv.TR))) ∧
    0 ≤ iv.LL ∧
    iv.LL * ((P64 + iv.TL * iv.TL) * (P64 + iv.TR * iv.TR)) ≤
      P64 * (2 * P32) * ((iv.TR - iv.TL) * (P64 + iv.TL * iv.TR)) ∧
    iv.w6l = (iv.VL - 6 * VSC) * VSC ∧ iv.w4l = (iv.VL - 4 * VSC) * VSC ∧
    iv.w30l = iv.VL * iv.VL - 30 * VSC * iv.VL + 120 * VSC * VSC ∧
    iv.w6h = (iv.VH - 6 * VSC) * VSC ∧ iv.w4h = (iv.VH - 4 * VSC) * VSC ∧
    iv.w30h = iv.VH * iv.VH - 30 * VSC * iv.VH + 120 * VSC * VSC := by
  simp only [Ivl.ok, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  tauto

/-- Interval widths are bounded below by `LL / 2^64`. -/
lemma Ivl.LL_le_width : (iv.LL : ℝ) / (P64 : ℝ) ≤ thetaOf iv.TR - thetaOf iv.TL := by
  obtain ⟨h0, hlt, hle, -, -, -, hLL, -⟩ := iv.ok_facts h
  have hw : 0 ≤ thetaOf iv.TR - thetaOf iv.TL := (sub_pos.2 (thetaOf_strictMono hlt)).le
  have hsin : Real.sin (thetaOf iv.TR - thetaOf iv.TL) ≤ thetaOf iv.TR - thetaOf iv.TL := Real.sin_le hw
  rw [Real.sin_sub, sin_thetaOf, sin_thetaOf, cos_thetaOf, cos_thetaOf] at hsin
  have hP64 : (0 : ℝ) < P64 := by norm_num [P64]
  have hpl : (0 : ℝ) < (P64 : ℝ) + (iv.TL : ℝ) ^ 2 := add_pos_of_pos_of_nonneg hP64 (sq_nonneg _)
  have hpr : (0 : ℝ) < (P64 : ℝ) + (iv.TR : ℝ) ^ 2 := add_pos_of_pos_of_nonneg hP64 (sq_nonneg _)
  have hLLr : (iv.LL : ℝ) * (((P64 : ℝ) + iv.TL * iv.TL) * ((P64 : ℝ) + iv.TR * iv.TR)) ≤
      (P64 : ℝ) * (2 * P32) * ((iv.TR - iv.TL) * (P64 + iv.TL * iv.TR)) := by exact_mod_cast hLL
  refine le_trans ?_ hsin
  rw [div_le_iff₀ hP64]
  have e : (2 * (P32 : ℝ) * iv.TR / ((P64 : ℝ) + (iv.TR : ℝ) ^ 2) * (((P64 : ℝ) - (iv.TL : ℝ) ^ 2) /
      ((P64 : ℝ) + (iv.TL : ℝ) ^ 2)) - ((P64 : ℝ) - (iv.TR : ℝ) ^ 2) / ((P64 : ℝ) + (iv.TR : ℝ) ^ 2) *
      (2 * (P32 : ℝ) * iv.TL / ((P64 : ℝ) + (iv.TL : ℝ) ^ 2))) =
      2 * P32 * ((iv.TR - iv.TL) * (P64 + iv.TL * iv.TR)) / ((P64 + iv.TL * iv.TL) * (P64 + iv.TR * iv.TR)) := by
    field_simp; ring
  have hprod : (0 : ℝ) < ((P64 : ℝ) + iv.TL * iv.TL) * ((P64 : ℝ) + iv.TR * iv.TR) := by
    rw [← sq, ← sq]; exact mul_pos hpl hpr
  rw [e, div_mul_eq_mul_div, le_div_iff₀ hprod]
  nlinarith [hLLr]

/-- On the open interval, `cos θ > 0` and `VL ≤ VSC · 4/cos²θ`. -/
lemma Ivl.VL_le (θ : ℝ) (hθ : θ ∈ Set.Ioo (thetaOf iv.TL) (thetaOf iv.TR)) :
    0 < Real.cos θ ∧ (iv.VL : ℝ) ≤ (VSC : ℝ) * (4 / Real.cos θ ^ 2) := by
  obtain ⟨h0, hlt, hle, hVL, -, -, -, -⟩ := iv.ok_facts h
  have hθ0 : 0 ≤ thetaOf iv.TL := thetaOf_nonneg h0
  have hθ1 : thetaOf iv.TR ≤ π / 2 := thetaOf_le_pi_div_two hle
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2]⟩
  refine ⟨hcos, ?_⟩
  have hcl : Real.cos θ < Real.cos (thetaOf iv.TL) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos, hθ.2]) hθ.1
  rw [cos_thetaOf] at hcl
  have hP64 : (0 : ℝ) < P64 := by norm_num [P64]
  have hpl : (0 : ℝ) < (P64 : ℝ) + (iv.TL : ℝ) ^ 2 := add_pos_of_pos_of_nonneg hP64 (sq_nonneg _)
  have hTL : (iv.TL : ℝ) < P32 := by exact_mod_cast lt_of_lt_of_le hlt hle
  have hcl0 : (0 : ℝ) < (P64 : ℝ) - (iv.TL : ℝ) ^ 2 := by
    rw [P64_eq]; have : (0 : ℝ) ≤ iv.TL := by exact_mod_cast h0
    nlinarith
  have hVLr : (iv.VL : ℝ) * (((P64 : ℝ) - iv.TL * iv.TL) * ((P64 : ℝ) - iv.TL * iv.TL)) ≤
      4 * VSC * (((P64 : ℝ) + iv.TL * iv.TL) * ((P64 : ℝ) + iv.TL * iv.TL)) := by exact_mod_cast hVL
  -- cos θ < cl/pl, so 4/cos²θ > 4 pl²/cl² ≥ VL/VSC
  have hc2 : Real.cos θ ^ 2 < (((P64 : ℝ) - (iv.TL : ℝ) ^ 2) / ((P64 : ℝ) + (iv.TL : ℝ) ^ 2)) ^ 2 :=
    pow_lt_pow_left₀ hcl hcos.le two_ne_zero
  have hVSC : (0 : ℝ) < VSC := by norm_num [VSC]
  rw [div_pow, lt_div_iff₀ (by positivity)] at hc2
  rw [div_eq_mul_inv, ← mul_assoc, le_mul_inv_iff₀ (by positivity)]
  nlinarith [hVLr, mul_le_mul_of_nonneg_left hc2.le (by positivity : (0 : ℝ) ≤ (iv.VL : ℝ) ⊔ 0)]

/-- On the open interval with `TR < 2^32`, `VSC · 4/cos²θ ≤ VH`. -/
lemma Ivl.le_VH (θ : ℝ) (hθ : θ ∈ Set.Ioo (thetaOf iv.TL) (thetaOf iv.TR)) (hTR : iv.TR < P32) :
    (VSC : ℝ) * (4 / Real.cos θ ^ 2) ≤ (iv.VH : ℝ) := by
  obtain ⟨h0, hlt, hle, -, hVH, -, -, -⟩ := iv.ok_facts h
  have hVH' : 4 * VSC * ((P64 + iv.TR * iv.TR) * (P64 + iv.TR * iv.TR)) ≤
      iv.VH * ((P64 - iv.TR * iv.TR) * (P64 - iv.TR * iv.TR)) := by
    rcases hVH with h' | h'
    · exact absurd h' (ne_of_lt hTR)
    · exact h'
  have hθ0 : 0 ≤ thetaOf iv.TL := thetaOf_nonneg h0
  have hθ1 : thetaOf iv.TR ≤ π / 2 := thetaOf_le_pi_div_two hle
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2]⟩
  have hcr : Real.cos (thetaOf iv.TR) < Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [Real.pi_pos]) hθ.2
  rw [cos_thetaOf] at hcr
  have hP64 : (0 : ℝ) < P64 := by norm_num [P64]
  have hpr : (0 : ℝ) < (P64 : ℝ) + (iv.TR : ℝ) ^ 2 := add_pos_of_pos_of_nonneg hP64 (sq_nonneg _)
  have hTR0 : (0 : ℝ) ≤ iv.TR := by exact_mod_cast (h0.trans hlt.le)
  have hTRr : (iv.TR : ℝ) < P32 := by exact_mod_cast hTR
  have hcr0 : (0 : ℝ) < (P64 : ℝ) - (iv.TR : ℝ) ^ 2 := by rw [P64_eq]; nlinarith
  have hVHr : 4 * (VSC : ℝ) * (((P64 : ℝ) + iv.TR * iv.TR) * ((P64 : ℝ) + iv.TR * iv.TR)) ≤
      (iv.VH : ℝ) * (((P64 : ℝ) - iv.TR * iv.TR) * ((P64 : ℝ) - iv.TR * iv.TR)) := by exact_mod_cast hVH'
  have hq : 0 < ((P64 : ℝ) - (iv.TR : ℝ) ^ 2) / ((P64 : ℝ) + (iv.TR : ℝ) ^ 2) := div_pos hcr0 hpr
  have hc2 : (((P64 : ℝ) - (iv.TR : ℝ) ^ 2) / ((P64 : ℝ) + (iv.TR : ℝ) ^ 2)) ^ 2 < Real.cos θ ^ 2 :=
    pow_lt_pow_left₀ hcr hq.le two_ne_zero
  have hVSC : (0 : ℝ) < VSC := by norm_num [VSC]
  rw [div_pow, div_lt_iff₀ (by positivity)] at hc2
  rw [show (VSC : ℝ) * (4 / Real.cos θ ^ 2) = 4 * VSC / Real.cos θ ^ 2 by ring, div_le_iff₀ (by positivity)]
  have hpr2 : 0 < ((P64 : ℝ) + (iv.TR : ℝ) ^ 2) ^ 2 := by positivity
  have hVH0 : 0 ≤ (iv.VH : ℝ) := by
    have : 0 < 4 * (VSC : ℝ) * (((P64 : ℝ) + iv.TR * iv.TR) * ((P64 : ℝ) + iv.TR * iv.TR)) := by
      rw [← sq]; positivity
    have h1' : 0 < (P64 : ℝ) - iv.TR * iv.TR := by nlinarith [hcr0]
    have h2 : 0 < ((P64 : ℝ) - iv.TR * iv.TR) * ((P64 : ℝ) - iv.TR * iv.TR) := mul_pos h1' h1'
    by_contra hneg; push Not at hneg
    nlinarith
  -- 4 VSC pr² ≤ VH cr² and cr² < cos²θ pr²  ⇒  4 VSC < VH cos²θ
  have e1 : 4 * (VSC : ℝ) * ((P64 : ℝ) + (iv.TR : ℝ) ^ 2) ^ 2 ≤ (iv.VH : ℝ) * ((P64 : ℝ) - (iv.TR : ℝ) ^ 2) ^ 2 := by
    nlinarith [hVHr]
  have e2 : (iv.VH : ℝ) * ((P64 : ℝ) - (iv.TR : ℝ) ^ 2) ^ 2 ≤ (iv.VH : ℝ) * (Real.cos θ ^ 2 * ((P64 : ℝ) + (iv.TR : ℝ) ^ 2) ^ 2) :=
    mul_le_mul_of_nonneg_left hc2.le hVH0
  have e3 : 4 * (VSC : ℝ) * ((P64 : ℝ) + (iv.TR : ℝ) ^ 2) ^ 2 ≤ (iv.VH * Real.cos θ ^ 2) * ((P64 : ℝ) + (iv.TR : ℝ) ^ 2) ^ 2 := by
    nlinarith [e1, e2]
  exact le_of_mul_le_mul_right e3 hpr2

end IvlFacts

end Poincare11a.Cert
