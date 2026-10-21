/-
The formula `|x| = (2/π) ∫_0^∞ (1 - cos(v x)) / v² dv` (M4 of the sharp L¹ Poincaré inequality on the Hamming
cube), through `1/v² = ∫_0^∞ t e^{-vt} dt`, Tonelli, and the Laplace transform of `cos`.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Prod

namespace Poincare11b.M4

open MeasureTheory Set

/-- `∫_0^∞ t e^{-vt} dt = 1/v²`. -/
lemma integral_mul_exp_neg {v : ℝ} (hv : 0 < v) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(v * t)) = 1 / v ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := v) two_pos hv
  have hG : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    simp
  rw [show (2 : ℝ) - 1 = 1 by norm_num, hG, mul_one, Real.rpow_two, div_pow, one_pow] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only [Real.rpow_one]

lemma integrableOn_mul_exp_neg {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(v * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := v) (by norm_num) one_pos hv
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

/-- `∫_0^∞ e^{-tv} cos(v x) dv = t / (t² + x²)`. -/
lemma integral_exp_neg_mul_cos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * Real.cos (v * x) = t / (t ^ 2 + x ^ 2) := by
  set a : ℂ := -(t : ℂ) + x * Complex.I with ha_def
  have ha : a.re < 0 := by simp [ha_def, ht]
  have h1 : ∀ v : ℝ, Real.exp (-(t * v)) * Real.cos (v * x) = (Complex.exp (a * v)).re := by
    intro v
    rw [Complex.exp_re]
    congr 1
    · congr 1
      simp [ha_def, Complex.mul_re]
    · congr 1
      simp [ha_def, Complex.mul_im]
      ring
  simp_rw [h1, ← RCLike.re_to_complex]
  rw [integral_re (integrableOn_exp_mul_complex_Ioi ha 0), integral_exp_mul_complex_Ioi ha 0,
    RCLike.re_to_complex]
  have hden : (t : ℝ) ^ 2 + x ^ 2 ≠ 0 := by positivity
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [Complex.div_re]
  simp [ha_def, Complex.normSq_apply]
  field_simp

lemma integrableOn_exp_neg_mul_cos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntegrableOn (fun v : ℝ => Real.exp (-(t * v)) * Real.cos (v * x)) (Ioi 0) := by
  have hi : IntegrableOn (fun v : ℝ => Real.exp (-t * v)) (Ioi 0) := integrableOn_exp_mul_Ioi (by linarith) 0
  refine hi.mono'
    (by fun_prop : Continuous fun v : ℝ => Real.exp (-(t * v)) * Real.cos (v * x)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- `∫_0^∞ e^{-tv} (1 - cos(v x)) dv = x² / (t (t² + x²))`. -/
lemma integral_exp_neg_mul_one_sub_cos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * (1 - Real.cos (v * x)) = x ^ 2 / (t * (t ^ 2 + x ^ 2)) := by
  have hi : IntegrableOn (fun v : ℝ => Real.exp (-(t * v))) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0
  have h0 : ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) = 1 / t := by
    have := integral_exp_mul_Ioi (a := -t) (by linarith) 0
    simp only [mul_zero, Real.exp_zero, neg_mul] at this
    rw [this]
    field_simp
  simp_rw [mul_sub, mul_one]
  rw [integral_sub hi (integrableOn_exp_neg_mul_cos ht x), h0, integral_exp_neg_mul_cos ht x]
  have hden : (t : ℝ) ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma integrableOn_exp_neg_mul_one_sub_cos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntegrableOn (fun v : ℝ => Real.exp (-(t * v)) * (1 - Real.cos (v * x))) (Ioi 0) := by
  have hi : IntegrableOn (fun v : ℝ => Real.exp (-(t * v))) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0
  simp_rw [mul_sub, mul_one]
  exact hi.sub (integrableOn_exp_neg_mul_cos ht x)

/-- `∫_0^∞ x² / (t² + x²) dt = (π/2) |x|`. -/
lemma integral_sq_div_sq_add_sq (x : ℝ) :
    IntegrableOn (fun t : ℝ => x ^ 2 / (t ^ 2 + x ^ 2)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), x ^ 2 / (t ^ 2 + x ^ 2) = Real.pi / 2 * |x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hax : 0 < |x| := abs_pos.2 hx
  have e : ∀ t : ℝ, x ^ 2 / (t ^ 2 + x ^ 2) = (1 + (|x|⁻¹ * t) ^ 2)⁻¹ := by
    intro t
    have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    rw [hx2]
    field_simp
    ring
  simp_rw [e]
  refine ⟨(integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hax.ne')).integrableOn, ?_⟩
  rw [integral_comp_mul_left_Ioi (fun w => (1 + w ^ 2)⁻¹) 0 (inv_pos.2 hax), mul_zero,
    integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, inv_inv, smul_eq_mul]
  ring

/-- **The `1 - cos` formula, Lebesgue-integral form.** `∫_0^∞ (1 - cos(v x))/v² dv = (π/2)|x|`. -/
theorem lintegral_one_sub_cos (x : ℝ) :
    ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (v * x)) / v ^ 2) =
      ENNReal.ofReal (Real.pi / 2 * |x|) := by
  -- `(1 - cos(vx))/v² = ∫_0^∞ t e^{-vt} (1 - cos(vx)) dt` for `v > 0`
  have step1 : ∀ v ∈ Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (v * x)) / v ^ 2) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * Real.exp (-(v * t)) * (1 - Real.cos (v * x))) := by
    intro v hv
    have hc : 0 ≤ 1 - Real.cos (v * x) := by linarith [Real.cos_le_one (v * x)]
    have hint := integrableOn_mul_exp_neg hv
    rw [div_eq_mul_one_div, ← integral_mul_exp_neg hv, ENNReal.ofReal_mul hc,
      ofReal_integral_eq_lintegral_ofReal hint
        (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => mul_nonneg (le_of_lt ht)
          (Real.exp_pos _).le)), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun t => ?_)
    rw [← ENNReal.ofReal_mul hc]
    ring_nf
  rw [setLIntegral_congr_fun measurableSet_Ioi step1]
  -- Tonelli
  have hmeas : Measurable (Function.uncurry fun v t : ℝ =>
      ENNReal.ofReal (t * Real.exp (-(v * t)) * (1 - Real.cos (v * x)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  -- the inner integral: `t ∫_0^∞ e^{-tv} (1 - cos(vx)) dv = x²/(t² + x²)`
  have step2 : ∀ t ∈ Ioi (0 : ℝ),
      ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (t * Real.exp (-(v * t)) * (1 - Real.cos (v * x))) =
        ENNReal.ofReal (x ^ 2 / (t ^ 2 + x ^ 2)) := by
    intro t ht
    have ht' : 0 < t := ht
    have h1 : ∀ v : ℝ, ENNReal.ofReal (t * Real.exp (-(v * t)) * (1 - Real.cos (v * x))) =
        ENNReal.ofReal t * ENNReal.ofReal (Real.exp (-(t * v)) * (1 - Real.cos (v * x))) := by
      intro v
      rw [← ENNReal.ofReal_mul ht'.le, mul_comm v t]
      ring_nf
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_mul_one_sub_cos ht' x)
        (Filter.Eventually.of_forall (fun v => mul_nonneg (Real.exp_pos _).le
          (by linarith [Real.cos_le_one (v * x)]))),
      integral_exp_neg_mul_one_sub_cos ht' x, ← ENNReal.ofReal_mul ht'.le]
    congr 1
    have hden : (t : ℝ) ^ 2 + x ^ 2 ≠ 0 := by positivity
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi step2]
  obtain ⟨hint, hval⟩ := integral_sq_div_sq_add_sq x
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun t => by positivity)), hval]

/-- `ofReal |x| = (2/π) ∫_0^∞ (1 - cos(v x))/v² dv`, the form used for `E|S|`. -/
theorem ofReal_abs_eq_lintegral (x : ℝ) :
    ENNReal.ofReal |x| =
      ENNReal.ofReal (2 / Real.pi) * ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (v * x)) / v ^ 2) := by
  rw [lintegral_one_sub_cos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end Poincare11b.M4
