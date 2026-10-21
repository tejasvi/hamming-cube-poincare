/-
(H_G) The Gaussian frequency integral `∫_0^∞ v^{-2} C_G(vρ) dv = π √(π/2) ρ` (M4 of the sharp L¹ Poincaré
inequality on the Hamming cube).

Proof: `(1 - e^{-k c})/k = ∫_0^c e^{-k u} du` with `k = q(1-q) v²` and `c = ρ²/2` turns the integrand into a
triple integral of `e^{-u q(1-q) v²} ≥ 0`; by Tonelli the `v`-integral is Gaussian, `√(π/(u q(1-q)))/2`, and
`∫_0^1 dq/√(q(1-q)) = π`, `∫_0^c du/(2√u) = √c`.
-/
import Poincare11b.Statements
import Poincare11b.M4.Arcsin
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Poincare11b

open MeasureTheory Set
open scoped ENNReal

namespace M4

/-- `∫_0^c e^{-k u} du = (1 - e^{-k c})/k` for `k > 0`, `c ≥ 0`, as a Lebesgue integral over `(0, c)`. -/
lemma lintegral_exp_neg_mul {k c : ℝ} (hk : 0 < k) (hc : 0 ≤ c) :
    ∫⁻ u in Ioo (0 : ℝ) c, ENNReal.ofReal (Real.exp (-(k * u))) =
      ENNReal.ofReal ((1 - Real.exp (-(k * c))) / k) := by
  have hcont : Continuous fun u : ℝ => Real.exp (-(k * u)) := by fun_prop
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-(k * u))) (Ioc 0 c) :=
    hcont.integrableOn_Ioc
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)), ← intervalIntegral.integral_of_le hc]
  congr 1
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) c,
      HasDerivAt (fun u : ℝ => -Real.exp (-(k * u)) / k) (Real.exp (-(k * u))) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => -(k * u)) (-k) u := by
      have := ((hasDerivAt_id u).const_mul k).neg
      simp only [id, mul_one] at this
      exact this
    have h2 := (h1.exp.neg).div_const k
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- `∫_0^c du / (2√u) · √π = √(π c)`. -/
lemma lintegral_sqrt_div {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ u in Ioo (0 : ℝ) c, ENNReal.ofReal (Real.sqrt (Real.pi / u) / 2) =
      ENNReal.ofReal (Real.sqrt (Real.pi * c)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  -- on `(0, c)`: `√(π/u)/2 = (√π/2) u^{-1/2}`
  have e : ∀ u ∈ Ioo (0 : ℝ) c, ENNReal.ofReal (Real.sqrt (Real.pi / u) / 2) =
      ENNReal.ofReal (Real.sqrt Real.pi / 2) * ENNReal.ofReal (u ^ (-(1 / 2 : ℝ))) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.sqrt_div' _ hu0.le, Real.sqrt_eq_rpow u, Real.rpow_neg hu0.le]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioo e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hint : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Ioc 0 c) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) (r := -(1 / 2 : ℝ)) (by norm_num)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1 this
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => Real.rpow_nonneg hu.1.le _)),
    ← intervalIntegral.integral_of_le hc,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.zero_rpow (by norm_num), sub_zero, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hpi.le]
  field_simp

/-- The Gaussian integral `∫_0^∞ e^{-b v²} dv = √(π/b)/2`, Lebesgue form. -/
lemma lintegral_gaussian {b : ℝ} (hb : 0 < b) :
    ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-b * v ^ 2)) =
      ENNReal.ofReal (Real.sqrt (Real.pi / b) / 2) := by
  rw [← integral_gaussian_Ioi b, ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_sq hb).integrableOn
    (Filter.Eventually.of_forall (fun v => (Real.exp_pos _).le))]

/-- The integrand of the triple integral. -/
noncomputable def gTriple (v q u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(u * (q * (1 - q))) * v ^ 2))

lemma measurable_gTriple : Measurable fun p : (ℝ × ℝ) × ℝ => gTriple p.1.1 p.1.2 p.2 := by
  apply ENNReal.measurable_ofReal.comp
  apply Continuous.measurable
  fun_prop

/-- The inner `u`-integral: the integrand of `C_G(vρ)/v²` for `v > 0`, `q ∈ (0, 1)`. -/
lemma ofReal_CG_integrand {v q ρ : ℝ} (hv : 0 < v) (hq : q ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal ((1 - Real.exp (-((v * ρ) ^ 2 * (q * (1 - q)) / 2))) / (q * (1 - q)) / v ^ 2) =
      ∫⁻ u in Ioo (0 : ℝ) (ρ ^ 2 / 2), gTriple v q u := by
  have hs : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
  have hk : 0 < q * (1 - q) * v ^ 2 := by positivity
  simp only [gTriple]
  have e : ∀ u : ℝ, Real.exp (-(u * (q * (1 - q))) * v ^ 2) = Real.exp (-(q * (1 - q) * v ^ 2 * u)) := by
    intro u
    congr 1
    ring
  simp_rw [e]
  rw [lintegral_exp_neg_mul hk (by positivity)]
  congr 1
  rw [div_div]
  congr 2
  ring_nf

end M4

open M4

/-- **(H_G)** `∫_0^∞ v^{-2} C_G(vρ) dv = π √(π/2) ρ`, with integrability. -/
theorem hG : HG := by
  intro ρ hρ
  set c : ℝ := ρ ^ 2 / 2 with hc_def
  have hc : 0 ≤ c := by positivity
  -- `Φ v = ∫_0^1 ∫_0^c e^{-u q(1-q) v²} du dq`
  set Φ : ℝ → ℝ≥0∞ := fun v => ∫⁻ q in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo (0 : ℝ) c, gTriple v q u with hΦ_def
  have hΦm : Measurable Φ := by
    have h1 : Measurable fun p : ℝ × ℝ => ∫⁻ u in Ioo (0 : ℝ) c, gTriple p.1 p.2 u :=
      measurable_gTriple.lintegral_prod_right'
    exact h1.lintegral_prod_right'
  -- `C_G(vρ)/v² = (Φ v).toReal` for `v > 0`
  have hCG : ∀ v ∈ Ioi (0 : ℝ), CG (v * ρ) / v ^ 2 = (Φ v).toReal := by
    intro v hv
    have hv' : 0 < v := hv
    simp only [CG, hΦ_def]
    rw [← integral_div]
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      refine setLIntegral_congr_fun measurableSet_Ioo (fun q hq => ?_)
      exact ofReal_CG_integrand hv' hq
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq => ?_)
      have hs : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
      have : Real.exp (-((v * ρ) ^ 2 * (q * (1 - q)) / 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (v * ρ) ^ 2 * (q * (1 - q)) / 2 := by positivity
        linarith
      have h1 : 0 ≤ 1 - Real.exp (-((v * ρ) ^ 2 * (q * (1 - q)) / 2)) := by linarith
      positivity
    · apply Measurable.aestronglyMeasurable
      apply Measurable.div_const
      apply Measurable.div
      · exact measurable_const.sub (Real.measurable_exp.comp (by fun_prop))
      · fun_prop
  -- the triple integral, by Tonelli
  have hTonelli : ∫⁻ v in Ioi (0 : ℝ), Φ v = ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / 2) * ρ) := by
    simp only [hΦ_def]
    -- swap `v` and `q`
    have hm1 : Measurable (Function.uncurry fun (v q : ℝ) => ∫⁻ u in Ioo (0 : ℝ) c, gTriple v q u) :=
      measurable_gTriple.lintegral_prod_right'
    rw [lintegral_lintegral_swap hm1.aemeasurable]
    -- swap `v` and `u` inside, for each `q`
    have hq_eq : ∀ q ∈ Ioo (0 : ℝ) 1, ∫⁻ v in Ioi (0 : ℝ), ∫⁻ u in Ioo (0 : ℝ) c, gTriple v q u =
        ENNReal.ofReal (1 / Real.sqrt (q * (1 - q))) * ENNReal.ofReal (Real.sqrt (Real.pi * c)) := by
      intro q hq
      have hs : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
      have hm2 : Measurable (Function.uncurry fun (v u : ℝ) => gTriple v q u) := by
        apply ENNReal.measurable_ofReal.comp
        apply Continuous.measurable
        fun_prop
      rw [lintegral_lintegral_swap hm2.aemeasurable]
      have hu_eq : ∀ u ∈ Ioo (0 : ℝ) c, ∫⁻ v in Ioi (0 : ℝ), gTriple v q u =
          ENNReal.ofReal (1 / Real.sqrt (q * (1 - q))) * ENNReal.ofReal (Real.sqrt (Real.pi / u) / 2) := by
        intro u hu
        have hus : 0 < u * (q * (1 - q)) := mul_pos hu.1 hs
        simp only [gTriple]
        rw [lintegral_gaussian hus, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.sqrt_div' _ hus.le, Real.sqrt_mul hu.1.le, Real.sqrt_div' _ hu.1.le]
        have h1 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu.1
        have h2 : 0 < Real.sqrt (q * (1 - q)) := Real.sqrt_pos.2 hs
        field_simp
      rw [setLIntegral_congr_fun measurableSet_Ioo hu_eq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_sqrt_div hc]
    rw [setLIntegral_congr_fun measurableSet_Ioo hq_eq, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      lintegral_inv_sqrt, ← ENNReal.ofReal_mul Real.pi_pos.le]
    congr 1
    rw [hc_def, show Real.pi * (ρ ^ 2 / 2) = (Real.pi / 2) * ρ ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hρ]
    ring
  have hfin : ∫⁻ v in Ioi (0 : ℝ), Φ v ≠ ∞ := by rw [hTonelli]; exact ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), Φ v < ∞ := ae_lt_top hΦm hfin
  have hae : (fun v => CG (v * ρ) / v ^ 2) =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun v => (Φ v).toReal :=
    ae_restrict_of_forall_mem measurableSet_Ioi hCG
  have hint : IntegrableOn (fun v => CG (v * ρ) / v ^ 2) (Ioi 0) :=
    (integrable_toReal_of_lintegral_ne_top hΦm.aemeasurable hfin).congr hae.symm
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae hae, integral_toReal hΦm.aemeasurable hlt, hTonelli,
    ENNReal.toReal_ofReal (by positivity)]

end Poincare11b
