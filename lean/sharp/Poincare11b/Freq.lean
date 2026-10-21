/-
(H_freq) The frequency representation `J(λ) = (1/π) ∫_0^∞ v^{-2} C_v(λ) dv` (M4 of the sharp L¹ Poincaré
inequality on the Hamming cube).

Proof: for `0 < p < 1`, `ξ_j = (η_j - p)/√(p(1-p))`, so `absMoment p λ = E|S_p|/√(p(1-p))`; by the formula
`|x| = (2/π) ∫_0^∞ (1 - cos(vx)) v^{-2} dv`, `E|S_p| = (2/π) ∫_0^∞ v^{-2} cosGap(v, p) dv`. In `J` substitute
`q = (1 + sin θ)/2`, so `dθ = dq/√(q(1-q))`; the symmetry `q ↔ 1 - q` of `cosGap` doubles the range `(1/2, 1)` of
`θ ∈ (0, π/2)` to `(0, 1)`; Tonelli exchanges the `v`- and `q`-integrals. All integrals are first taken as Lebesgue
integrals of nonnegative functions; finiteness comes from `absMoment ≤ (1 + |λ|²)/2`.
-/
import Poincare11b.Statements
import Poincare11b.M4.AbsCos
import Poincare11b.M4.Arcsin
import Poincare11a.KLe
import Mathlib.MeasureTheory.Measure.Prod

namespace Poincare11b

open Poincare11a MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

namespace M4

lemma xiProb_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) : 0 ≤ xiProb p b := by
  cases b <;> simp [xiProb] <;> linarith

lemma weight_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (z : Cube n) : 0 ≤ ∏ j, xiProb p (z j) :=
  Finset.prod_nonneg (fun j _ => xiProb_nonneg h0 h1 (z j))

/-- `ξ = (η - p)/√(p(1-p))` for `0 < p < 1`. -/
lemma xiVal_eq {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (b : Bool) :
    xiVal p b = (eta b - p) / Real.sqrt (p * (1 - p)) := by
  have h1p : 0 < 1 - p := by linarith
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 (mul_pos h0 h1p)
  rw [eq_div_iff hs.ne']
  cases b
  · simp only [xiVal, eta, Bool.false_eq_true, ite_false, zero_sub, neg_mul, neg_inj]
    rw [← Real.sqrt_mul (div_nonneg h0.le h1p.le), show p / (1 - p) * (p * (1 - p)) = p ^ 2 by
      field_simp, Real.sqrt_sq h0.le]
  · simp only [xiVal, eta, ite_true]
    rw [← Real.sqrt_mul (div_nonneg h1p.le h0.le), show (1 - p) / p * (p * (1 - p)) = (1 - p) ^ 2 by
      field_simp, Real.sqrt_sq h1p.le]

/-- `E|S_p|`, with `S_p = ∑ λ_j (η_j - p)`. -/
noncomputable def eAbs (p : ℝ) (lam : Fin n → ℝ) : ℝ :=
  ∑ z : Cube n, (∏ j, xiProb p (z j)) * |∑ j, lam j * (eta (z j) - p)|

/-- `absMoment p λ = E|S_p| / √(p(1-p))` for `0 < p < 1`. -/
lemma absMoment_eq {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (lam : Fin n → ℝ) :
    absMoment p lam = eAbs p lam / Real.sqrt (p * (1 - p)) := by
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 (mul_pos h0 (by linarith))
  simp only [absMoment, eAbs, Finset.sum_div]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [xiVal_eq h0 h1, mul_div_assoc', ← Finset.sum_div, abs_div, abs_of_pos hs]

lemma continuous_xiProb (b : Bool) : Continuous fun p : ℝ => xiProb p b := by
  cases b <;> simp only [xiProb] <;> fun_prop

lemma continuous_cosGap (lam : Fin n → ℝ) : Continuous fun p : ℝ × ℝ => cosGap p.1 p.2 lam := by
  simp only [cosGap]
  refine continuous_finsetSum _ (fun z _ => ?_)
  refine (continuous_finsetProd _ (fun j _ => (continuous_xiProb (z j)).comp continuous_snd)).mul ?_
  refine continuous_const.sub (Real.continuous_cos.comp (continuous_fst.mul ?_))
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_const.sub continuous_snd))

lemma cosGap_nonneg {v q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (lam : Fin n → ℝ) : 0 ≤ cosGap v q lam := by
  simp only [cosGap]
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (weight_nonneg h0 h1 z)
    (by linarith [Real.cos_le_one (v * ∑ j, lam j * (eta (z j) - q))]))

/-- The involution `z ↦ ¬z` of the cube. -/
def notEquiv : Cube n ≃ Cube n where
  toFun z j := !z j
  invFun z j := !z j
  left_inv z := by funext j; simp
  right_inv z := by funext j; simp

/-- `cosGap` is symmetric under `q ↔ 1 - q` (the law of `S_{1-q}` is that of `-S_q`). -/
lemma cosGap_one_sub (v q : ℝ) (lam : Fin n → ℝ) : cosGap v (1 - q) lam = cosGap v q lam := by
  simp only [cosGap]
  rw [← (notEquiv (n := n)).sum_comp]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [notEquiv, Equiv.coe_fn_mk]
  congr 1
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    cases z j <;> simp [xiProb]
  · have : ∑ j, lam j * (eta (!z j) - (1 - q)) = -∑ j, lam j * (eta (z j) - q) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      cases z j <;> simp only [eta, Bool.not_false, Bool.not_true, ite_true, ite_false,
        Bool.false_eq_true] <;> ring
    rw [this, mul_neg, Real.cos_neg]

/-- `E|S_q| = (2/π) ∫_0^∞ v^{-2} cosGap(v, q) dv`, Lebesgue form, for `0 ≤ q ≤ 1`. -/
lemma ofReal_eAbs {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (lam : Fin n → ℝ) :
    ENNReal.ofReal (eAbs q lam) =
      ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (2 / Real.pi * (cosGap v q lam / v ^ 2)) := by
  have hw := weight_nonneg (n := n) h0 h1
  simp only [eAbs, cosGap]
  rw [ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (hw z) (abs_nonneg _))]
  have hterm : ∀ z : Cube n, ENNReal.ofReal ((∏ j, xiProb q (z j)) * |∑ j, lam j * (eta (z j) - q)|) =
      ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (2 / Real.pi * ((∏ j, xiProb q (z j)) *
        (1 - Real.cos (v * ∑ j, lam j * (eta (z j) - q))) / v ^ 2)) := by
    intro z
    rw [ENNReal.ofReal_mul (hw z), ofReal_abs_eq_lintegral, ← mul_assoc,
      ← ENNReal.ofReal_mul (hw z), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun v => ?_)
    have hc : 0 ≤ (1 - Real.cos (v * ∑ j, lam j * (eta (z j) - q))) / v ^ 2 := by
      have := Real.cos_le_one (v * ∑ j, lam j * (eta (z j) - q))
      positivity
    rw [← ENNReal.ofReal_mul (mul_nonneg (hw z) (by positivity))]
    congr 1
    ring
  simp_rw [hterm]
  rw [← lintegral_finsetSum]
  · refine lintegral_congr (fun v => ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [Finset.sum_div, Finset.mul_sum]
    · intro z _
      have := Real.cos_le_one (v * ∑ j, lam j * (eta (z j) - q))
      have : 0 ≤ 1 - Real.cos (v * ∑ j, lam j * (eta (z j) - q)) := by linarith
      have := hw z
      positivity
  · intro z _
    apply ENNReal.measurable_ofReal.comp
    fun_prop

lemma sqrt_qOf {θ : ℝ} (hθ : θ ∈ halfPi) : Real.sqrt (qOf θ * (1 - qOf θ)) = Real.cos θ / 2 := by
  rw [qOf_mul_one_sub, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq (cos_pos_of_mem hθ).le,
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

/-- `absMoment(q(θ)) = (2/cos θ) E|S_{q(θ)}| = (4/(π cos θ)) ∫_0^∞ v^{-2} cosGap(v, q(θ)) dv`. -/
lemma ofReal_absMoment_qOf {θ : ℝ} (hθ : θ ∈ halfPi) (lam : Fin n → ℝ) :
    ENNReal.ofReal (absMoment (qOf θ) lam) =
      ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (4 / (Real.pi * Real.cos θ) * (cosGap v (qOf θ) lam / v ^ 2)) := by
  have hq := qOf_mem hθ
  have hc := cos_pos_of_mem hθ
  have hE : 0 ≤ eAbs (qOf θ) lam :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (weight_nonneg hq.1.le hq.2.le z) (abs_nonneg _))
  rw [absMoment_eq hq.1 hq.2, sqrt_qOf hθ, div_div_eq_mul_div, mul_div_assoc, mul_comm,
    ENNReal.ofReal_mul (by positivity), ofReal_eAbs hq.1.le hq.2.le,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun v => ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

lemma measurable_cosGap_div (lam : Fin n → ℝ) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal (cosGap p.1 p.2 lam / (p.2 * (1 - p.2))) := by
  apply ENNReal.measurable_ofReal.comp
  exact (continuous_cosGap lam).measurable.div (by fun_prop)

end M4

open M4

/-- **(H_freq)** `J(λ) = (1/π) ∫_0^∞ v^{-2} C_v(λ) dv`, with integrability. -/
theorem hFreq : HFreq := by
  intro n lam
  have hpi : 0 < Real.pi := Real.pi_pos
  -- `L v = ∫_0^1 cosGap(v, q)/(q(1-q)) dq` as a Lebesgue integral
  set L : ℝ → ℝ≥0∞ := fun v => ∫⁻ q in Ioo (0 : ℝ) 1, ENNReal.ofReal (cosGap v q lam / (q * (1 - q)))
    with hL_def
  have hLm : Measurable L := (measurable_cosGap_div lam).lintegral_prod_right'
  -- (1) `C_v = (L v).toReal`
  have hC : ∀ v, Cfreq v lam = (L v).toReal := by
    intro v
    simp only [Cfreq, hL_def]
    refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq => ?_)
      have := cosGap_nonneg (v := v) hq.1.le hq.2.le lam
      have : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
      positivity
    · exact (((continuous_cosGap lam).comp (Continuous.prodMk_right v)).measurable.div
        (by fun_prop)).aestronglyMeasurable
  -- (2) `J = ∫_0^{π/2} absMoment(q(θ)) dθ` as a Lebesgue integral
  set I : ℝ≥0∞ := ∫⁻ θ in Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal (absMoment (qOf θ) lam) with hI_def
  have hJ : J lam = I.toReal := by
    simp only [J, hI_def]
    rw [intervalIntegral.integral_of_le (by positivity), setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
    refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact (absMoment_mem hθ.1.le hθ.2.le lam).1
    · exact (Poincare11a.measurable_absMoment lam).aestronglyMeasurable
  -- (3) Tonelli: `I = ∫_0^∞ L(v)/(π v²) dv`
  have hT : I = ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (1 / (Real.pi * v ^ 2)) * L v := by
    simp only [hI_def]
    have hsub : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2), θ ∈ halfPi :=
      fun θ hθ => ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ofReal_absMoment_qOf (hsub θ hθ) lam)]
    have hm : Measurable (Function.uncurry fun (θ v : ℝ) =>
        ENNReal.ofReal (4 / (Real.pi * Real.cos θ) * (cosGap v (qOf θ) lam / v ^ 2))) := by
      apply ENNReal.measurable_ofReal.comp
      have h1 : Measurable fun p : ℝ × ℝ => cosGap p.2 (qOf p.1) lam :=
        ((continuous_cosGap lam).comp (continuous_snd.prodMk
          (((continuous_const.add Real.continuous_sin).div_const 2 : Continuous qOf).comp
            continuous_fst))).measurable
      exact (measurable_const.div (measurable_const.mul (Real.continuous_cos.measurable.comp
        measurable_fst))).mul (h1.div (by fun_prop))
    rw [lintegral_lintegral_swap hm.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    have hv' : 0 < v := hv
    -- `H θ = 2 cosGap(v, q(θ))/cos θ`
    set H : ℝ → ℝ≥0∞ := fun θ => ENNReal.ofReal (2 * cosGap v (qOf θ) lam / Real.cos θ) with hH_def
    have h1 : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal (4 / (Real.pi * Real.cos θ) * (cosGap v (qOf θ) lam / v ^ 2)) =
          ENNReal.ofReal (2 / (Real.pi * v ^ 2)) * H θ := by
      intro θ hθ
      have hc := cos_pos_of_mem (hsub θ hθ)
      rw [hH_def, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioo h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hLv : L v = 2 * ∫⁻ θ in Ioo (0 : ℝ) (Real.pi / 2), H θ := by
      simp only [hL_def]
      rw [lintegral_Ioo01]
      have h2 : ∀ θ ∈ halfPi, ENNReal.ofReal (Real.cos θ / 2) *
          ENNReal.ofReal (cosGap v (qOf θ) lam / (qOf θ * (1 - qOf θ))) = H θ := by
        intro θ hθ
        have hc := cos_pos_of_mem hθ
        rw [hH_def, ← ENNReal.ofReal_mul (by positivity), qOf_mul_one_sub]
        congr 1
        field_simp
        ring
      rw [setLIntegral_congr_fun measurableSet_Ioo h2]
      refine lintegral_halfPi_of_even H (fun θ => ?_)
      simp only [hH_def, qOf_neg, cosGap_one_sub, Real.cos_neg]
    rw [hLv, ← mul_assoc]
    congr 1
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  -- (4) finiteness: `absMoment ≤ (1 + |λ|²)/2`
  have hfin : I ≠ ∞ := by
    simp only [hI_def]
    refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono (by fun_prop : Measurable fun _ : ℝ =>
      ENNReal.ofReal ((1 + psum lam 2) / 2)) (fun θ hθ => ENNReal.ofReal_le_ofReal
        (absMoment_mem hθ.1.le hθ.2.le lam).2)) ?_)
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top
  -- (5) conclusion
  have hM : ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (1 / (Real.pi * v ^ 2)) * L v ≠ ∞ := by rwa [← hT]
  have hMm : Measurable fun v : ℝ => ENNReal.ofReal (1 / (Real.pi * v ^ 2)) * L v :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hLm
  have hLfin : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), L v ≠ ∞ := by
    filter_upwards [ae_lt_top hMm hM, ae_restrict_mem measurableSet_Ioi] with v hv hv0
    have hv0' : 0 < v := hv0
    intro hLv
    rw [hLv, ENNReal.mul_top (by simp; positivity)] at hv
    exact lt_irrefl _ hv
  have hEq : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (Cfreq v lam / v ^ 2) =
        ENNReal.ofReal Real.pi * (ENNReal.ofReal (1 / (Real.pi * v ^ 2)) * L v) := by
    filter_upwards [hLfin, ae_restrict_mem measurableSet_Ioi] with v hv hv0
    have hv0' : 0 < v := hv0
    rw [hC v, div_eq_mul_one_div, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hv,
      ← mul_assoc, ← ENNReal.ofReal_mul hpi.le, mul_comm]
    congr 2
    field_simp
  have hlint : ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Cfreq v lam / v ^ 2) = ENNReal.ofReal Real.pi * I := by
    rw [lintegral_congr_ae hEq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hT]
  have hmeasC : AEStronglyMeasurable (fun v => Cfreq v lam / v ^ 2) (volume.restrict (Ioi (0 : ℝ))) := by
    have : (fun v => Cfreq v lam / v ^ 2) = fun v => (L v).toReal / v ^ 2 := by
      funext v; rw [hC v]
    rw [this]
    exact (hLm.ennreal_toReal.div (by fun_prop)).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun v => Cfreq v lam / v ^ 2 := by
    refine Filter.Eventually.of_forall (fun v => ?_)
    simp only [Pi.zero_apply]
    rw [hC v]
    positivity
  have hint : IntegrableOn (fun v => Cfreq v lam / v ^ 2) (Ioi 0) := by
    refine ⟨hmeasC, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnonneg, hlint]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeasC, hlint, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hpi.le, hJ]
  field_simp

end Poincare11b
