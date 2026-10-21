/-
Per-frequency Theorem A (PFA), part 2: the sign lemma.
`Ψ(θ, τ) = ∫_0^1 G_τ(q) Im ∂_q F_θ(q) dq = ∫_0^1 G_τ''(q) I_θ(q) dq ≥ 0` for `θ ≥ 0`, `τ ≥ 0`,
with `I_θ(q) = ∫_0^q Im F_θ ≥ 0` from the sine series of HSSL.
-/
import Poincare11b.PFA1
import Poincare11b.SSL

namespace Poincare11b

open Complex Real MeasureTheory Set Filter Finset

variable {n : ℕ}

lemma continuous_fcq (c : ℝ) : Continuous (fun q => fcq c q) := by
  unfold fcq gc fc; fun_prop

lemma continuous_Fq (c : Fin n → ℝ) : Continuous (Fq c) := by
  unfold Fq
  refine continuous_finsetSum _ (fun j _ => Continuous.mul ?_ (continuous_fcq _))
  exact continuous_finsetProd _ (fun l _ => continuous_fc' _)

lemma Gt_pos (τ q : ℝ) : 0 < Gt τ q := Real.exp_pos _

/-- `G_τ'(q)`. -/
noncomputable def Gt1 (τ q : ℝ) : ℝ := Gt τ q * (-(τ * (1 - 2 * q)) / 2)

/-- `G_τ''(q) = G_τ(q) (τ²(1-2q)²/4 + τ)`. -/
noncomputable def Gt2 (τ q : ℝ) : ℝ := Gt τ q * ((τ * (1 - 2 * q) / 2) ^ 2 + τ)

lemma hasDerivAt_Gt (τ q : ℝ) : HasDerivAt (Gt τ) (Gt1 τ q) q := by
  have h1 : HasDerivAt (fun q : ℝ => -(τ * (q * (1 - q)) / 2)) (-(τ * (1 - 2 * q)) / 2) q := by
    have h2 : HasDerivAt (fun q : ℝ => q * (1 - q)) (1 - 2 * q) q := by
      have := (hasDerivAt_id' q).fun_mul ((hasDerivAt_id' q).const_sub 1)
      convert this using 1; ring
    have := ((h2.const_mul τ).div_const 2).fun_neg
    convert this using 1; ring
  have := h1.exp
  unfold Gt1 Gt
  convert this using 1

lemma hasDerivAt_Gt1 (τ q : ℝ) : HasDerivAt (Gt1 τ) (Gt2 τ q) q := by
  have h1 : HasDerivAt (fun q : ℝ => -(τ * (1 - 2 * q)) / 2) τ q := by
    have := ((((hasDerivAt_id q).const_mul 2).const_sub 1).const_mul τ).fun_neg.div_const 2
    convert this using 1; simp; ring
  have := (hasDerivAt_Gt τ q).fun_mul h1
  have e : Gt1 τ = fun i => Gt τ i * (-(τ * (1 - 2 * i)) / 2) := rfl
  rw [e]
  convert this using 1
  unfold Gt2 Gt1; ring

lemma continuous_Gt (τ : ℝ) : Continuous (Gt τ) := by unfold Gt; fun_prop
lemma continuous_Gt1 (τ : ℝ) : Continuous (Gt1 τ) := by unfold Gt1 Gt; fun_prop
lemma continuous_Gt2 (τ : ℝ) : Continuous (Gt2 τ) := by unfold Gt2 Gt; fun_prop

lemma Gt2_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (q : ℝ) : 0 ≤ Gt2 τ q :=
  mul_nonneg (Gt_pos τ q).le (by positivity)

lemma hasDerivAt_im_Fth (c : Fin n → ℝ) (q : ℝ) :
    HasDerivAt (fun q => (Fth c q).im) (Fq c q).im q :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt q (hasDerivAt_Fth_q c q)

lemma integral_sin_mul (a q : ℝ) (ha : a ≠ 0) :
    ∫ r in (0 : ℝ)..q, Real.sin (a * r) = (1 - Real.cos (a * q)) / a := by
  have h := intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) (a := 0) (b := q) ha
  simp only [mul_zero, smul_eq_mul] at h
  rw [h, integral_sin, Real.cos_zero]
  field_simp

/-- `I_θ(q) = ∫_0^q Im F_θ ≥ 0` on `[0,1]`, and `I_θ(1) = 0`. -/
lemma I_props (θ : Fin n → ℝ) (hθ : ∀ j, 0 ≤ θ j) :
    (∀ q ∈ Icc (0 : ℝ) 1, 0 ≤ ∫ r in (0 : ℝ)..q, (Fth θ r).im) ∧ ∫ r in (0 : ℝ)..1, (Fth θ r).im = 0 := by
  obtain ⟨β, hβ0, hβs, hβ⟩ := sine_series θ hθ
  have key : ∀ q ∈ Icc (0 : ℝ) 1, HasSum (fun k : ℕ => β k * ((1 - Real.cos (2 * Real.pi * ((k : ℝ) + 1) * q)) /
      (2 * Real.pi * ((k : ℝ) + 1)))) (∫ r in (0 : ℝ)..q, (Fth θ r).im) := by
    intro q hq
    have hs := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := q)
      (F := fun k r => β k * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * r)) (f := fun r => (Fth θ r).im)
      (fun k _ => β k) (fun k => by
        exact (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun k => Eventually.of_forall (fun r _ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hβ0 k)]
        exact mul_le_of_le_one_right (hβ0 k) (Real.abs_sin_le_one _)))
      (Eventually.of_forall (fun r _ => hβs))
      intervalIntegrable_const
      (Eventually.of_forall (fun r hr => by
        have hr' : r ∈ Icc (0 : ℝ) 1 := by
          rw [uIoc_of_le hq.1] at hr
          exact ⟨hr.1.le, hr.2.trans hq.2⟩
        exact hβ r hr'))
    refine hs.congr_fun (fun k => ?_)
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hk : 2 * Real.pi * ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [← integral_sin_mul _ q hk]
  refine ⟨fun q hq => (key q hq).nonneg (fun k => mul_nonneg (hβ0 k)
    (div_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * ((k : ℝ) + 1) * q)]) (by positivity))), ?_⟩
  have h1 := key 1 ⟨zero_le_one, le_rfl⟩
  have h0 : HasSum (fun k : ℕ => β k * ((1 - Real.cos (2 * Real.pi * ((k : ℝ) + 1) * 1)) /
      (2 * Real.pi * ((k : ℝ) + 1)))) 0 := by
    have : (fun k : ℕ => β k * ((1 - Real.cos (2 * Real.pi * ((k : ℝ) + 1) * 1)) /
        (2 * Real.pi * ((k : ℝ) + 1)))) = fun _ => 0 := by
      funext k
      have : Real.cos (2 * Real.pi * ((k : ℝ) + 1) * 1) = 1 := by
        rw [show 2 * Real.pi * ((k : ℝ) + 1) * 1 = ((k + 1 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
        exact Real.cos_nat_mul_two_pi _
      rw [this]; simp
    rw [this]; exact hasSum_zero
  exact h1.unique h0

/-- The sign lemma: `Ψ(θ, τ) = ∫_0^1 G_τ Im ∂_q F_θ ≥ 0` for `θ ≥ 0`, `τ ≥ 0`. -/
theorem psi_nonneg (θ : Fin n → ℝ) (hθ : ∀ j, 0 ≤ θ j) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ ∫ q in Ioo (0 : ℝ) 1, Gt τ q * (Fq θ q).im := by
  obtain ⟨hI0, hI1⟩ := I_props θ hθ
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  set v : ℝ → ℝ := fun q => (Fth θ q).im with hv
  set I : ℝ → ℝ := fun q => ∫ r in (0 : ℝ)..q, v r with hIdef
  have hvc : Continuous v := Complex.continuous_im.comp (continuous_Fth θ)
  have hIderiv : ∀ q, HasDerivAt I (v q) q := fun q => (hvc.integral_hasStrictDerivAt 0 q).hasDerivAt
  have hv0 : v 0 = 0 := by simp [hv, Fth_zero]
  have hv1 : v 1 = 0 := by simp [hv, Fth_one]
  have hIat0 : I 0 = 0 := by simp [hIdef]
  have hIat1 : I 1 = 0 := hI1
  -- first integration by parts: ∫ G v' = -∫ G' v
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := Gt τ) (u' := Gt1 τ) (v := v) (v' := fun q => (Fq θ q).im)
    (fun q _ => hasDerivAt_Gt τ q) (fun q _ => hasDerivAt_im_Fth θ q)
    ((continuous_Gt1 τ).intervalIntegrable _ _)
    ((Complex.continuous_im.comp (continuous_Fq θ)).intervalIntegrable _ _)
  -- second integration by parts: ∫ G' v = ∫ G' I' = -∫ G'' I
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := Gt1 τ) (u' := Gt2 τ) (v := I) (v' := v)
    (fun q _ => hasDerivAt_Gt1 τ q) (fun q _ => hIderiv q)
    ((continuous_Gt2 τ).intervalIntegrable _ _) (hvc.intervalIntegrable _ _)
  rw [ibp1, hv0, hv1, ibp2, hIat0, hIat1]
  simp only [mul_zero, sub_zero, zero_sub, neg_neg]
  refine intervalIntegral.integral_nonneg zero_le_one (fun q hq => ?_)
  exact mul_nonneg (Gt2_nonneg hτ q) (hI0 q hq)

end Poincare11b
