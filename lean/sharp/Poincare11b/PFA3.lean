/-
Per-frequency Theorem A (PFA), part 3: differentiation of `Φ(t) = C(θ - t; τ(t))` under the integral, the
monotonicity of `Φ` on `[0, min θ]`, the induction on the number of coordinates, and HPFA.
-/
import Poincare11b.PFA2
import Poincare11b.TheoremB

namespace Poincare11b

open Poincare11a Complex Real MeasureTheory Set Filter Finset

variable {n : ℕ}

lemma abs_exp_sub_one_le (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_total 0 x with hx | hx
  · have h1 : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    rw [abs_of_nonneg h3, abs_of_nonneg hx]
    nlinarith [Real.exp_pos x]
  · have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have h2 : Real.exp x ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hx
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hx]
    have h4 : 1 ≤ Real.exp (-x) := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    nlinarith

lemma Gt_le (τ : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : Gt τ q ≤ Real.exp |τ| := by
  unfold Gt
  apply Real.exp_le_exp.mpr
  have hs0 : 0 ≤ q * (1 - q) := mul_nonneg hq.1 (by linarith [hq.2])
  have hs1 : q * (1 - q) ≤ 1 := by nlinarith [hq.1, hq.2]
  have : |τ * (q * (1 - q))| ≤ |τ| := by
    rw [abs_mul, abs_of_nonneg hs0]; exact mul_le_of_le_one_right (abs_nonneg τ) hs1
  have := neg_abs_le (τ * (q * (1 - q)))
  linarith [abs_nonneg τ]

lemma abs_one_sub_Gt_le (τ : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    |1 - Gt τ q| ≤ |τ| * Real.exp |τ| * (q * (1 - q)) := by
  unfold Gt
  have hs0 : 0 ≤ q * (1 - q) := mul_nonneg hq.1 (by linarith [hq.2])
  have hs1 : q * (1 - q) ≤ 1 := by nlinarith [hq.1, hq.2]
  have hx : |(-(τ * (q * (1 - q)) / 2))| ≤ |τ| * (q * (1 - q)) := by
    rw [abs_neg, abs_div, abs_mul, abs_of_nonneg hs0]; norm_num
    nlinarith [abs_nonneg τ]
  have hx' : |(-(τ * (q * (1 - q)) / 2))| ≤ |τ| := hx.trans (mul_le_of_le_one_right (abs_nonneg τ) hs1)
  rw [abs_sub_comm]
  calc |Real.exp (-(τ * (q * (1 - q)) / 2)) - 1|
      ≤ |(-(τ * (q * (1 - q)) / 2))| * Real.exp |(-(τ * (q * (1 - q)) / 2))| := abs_exp_sub_one_le _
    _ ≤ (|τ| * (q * (1 - q))) * Real.exp |τ| := by
        apply mul_le_mul hx (Real.exp_le_exp.mpr hx') (Real.exp_pos _).le (by positivity)
    _ = |τ| * Real.exp |τ| * (q * (1 - q)) := by ring

lemma norm_fcq_le (c : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : ‖fcq c q‖ ≤ |c| + 2 := by
  unfold fcq gc
  have h1 : ‖I * (c : ℂ) * fc c q‖ ≤ |c| := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg c) (norm_fc_le hq)
  have h2 : ‖Complex.exp ((c : ℂ) * q * I) - Complex.exp (-((c : ℂ) * (1 - q)) * I)‖ ≤ 2 := by
    have e1 : ‖Complex.exp ((c : ℂ) * q * I)‖ = 1 := by
      rw [show (c : ℂ) * q * I = ((c * q : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have e2 : ‖Complex.exp (-((c : ℂ) * (1 - q)) * I)‖ = 1 := by
      rw [show -((c : ℂ) * (1 - q)) * I = ((-(c * (1 - q)) : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    calc _ ≤ ‖Complex.exp ((c : ℂ) * q * I)‖ + ‖Complex.exp (-((c : ℂ) * (1 - q)) * I)‖ := norm_sub_le _ _
      _ = 2 := by rw [e1, e2]; norm_num
  calc _ ≤ ‖I * (c : ℂ) * fc c q‖ + ‖Complex.exp ((c : ℂ) * q * I) - Complex.exp (-((c : ℂ) * (1 - q)) * I)‖ :=
        norm_sub_le _ _
    _ ≤ |c| + 2 := add_le_add h1 h2

lemma norm_Fq_le (c : Fin n → ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : ‖Fq c q‖ ≤ ∑ j, (|c j| + 2) := by
  unfold Fq
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul]
  have hP : ‖∏ l ∈ univ.erase j, fc (c l) q‖ ≤ 1 := norm_prod_le_one _ _ (fun l _ => norm_fc_le hq)
  calc ‖∏ l ∈ univ.erase j, fc (c l) q‖ * ‖fcq (c j) q‖ ≤ 1 * (|c j| + 2) :=
        mul_le_mul hP (norm_fcq_le _ hq) (norm_nonneg _) zero_le_one
    _ = |c j| + 2 := one_mul _

/-- `Φ(t) = C(θ - t; τ(t))`. -/
noncomputable def PhiPath (θ : Fin n → ℝ) (τ₀ t : ℝ) : ℝ := Cth (fun j => θ j - t) (tauPath θ τ₀ t)

lemma continuous_Cth_integrand (c : Fin n → ℝ) (τ : ℝ) :
    Continuous (fun q => 1 - Gt τ q * (Fth c q).re) :=
  continuous_const.sub ((continuous_Gt τ).mul (Complex.continuous_re.comp (continuous_Fth c)))

lemma hasDerivAt_PhiPath (θ : Fin n → ℝ) (τ₀ t₀ : ℝ) :
    HasDerivAt (PhiPath θ τ₀)
      (∫ q in Ioo (0 : ℝ) 1, Gt (tauPath θ τ₀ t₀) q * (Fq (fun j => θ j - t₀) q).im) t₀ := by
  set T : ℝ := |τ₀| + ∑ j, θ j ^ 2 + ∑ j, (|θ j| + |t₀| + 1) ^ 2 with hT
  set B : ℝ := Real.exp T * ∑ j, (|θ j| + |t₀| + 3) with hB
  have hball : ∀ x ∈ Metric.ball t₀ 1, |tauPath θ τ₀ x| ≤ T ∧ ∀ j, |θ j - x| ≤ |θ j| + |t₀| + 1 := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have hj : ∀ j, |θ j - x| ≤ |θ j| + |t₀| + 1 := by
      intro j
      calc |θ j - x| ≤ |θ j| + |x| := abs_sub _ _
        _ ≤ |θ j| + (|t₀| + 1) := by
            have := abs_sub_abs_le_abs_sub x t₀
            linarith
        _ = |θ j| + |t₀| + 1 := by ring
    refine ⟨?_, hj⟩
    unfold tauPath
    have h1 : ∑ j, (θ j - x) ^ 2 ≤ ∑ j, (|θ j| + |t₀| + 1) ^ 2 := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      rw [← sq_abs (θ j - x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hj j) 2
    have h2 : 0 ≤ ∑ j, (θ j - x) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h3 : 0 ≤ ∑ j, θ j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    rw [abs_le]; constructor
    · linarith [neg_abs_le τ₀]
    · linarith [le_abs_self τ₀]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))
    (F := fun x q => (1 - Gt (tauPath θ τ₀ x) q * (Fth (fun j => θ j - x) q).re) / (q * (1 - q)))
    (F' := fun x q => Gt (tauPath θ τ₀ x) q * (Fq (fun j => θ j - x) q).im)
    (x₀ := t₀) (bound := fun _ => B) (Metric.ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall (fun x => (measurable_div_s (continuous_Cth_integrand _ _)).aestronglyMeasurable))
    ?_ ?_ ?_ (integrable_const B) ?_
  · exact key.2
  · -- integrability at t₀
    set c : Fin n → ℝ := fun j => θ j - t₀
    set τ : ℝ := tauPath θ τ₀ t₀
    refine (integrableOn_Ioo01 (measurable_div_s (continuous_Cth_integrand c τ))
      (|τ| * Real.exp |τ| + Real.exp |τ| * (2 * ∑ j, |c j|)) (fun q hq => ?_))
    have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
    have hs : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    have h1 := abs_one_sub_Gt_le τ hq'
    have h2 : |1 - (Fth c q).re| ≤ 2 * (∑ j, |c j|) * (q * (1 - q)) := by
      calc |1 - (Fth c q).re| = |(Fth c q - 1).re| := by
            rw [Complex.sub_re, Complex.one_re, abs_sub_comm]
        _ ≤ ‖Fth c q - 1‖ := Complex.abs_re_le_norm _
        _ ≤ _ := norm_Fth_sub_one_le c hq'
    have h3 : 0 < Gt τ q := Gt_pos τ q
    have h4 := Gt_le τ hq'
    have e : 1 - Gt τ q * (Fth c q).re = (1 - Gt τ q) + Gt τ q * (1 - (Fth c q).re) := by ring
    rw [e]
    calc |(1 - Gt τ q) + Gt τ q * (1 - (Fth c q).re)|
        ≤ |1 - Gt τ q| + Gt τ q * |1 - (Fth c q).re| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_pos h3]
      _ ≤ |τ| * Real.exp |τ| * (q * (1 - q)) + Real.exp |τ| * (2 * (∑ j, |c j|) * (q * (1 - q))) := by
          apply add_le_add h1
          exact mul_le_mul h4 h2 (abs_nonneg _) (Real.exp_pos _).le
      _ = (|τ| * Real.exp |τ| + Real.exp |τ| * (2 * ∑ j, |c j|)) * (q * (1 - q)) := by ring
  · exact (((continuous_Gt _).mul (Complex.continuous_im.comp (continuous_Fq _))).measurable).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq x hx => ?_)
    have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
    obtain ⟨hτx, hθx⟩ := hball x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Gt_pos _ _)]
    have hG : Gt (tauPath θ τ₀ x) q ≤ Real.exp T :=
      (Gt_le _ hq').trans (Real.exp_le_exp.mpr hτx)
    have hF : |(Fq (fun j => θ j - x) q).im| ≤ ∑ j, (|θ j| + |t₀| + 3) := by
      refine (Complex.abs_im_le_norm _).trans ((norm_Fq_le _ hq').trans (Finset.sum_le_sum (fun j _ => ?_)))
      have := hθx j
      linarith
    exact mul_le_mul hG hF (abs_nonneg _) (Real.exp_pos _).le
  · exact ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq x _ => hasDerivAt_integrand θ τ₀ x hq)

lemma tauPath_nonneg {θ : Fin n → ℝ} {τ₀ t₁ t : ℝ} (hθ : ∀ j, t₁ ≤ θ j)
    (ht0 : 0 ≤ t) (ht1 : t ≤ t₁) : τ₀ ≤ tauPath θ τ₀ t := by
  unfold tauPath
  have : ∑ j, (θ j - t) ^ 2 ≤ ∑ j, θ j ^ 2 :=
    Finset.sum_le_sum (fun j _ => by nlinarith [hθ j])
  linarith

/-- One segment of the equal-subtraction path: `C(θ; τ₀) ≤ C(θ - t₁; τ(t₁))` when `0 ≤ t₁ ≤ min θ`. -/
lemma segment {θ : Fin n → ℝ} {τ₀ t₁ : ℝ} (hτ₀ : 0 ≤ τ₀) (ht₁ : 0 ≤ t₁) (hθ : ∀ j, t₁ ≤ θ j) :
    Cth θ τ₀ ≤ Cth (fun j => θ j - t₁) (tauPath θ τ₀ t₁) := by
  have hmono : MonotoneOn (PhiPath θ τ₀) (Icc 0 t₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t₁)
    · exact fun t _ => (hasDerivAt_PhiPath θ τ₀ t).continuousAt.continuousWithinAt
    · exact fun t _ => (hasDerivAt_PhiPath θ τ₀ t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_PhiPath θ τ₀ t).deriv]
      apply psi_nonneg
      · intro j; linarith [hθ j, ht.2]
      · exact hτ₀.trans (tauPath_nonneg hθ ht.1.le ht.2.le)
  have h := hmono ⟨le_rfl, ht₁⟩ ⟨ht₁, le_rfl⟩ ht₁
  have e0 : PhiPath θ τ₀ 0 = Cth θ τ₀ := by
    unfold PhiPath tauPath; simp
  rw [e0] at h
  exact h

/-- Theorem PFA: `C(θ; τ) ≤ C_G(|θ|² + τ)` for `θ ≥ 0`, `τ ≥ 0`. -/
theorem pfa_main : ∀ (n : ℕ) (θ : Fin n → ℝ), (∀ j, 0 ≤ θ j) → ∀ τ : ℝ, 0 ≤ τ →
    Cth θ τ ≤ CGt (∑ j, θ j ^ 2 + τ)
  | 0, θ, _, τ, _ => by simp [Cth, CGt, Fth]
  | n + 1, θ, hθ, τ, hτ => by
    have IH := pfa_main n
    have caseA : ∀ θ' : Fin (n + 1) → ℝ, (∀ j, 0 ≤ θ' j) → ∀ τ', 0 ≤ τ' → (∃ i, θ' i = 0) →
        Cth θ' τ' ≤ CGt (∑ j, θ' j ^ 2 + τ') := by
      rintro θ' hθ' τ' hτ' ⟨i, hi⟩
      have hF : ∀ q, Fth θ' q = Fth (fun j => θ' (i.succAbove j)) q := by
        intro q; unfold Fth; rw [Fin.prod_univ_succAbove _ i, hi, fc_zero_c, one_mul]
      have hS : ∑ j, θ' j ^ 2 = ∑ j, (θ' (i.succAbove j)) ^ 2 := by
        rw [Fin.sum_univ_succAbove _ i, hi]; simp
      have hC : Cth θ' τ' = Cth (fun j => θ' (i.succAbove j)) τ' := by
        unfold Cth; simp_rw [hF]
      rw [hC, hS]
      exact IH _ (fun j => hθ' _) τ' hτ'
    by_cases hz : ∃ i, θ i = 0
    · exact caseA θ hθ τ hτ hz
    · push Not at hz
      have hpos : ∀ j, 0 < θ j := fun j => lt_of_le_of_ne (hθ j) (Ne.symm (hz j))
      obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty θ
      set t₁ := Finset.univ.inf' Finset.univ_nonempty θ with ht₁
      have hle : ∀ j, t₁ ≤ θ j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
      have ht₁0 : 0 ≤ t₁ := by rw [hj₀]; exact (hpos j₀).le
      have hseg := segment hτ ht₁0 hle
      have hτ1 : 0 ≤ tauPath θ τ t₁ := hτ.trans (tauPath_nonneg hle ht₁0 le_rfl)
      have hA := caseA (fun j => θ j - t₁) (fun j => by linarith [hle j]) _ hτ1
        ⟨j₀, by rw [hj₀]; ring⟩
      have hsum : ∑ j, (θ j - t₁) ^ 2 + tauPath θ τ t₁ = ∑ j, θ j ^ 2 + τ := by
        unfold tauPath; ring
      rw [hsum] at hA
      exact hseg.trans hA

/-- HPFA: Theorem A at every frequency for nonnegative directions, `C_v(λ) ≤ C_G(v|λ|)`. -/
theorem hPFA : HPFA := by
  intro n lam v hlam hv
  have h1 : Cfreq v lam = Cth (fun j => v * lam j) 0 := by
    unfold Cfreq Cth
    refine setIntegral_congr_fun measurableSet_Ioo (fun q _ => ?_)
    rw [cosGap_eq, ← map_prod, Complex.conj_re]
    unfold Gt Fth
    simp
  have h2 := pfa_main n (fun j => v * lam j) (fun j => mul_nonneg hv.le (hlam j)) 0 le_rfl
  have h3 : CGt (∑ j, (v * lam j) ^ 2 + 0) = CG (v * vnorm lam) := by
    have e : (v * vnorm lam) ^ 2 = ∑ j, (v * lam j) ^ 2 := by
      unfold vnorm
      rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _)), Finset.mul_sum]
      congr 1; funext j; ring
    unfold CGt CG Gt
    rw [add_zero, ← e]
  rw [h1]
  rw [h3] at h2
  exact h2

end Poincare11b
