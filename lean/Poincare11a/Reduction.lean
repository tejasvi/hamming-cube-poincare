/-
Paper Theorem 2.2 (first inequality): E|f − Ef| ≤ E_y[ |∇f(y)| J(∇f(y)/|∇f(y)|) ], by the fundamental theorem of
calculus for θ ↦ P(sin θ, x) (Lemma 2.1 in θ-form), the triangle inequality and the bijection x ↦ x ⊙ z.
-/
import Poincare11a.KLe

namespace Poincare11a

open Finset Poincare11a.Cert MeasureTheory Set

variable {n : ℕ}

lemma absMoment_smul (p r : ℝ) (lam : Fin n → ℝ) :
    absMoment p (fun j => r * lam j) = |r| * absMoment p lam := by
  unfold absMoment
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  have : ∑ j, r * lam j * xiVal p (z j) = r * ∑ j, lam j * xiVal p (z j) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this, abs_mul]; ring

lemma J_smul (r : ℝ) (lam : Fin n → ℝ) : J (fun j => r * lam j) = |r| * J lam := by
  unfold J
  simp_rw [absMoment_smul]
  rw [intervalIntegral.integral_const_mul]

lemma J_grad (f : Cube n → ℝ) (y : Cube n) :
    J (grad f y) = gradNorm f y * J (fun j => D f j y / gradNorm f y) := by
  by_cases h : gradNorm f y = 0
  · have hz : ∀ j, D f j y = 0 := by
      intro j
      have h2 : ∑ j, D f j y ^ 2 = 0 := by
        have := Real.sqrt_eq_zero'.1 h
        exact le_antisymm this (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (D f i y))).1 h2 j (Finset.mem_univ j)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    rw [h, zero_mul]
    have : grad f y = fun j => (0 : ℝ) * D f j y := funext fun j => by simp [grad, hz j]
    rw [this, J_smul, abs_zero, zero_mul]
  · have hpos : 0 < gradNorm f y := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h)
    have : grad f y = fun j => gradNorm f y * (D f j y / gradNorm f y) :=
      funext fun j => by simp only [grad]; field_simp
    rw [this, J_smul, abs_of_pos hpos]

lemma continuous_wt (b : Bool) : Continuous (fun m => wt m b) := by
  cases b <;> simp only [wt, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

lemma continuous_dPsg (f : Cube n → ℝ) (x : Cube n) : Continuous (fun m => dPsg f m x) := by
  unfold dPsg Wk
  refine continuous_finsetSum _ (fun z _ => Continuous.mul ?_ continuous_const)
  refine continuous_finsetSum _ (fun k _ => Continuous.mul ?_ continuous_const)
  exact continuous_finsetProd _ (fun j _ => continuous_wt (z j))

lemma continuous_G (f : Cube n → ℝ) (x : Cube n) :
    Continuous (fun θ => Real.cos θ * dPsg f (Real.sin θ) x) :=
  Real.continuous_cos.mul ((continuous_dPsg f x).comp Real.continuous_sin)

/-- Lemma 2.1 in θ-form: `f(x) − Ef = ∫_0^{π/2} cos θ · ∂_m P(sin θ, x) dθ`. -/
lemma f_sub_avg_eq_integral (f : Cube n → ℝ) (x : Cube n) :
    f x - avg f = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ * dPsg f (Real.sin θ) x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => Psg f (Real.sin θ) x)
    (fun θ _ => hasDerivAt_Psg_sin f x θ) ((continuous_G f x).intervalIntegrable _ _)]
  simp only [Real.sin_pi_div_two, Real.sin_zero, Psg_one, Psg_zero]

/-- Paper Theorem 2.2, first inequality. -/
theorem reduction (n : ℕ) (f : Cube n → ℝ) :
    avg (fun x => |f x - avg f|) ≤ avg (fun y => gradNorm f y * J (fun j => D f j y / gradNorm f y)) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hG : ∀ x, IntervalIntegrable (fun θ => |Real.cos θ * dPsg f (Real.sin θ) x|) volume 0 (Real.pi / 2) :=
    fun x => ((continuous_G f x).abs).intervalIntegrable _ _
  have hA : ∀ y, IntervalIntegrable (fun θ => absMoment ((1 + Real.sin θ) / 2) (grad f y)) volume 0 (Real.pi / 2) :=
    fun y => J_intervalIntegrable (grad f y)
  have main : ∑ x, |f x - avg f| ≤ ∑ y, J (grad f y) := by
    calc ∑ x, |f x - avg f|
        ≤ ∑ x, ∫ θ in (0 : ℝ)..(Real.pi / 2), |Real.cos θ * dPsg f (Real.sin θ) x| :=
          Finset.sum_le_sum (fun x _ => by
            rw [f_sub_avg_eq_integral]; exact intervalIntegral.abs_integral_le_integral_abs hpi)
      _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), ∑ x, |Real.cos θ * dPsg f (Real.sin θ) x| :=
          (intervalIntegral.integral_finsetSum (fun x _ => hG x)).symm
      _ ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), ∑ y, absMoment ((1 + Real.sin θ) / 2) (grad f y) := by
          have i1 : IntervalIntegrable (fun θ => ∑ x, |Real.cos θ * dPsg f (Real.sin θ) x|) volume 0 (Real.pi / 2) := by
            convert IntervalIntegrable.sum Finset.univ (fun x _ => hG x) using 1
            ext θ; simp [Finset.sum_apply]
          have i2 : IntervalIntegrable (fun θ => ∑ y, absMoment ((1 + Real.sin θ) / 2) (grad f y)) volume 0
              (Real.pi / 2) := by
            convert IntervalIntegrable.sum Finset.univ (fun y _ => hA y) using 1
            ext θ; simp [Finset.sum_apply]
          refine intervalIntegral.integral_mono_on_of_le_Ioo hpi i1 i2 (fun θ hθ => ?_)
          have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
          have hcm : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
          calc ∑ x, |Real.cos θ * dPsg f (Real.sin θ) x| ≤ ∑ y, Phi (Real.sin θ) (Real.cos θ) (grad f y) :=
                sum_abs_dPsg_le hc.ne' hcm (Real.neg_one_le_sin θ) (Real.sin_le_one θ) f
            _ = ∑ y, absMoment ((1 + Real.sin θ) / 2) (grad f y) :=
                Finset.sum_congr rfl (fun y _ => (absMoment_eq_Phi hc (grad f y)).symm)
      _ = ∑ y, J (grad f y) := by
          rw [intervalIntegral.integral_finsetSum (fun y _ => hA y)]; rfl
  have main' : ∑ x, |f x - avg f| ≤ ∑ y, gradNorm f y * J (fun j => D f j y / gradNorm f y) := by
    simpa only [J_grad] using main
  unfold avg
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  exact div_le_div_of_nonneg_right main' h2.le

end Poincare11a

namespace Poincare11a

/-- The paper's route to Theorem 1.1 (Theorem 2.2 + Theorem 4.2), given `K_le` for all unit vectors. -/
theorem poincare_of_reduction (hK : ∀ (m : ℕ) (lam : Fin m → ℝ), ∑ j, lam j ^ 2 = 1 → J lam ≤ 71 / 50)
    {n : ℕ} (f : Cube n → ℝ) : avg (fun x => |f x - avg f|) ≤ 71 / 50 * avg (gradNorm f) := by
  refine (reduction n f).trans ?_
  unfold avg
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity), Finset.mul_sum]
  refine Finset.sum_le_sum (fun y _ => ?_)
  by_cases h : gradNorm f y = 0
  · rw [h]; simp
  · have hpos : 0 < gradNorm f y := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h)
    have hunit : ∑ j, (D f j y / gradNorm f y) ^ 2 = 1 := by
      simp only [div_pow, ← Finset.sum_div]
      rw [show gradNorm f y ^ 2 = ∑ j, D f j y ^ 2 from Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
      exact div_self (by rw [← Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (D f j y)))]; exact pow_ne_zero 2 h)
    rw [mul_comm (71 / 50 : ℝ)]
    exact mul_le_mul_of_nonneg_left (hK n _ hunit) hpos.le

end Poincare11a
