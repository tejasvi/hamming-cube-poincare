/-
Lemma B2: the Fourier series of `f_c` on `[0,1]` is `∑_k κ_c(k) e^{2πikq}`, with `κ_c(k) = (2 - 2 cos c)/(c - 2πk)²`.
-/
import Poincare11b.Statements
import Poincare11b.Kappa

namespace Poincare11b

open Complex Real MeasureTheory

lemma continuous_fc (c : ℝ) : Continuous (fun x : ℝ => fc c x) := by
  unfold fc; fun_prop

lemma fc_zero (c : ℝ) : fc c 0 = 1 := by simp [fc]

lemma fc_one (c : ℝ) : fc c 1 = 1 := by simp [fc]

/-- `∫_0^1 e^{-2πikx} f_c(x) dx = κ_c(k)`. -/
lemma integral_fc_coeff (c : ℝ) (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * k * x : ℝ) * I) * fc c x = (kap c k : ℂ) := by
  set μ : ℝ := c - 2 * Real.pi * k with hμ
  set E : ℂ := Complex.exp (-(c : ℂ) * I) with hE
  have hint : ∀ x : ℝ, Complex.exp (-(2 * Real.pi * k * x : ℝ) * I) * fc c x =
      Complex.exp ((μ : ℂ) * x * I) * ((1 - (x : ℂ)) + (x : ℂ) * E) := by
    intro x
    unfold fc
    rw [hE, hμ]
    have e1 : Complex.exp (-(2 * Real.pi * k * x : ℝ) * I) * Complex.exp ((c : ℂ) * x * I) =
        Complex.exp (((c - 2 * Real.pi * k : ℝ) : ℂ) * x * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp (-(2 * Real.pi * k * x : ℝ) * I) * Complex.exp (-((c : ℂ) * (1 - x)) * I) =
        Complex.exp (((c - 2 * Real.pi * k : ℝ) : ℂ) * x * I) * Complex.exp (-(c : ℂ) * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination (1 - (x : ℂ)) * e1 + (x : ℂ) * e2
  simp_rw [hint]
  have hEk : Complex.exp ((μ : ℂ) * I) * E = 1 := by
    rw [hE, ← Complex.exp_add, hμ]
    have : ((c - 2 * Real.pi * k : ℝ) : ℂ) * I + -(c : ℂ) * I = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  by_cases h0 : c = 2 * Real.pi * k
  · -- μ = 0, E = 1
    have hμ0 : μ = 0 := by rw [hμ, h0]; ring
    have hE1 : E = 1 := by
      have := hEk; rw [hμ0] at this; simpa using this
    have : ∀ x : ℝ, Complex.exp ((μ : ℂ) * x * I) * ((1 - (x : ℂ)) + (x : ℂ) * E) = 1 := by
      intro x; rw [hμ0, hE1]; simp
    simp_rw [this]
    simp [kap, h0]
  · have hμne : μ ≠ 0 := by rw [hμ]; intro h; apply h0; linarith
    have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμne
    set A : ℂ := 1 / (I * μ) + (E - 1) / (μ : ℂ) ^ 2 with hA
    set B : ℂ := (E - 1) / (I * μ) with hB
    have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp ((μ : ℂ) * x * I) * (A + (x : ℂ) * B))
        (Complex.exp ((μ : ℂ) * x * I) * ((1 - (x : ℂ)) + (x : ℂ) * E)) x := by
      intro x
      have h1 : HasDerivAt (fun x : ℝ => (μ : ℂ) * x * I) ((μ : ℂ) * I) x := by
        have := ((hasDerivAt_id x).ofReal_comp).const_mul (μ : ℂ)
        have := this.mul_const I
        simpa using this
      have h2 := h1.cexp
      have h3 : HasDerivAt (fun x : ℝ => A + (x : ℂ) * B) B x := by
        have := (((hasDerivAt_id x).ofReal_comp).mul_const B).const_add A
        simpa using this
      convert h2.mul h3 using 1
      rw [hA, hB]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_mul, Complex.exp_zero,
      one_mul, add_zero]
    unfold kap
    rw [ite_eq_right h0]
    have hexp : Complex.exp ((μ : ℂ) * I) = Complex.exp ((c : ℂ) * I) := by
      have h1 : Complex.exp ((μ : ℂ) * I) = 1 / E := by
        rw [eq_div_iff (by rw [hE]; exact Complex.exp_ne_zero _)]; exact hEk
      rw [h1, hE, one_div, ← Complex.exp_neg]; congr 1; ring
    push_cast
    rw [hexp]
    have hden : ((c : ℂ) - 2 * (Real.pi : ℂ) * (k : ℂ)) = (μ : ℂ) := by rw [hμ]; push_cast; ring
    rw [hden]
    have hcos : (2 - 2 * Complex.cos (c : ℂ)) = 2 - Complex.exp ((c : ℂ) * I) - E := by
      rw [Complex.cos, hE]; ring
    rw [hcos]
    have hEc : Complex.exp ((c : ℂ) * I) * E = 1 := by rw [← hexp]; exact hEk
    have key : Complex.exp ((c : ℂ) * I) * (A + B) - A - (2 - Complex.exp ((c : ℂ) * I) - E) / (μ : ℂ) ^ 2
        = (Complex.exp ((c : ℂ) * I) * E - 1) * (1 / (I * μ) + 1 / (μ : ℂ) ^ 2) := by
      rw [hA, hB]; ring
    rw [hEc, sub_self, zero_mul] at key
    linear_combination key

lemma ex_coe_fourier (k : ℤ) (q : ℝ) [Fact ((0 : ℝ) < 1)] :
    fourier k (q : AddCircle (1 : ℝ)) = ex k q := by
  rw [fourier_coe_apply, ex]; congr 1; push_cast; ring

/-- Lemma B2: `f_c(q) = ∑_k κ_c(k) e^{2πikq}` for `q ∈ [0,1]` (absolutely convergent). -/
theorem fc_hasSum (c : ℝ) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun k : ℤ => (kap c k : ℂ) * ex k q) (fc c q) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hper : fc c 0 = fc c (0 + 1) := by rw [zero_add, fc_zero, fc_one]
  let F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIco 1 0 (fc c), AddCircle.liftIco_continuous hper (continuous_fc c).continuousOn⟩
  have hF : ∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) 1 → F (x : AddCircle (1 : ℝ)) = fc c x := by
    intro x hx
    show AddCircle.liftIco 1 0 (fc c) (x : AddCircle (1 : ℝ)) = fc c x
    exact AddCircle.liftIco_coe_apply (by rwa [zero_add])
  have hcoef : ∀ k : ℤ, fourierCoeff F k = (kap c k : ℂ) := by
    intro k
    rw [fourierCoeff_eq_intervalIntegral F k 0, zero_add, div_one, one_smul, ← integral_fc_coeff c k]
    refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one (fun x hx => ?_)
    simp only [smul_eq_mul]
    rw [hF x ⟨hx.1.le, hx.2⟩, ex_coe_fourier, ex, show (-k : ℤ) = -k from rfl]
    congr 1; congr 1; push_cast; ring
  have hsum : Summable (fourierCoeff F) := by
    have : (fourierCoeff F) = fun k => (kap c k : ℂ) := funext hcoef
    rw [this]
    exact Complex.summable_ofReal.mpr (kap_summable c)
  have key : ∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) 1 → HasSum (fun k : ℤ => (kap c k : ℂ) * ex k x) (fc c x) := by
    intro x hx
    have h := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (1 : ℝ))
    rw [hF x hx] at h
    refine h.congr_fun (fun k => ?_)
    rw [hcoef k, ex_coe_fourier, smul_eq_mul]
  rcases eq_or_lt_of_le hq.2 with h1 | h1
  · subst h1
    have h0 := key 0 ⟨le_rfl, zero_lt_one⟩
    rw [fc_zero] at h0
    rw [fc_one]
    refine h0.congr_fun (fun k => ?_)
    congr 1
    unfold ex
    have : ((2 * Real.pi * k * 1 : ℝ) : ℂ) * I = (k : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]; simp
  · exact key q ⟨hq.1, h1⟩

lemma fc_eq_fser (c : ℝ) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) : fc c q = fser (kap c) q :=
  (fc_hasSum c hq).tsum_eq.symm

end Poincare11b
