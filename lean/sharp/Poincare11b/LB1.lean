/-
Lower bound, part 1: the central limit theorem for normalized Rademacher sums on the cube,
`avg (F ∘ t_n) → ∫ F d(gaussianReal 0 1)` for bounded continuous `F`, via Lévy's continuity theorem.
-/
import Poincare11b.TheoremB
import Mathlib.Probability.CentralLimitTheorem

namespace Poincare11b

open Poincare11a MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal BoundedContinuousFunction

/-- The `±1` value of a cube coordinate. -/
def xb (b : Bool) : ℝ := if b then 1 else -1

/-- `t_n(x) = n^{-1/2} ∑_j x_j`. -/
noncomputable def tn (n : ℕ) (x : Cube n) : ℝ := (Real.sqrt n)⁻¹ * ∑ j, xb (x j)

/-- The law of `t_n` under the uniform measure on the cube. -/
noncomputable def muN (n : ℕ) : Measure ℝ :=
  ∑ x : Cube n, ((2 : ℝ≥0∞) ^ n)⁻¹ • Measure.dirac (tn n x)

lemma card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by simp

instance muN_isProb (n : ℕ) : IsProbabilityMeasure (muN n) := by
  constructor
  simp only [muN, Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, card_cube, nsmul_eq_mul]
  push_cast
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

lemma integral_muN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (n : ℕ)
    (F : ℝ → E) : ∫ s, F s ∂(muN n) = ((2 : ℝ) ^ n)⁻¹ • ∑ x : Cube n, F (tn n x) := by
  unfold muN
  rw [integral_finsetSum_measure (fun x _ => (integrable_dirac (by simp)).smul_measure (by simp))]
  simp only [integral_smul_measure, integral_dirac]
  rw [Finset.smul_sum]
  congr 1; funext x
  congr 1
  simp

lemma integral_muN_real (n : ℕ) (F : ℝ → ℝ) : ∫ s, F s ∂(muN n) = avg (fun x => F (tn n x)) := by
  rw [integral_muN, avg, smul_eq_mul, div_eq_inv_mul]

/-- A uniform random sign as a probability space. -/
noncomputable def muB : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance muB_isProb : IsProbabilityMeasure muB := by
  constructor
  simp only [muB, Measure.coe_smul, Measure.coe_add, Pi.smul_apply, Pi.add_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul]
  rw [← two_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma integral_muB {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (F : Bool → E) :
    ∫ b, F b ∂muB = (2⁻¹ : ℝ) • (F true + F false) := by
  unfold muB
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]
  congr 1
  simp

lemma measurable_xb : Measurable xb := measurable_of_finite _

lemma charFun_muB_xb (s : ℝ) :
    charFun (muB.map xb) s = (2⁻¹ : ℂ) * (Complex.exp (s * I) + Complex.exp (-(s * I))) := by
  rw [charFun_apply_real, integral_map measurable_xb.aemeasurable (by fun_prop), integral_muB]
  simp only [xb, ite_true, Bool.false_eq_true, ite_false]
  push_cast
  rw [Complex.real_smul]
  congr 1
  · push_cast; ring_nf
  · ring_nf

lemma charFun_muN (n : ℕ) (t : ℝ) :
    charFun (muN n) t = (charFun (muB.map xb) ((Real.sqrt n)⁻¹ * t)) ^ n := by
  rw [charFun_apply_real, integral_muN, charFun_muB_xb]
  have h : ∀ x : Cube n, Complex.exp (t * tn n x * I) =
      ∏ j, Complex.exp (((Real.sqrt n)⁻¹ * t : ℝ) * xb (x j) * I) := by
    intro x
    rw [← Complex.exp_sum]
    congr 1
    unfold tn
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [h]
  rw [sum_cube_prod (fun _ b => Complex.exp (((Real.sqrt n)⁻¹ * t : ℝ) * xb b * I))]
  simp only [xb, ite_true, Bool.false_eq_true, ite_false, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [Complex.real_smul, mul_pow]
  push_cast
  congr 1
  · rw [inv_pow]
  · congr 1; ring_nf

lemma muB_mean : muB[xb] = 0 := by
  rw [integral_muB]; simp [xb]

lemma muB_sq : muB[xb ^ 2] = 1 := by
  rw [integral_muB]; simp [xb]; norm_num

/-- The central limit theorem for `t_n`: `muN n → N(0,1)` weakly. -/
theorem tendsto_muN :
    Tendsto (β := ProbabilityMeasure ℝ) (fun n => ⟨muN n, inferInstance⟩) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 (fun t => ?_)
  simp only [ProbabilityMeasure.coe_mk]
  rw [charFun_gaussianReal]
  have := tendsto_charFun_inv_sqrt_mul_pow (P := muB) (X := xb) measurable_xb.aemeasurable muB_mean muB_sq t
  convert this using 1
  · funext n; exact charFun_muN n t
  · congr 1; push_cast; ring_nf

/-- `avg (F ∘ t_n) → E F(Z)` for bounded continuous `F`. -/
theorem tendsto_avg_tn (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n => avg (fun x => F (tn n x))) atTop (𝓝 (∫ s, F s ∂(gaussianReal 0 1))) := by
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_muN) F
  simp only [ProbabilityMeasure.coe_mk, integral_muN_real] at this
  exact this

end Poincare11b
