/-
The substitution `q = (1 + sin θ)/2` between `θ ∈ (-π/2, π/2)` and `q ∈ (0, 1)` (M4 of the sharp L¹ Poincaré
inequality on the Hamming cube): change of variables for Lebesgue integrals, `q(1-q) = cos²θ/4`,
`∫_0^1 dq/√(q(1-q)) = π`, and the reflection `θ ↦ -θ`.
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Poincare11b.M4

open MeasureTheory Set
open scoped ENNReal

/-- The substitution `q = (1 + sin θ)/2`. -/
noncomputable def qOf (θ : ℝ) : ℝ := (1 + Real.sin θ) / 2

/-- The open interval `(-π/2, π/2)`. -/
abbrev halfPi : Set ℝ := Ioo (-(Real.pi / 2)) (Real.pi / 2)

lemma sin_mem_Ioo {θ : ℝ} (hθ : θ ∈ halfPi) : -1 < Real.sin θ ∧ Real.sin θ < 1 := by
  have hI : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := Ioo_subset_Icc_self hθ
  have hl : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hr : Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  constructor
  · have := Real.strictMonoOn_sin hl hI hθ.1
    rwa [Real.sin_neg, Real.sin_pi_div_two] at this
  · have := Real.strictMonoOn_sin hI hr hθ.2
    rwa [Real.sin_pi_div_two] at this

lemma cos_pos_of_mem {θ : ℝ} (hθ : θ ∈ halfPi) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo hθ

lemma qOf_mem {θ : ℝ} (hθ : θ ∈ halfPi) : qOf θ ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := sin_mem_Ioo hθ
  constructor <;> simp only [qOf] <;> linarith

lemma qOf_image : qOf '' halfPi = Ioo (0 : ℝ) 1 := by
  ext q
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact qOf_mem hθ
  · rintro ⟨hq0, hq1⟩
    refine ⟨Real.arcsin (2 * q - 1), ⟨Real.neg_pi_div_two_lt_arcsin.2 (by linarith),
      Real.arcsin_lt_pi_div_two.2 (by linarith)⟩, ?_⟩
    simp only [qOf]
    rw [Real.sin_arcsin (by linarith) (by linarith)]
    ring

lemma qOf_injOn : InjOn qOf halfPi := by
  intro a ha b hb h
  simp only [qOf] at h
  exact Real.injOn_sin (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) (by linarith)

lemma hasDerivAt_qOf (θ : ℝ) : HasDerivAt qOf (Real.cos θ / 2) θ :=
  ((Real.hasDerivAt_sin θ).const_add 1).div_const 2

lemma qOf_mul_one_sub (θ : ℝ) : qOf θ * (1 - qOf θ) = Real.cos θ ^ 2 / 4 := by
  simp only [qOf]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination (-1 / 4 : ℝ) * this

lemma qOf_neg (θ : ℝ) : qOf (-θ) = 1 - qOf θ := by
  simp only [qOf, Real.sin_neg]
  ring

/-- **Change of variables** `q = (1 + sin θ)/2` for Lebesgue integrals over `(0, 1)`. -/
theorem lintegral_Ioo01 (g : ℝ → ℝ≥0∞) :
    ∫⁻ q in Ioo (0 : ℝ) 1, g q =
      ∫⁻ θ in halfPi, ENNReal.ofReal (Real.cos θ / 2) * g (qOf θ) := by
  rw [← qOf_image, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun θ _ => (hasDerivAt_qOf θ).hasDerivWithinAt) qOf_injOn g]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  rw [abs_of_pos (by linarith [cos_pos_of_mem hθ])]

/-- `∫_0^1 dq/√(q(1-q)) = π`. -/
theorem lintegral_inv_sqrt :
    ∫⁻ q in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / Real.sqrt (q * (1 - q))) = ENNReal.ofReal Real.pi := by
  rw [lintegral_Ioo01]
  have h : ∀ θ ∈ halfPi, ENNReal.ofReal (Real.cos θ / 2) *
      ENNReal.ofReal (1 / Real.sqrt (qOf θ * (1 - qOf θ))) = 1 := by
    intro θ hθ
    have hc := cos_pos_of_mem hθ
    rw [qOf_mul_one_sub, ← ENNReal.ofReal_mul (by linarith), Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      Real.sqrt_sq hc.le, show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [← ENNReal.ofReal_one]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioo h, setLIntegral_const, one_mul]
  show volume (Ioo (-(Real.pi / 2)) (Real.pi / 2)) = _
  rw [Real.volume_Ioo]
  congr 1
  ring

/-- **Reflection.** For `h` even, `∫_{-π/2}^{π/2} h = 2 ∫_0^{π/2} h`. -/
theorem lintegral_halfPi_of_even (h : ℝ → ℝ≥0∞) (hh : ∀ θ, h (-θ) = h θ) :
    ∫⁻ θ in halfPi, h θ = 2 * ∫⁻ θ in Ioo (0 : ℝ) (Real.pi / 2), h θ := by
  have hsplit : halfPi = Ioo (-(Real.pi / 2)) 0 ∪ Ico 0 (Real.pi / 2) :=
    (Ioo_union_Ico_eq_Ioo (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).symm
  have hneg : Ioo (-(Real.pi / 2)) 0 = (fun θ : ℝ => -θ) '' Ioo 0 (Real.pi / 2) := by
    rw [Set.image_neg_Ioo, neg_zero]
  have hdisj : Disjoint (Ioo (-(Real.pi / 2)) 0) (Ico 0 (Real.pi / 2)) :=
    Set.disjoint_left.2 (fun x hx hx' => by linarith [hx.2, hx'.1])
  rw [hsplit, lintegral_union measurableSet_Ico hdisj, hneg,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun θ _ => (hasDerivAt_neg θ).hasDerivWithinAt) neg_injective.injOn h,
    setLIntegral_congr Ioo_ae_eq_Ico.symm]
  simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul, hh]
  ring

end Poincare11b.M4
