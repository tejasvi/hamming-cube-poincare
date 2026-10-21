/-
Elementary facts about `f_c` and `F_θ`: conjugation, the bounds `|f_c| ≤ 1`, `|f_c - 1| ≤ 2|c| q(1-q)`,
the telescoping bound for products, continuity, and an integrability helper on `(0,1)`.
-/
import Poincare11b.Statements
import Mathlib

namespace Poincare11b

open Complex Real MeasureTheory Set

variable {n : ℕ}

lemma fc_neg (c q : ℝ) : fc (-c) q = (starRingEnd ℂ) (fc c q) := by
  unfold fc
  simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal, ← Complex.exp_conj, map_neg,
    Complex.conj_I]
  push_cast
  ring_nf

lemma fc_zero_c (q : ℝ) : fc 0 q = 1 := by
  unfold fc; simp

lemma norm_fc_le {c q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : ‖fc c q‖ ≤ 1 := by
  have h1 : ‖((1 - q : ℝ) : ℂ) * Complex.exp ((c * q : ℝ) * I)‖ = 1 - q := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith [hq.2])]
  have h2 : ‖((q : ℝ) : ℂ) * Complex.exp ((-(c * (1 - q)) : ℝ) * I)‖ = q := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hq.1]
  have e : fc c q = ((1 - q : ℝ) : ℂ) * Complex.exp ((c * q : ℝ) * I) +
      ((q : ℝ) : ℂ) * Complex.exp ((-(c * (1 - q)) : ℝ) * I) := by
    unfold fc; push_cast; ring_nf
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [h1, h2]; linarith

lemma norm_cexp_sub_one_le (x : ℝ) : ‖Complex.exp ((x : ℂ) * I) - 1‖ ≤ |x| := by
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)
  rw [mul_comm] at this
  simpa [Real.norm_eq_abs] using this

lemma norm_fc_sub_one_le {c q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ‖fc c q - 1‖ ≤ 2 * |c| * (q * (1 - q)) := by
  have hq1 : 0 ≤ 1 - q := by linarith [hq.2]
  have e : fc c q - 1 = ((1 - q : ℝ) : ℂ) * (Complex.exp ((c * q : ℝ) * I) - 1) +
      ((q : ℝ) : ℂ) * (Complex.exp ((-(c * (1 - q)) : ℝ) * I) - 1) := by
    unfold fc; push_cast; ring
  rw [e]
  calc _ ≤ ‖((1 - q : ℝ) : ℂ) * (Complex.exp ((c * q : ℝ) * I) - 1)‖ +
        ‖((q : ℝ) : ℂ) * (Complex.exp ((-(c * (1 - q)) : ℝ) * I) - 1)‖ := norm_add_le _ _
    _ ≤ (1 - q) * |c * q| + q * |-(c * (1 - q))| := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hq1,
          Real.norm_of_nonneg hq.1]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_cexp_sub_one_le _) hq1)
          (mul_le_mul_of_nonneg_left (norm_cexp_sub_one_le _) hq.1)
    _ = 2 * |c| * (q * (1 - q)) := by
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hq.1, abs_of_nonneg hq1]; ring

/-- Telescoping bound: `‖∏ a_j - 1‖ ≤ ∑ ‖a_j - 1‖` when all `‖a_j‖ ≤ 1`. -/
lemma norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) :
    ‖(∏ i ∈ s, a i) - 1‖ ≤ ∑ i ∈ s, ‖a i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have ih' := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    have hai := ha i (Finset.mem_insert_self i s)
    have e : a i * ∏ j ∈ s, a j - 1 = a i * ((∏ j ∈ s, a j) - 1) + (a i - 1) := by ring
    rw [e]
    calc _ ≤ ‖a i * ((∏ j ∈ s, a j) - 1)‖ + ‖a i - 1‖ := norm_add_le _ _
      _ ≤ 1 * ‖(∏ j ∈ s, a j) - 1‖ + ‖a i - 1‖ := by
          rw [norm_mul]; gcongr
      _ ≤ ‖a i - 1‖ + ∑ j ∈ s, ‖a j - 1‖ := by linarith

lemma norm_prod_le_one {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) :
    ‖∏ i ∈ s, a i‖ ≤ 1 := by
  rw [norm_prod]; exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) ha

lemma norm_Fth_le (θ : Fin n → ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : ‖Fth θ q‖ ≤ 1 :=
  norm_prod_le_one _ _ (fun _ _ => norm_fc_le hq)

lemma norm_Fth_sub_one_le (θ : Fin n → ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ‖Fth θ q - 1‖ ≤ 2 * (∑ j, |θ j|) * (q * (1 - q)) := by
  calc ‖Fth θ q - 1‖ ≤ ∑ j, ‖fc (θ j) q - 1‖ := norm_prod_sub_one_le _ _ (fun _ _ => norm_fc_le hq)
    _ ≤ ∑ j, 2 * |θ j| * (q * (1 - q)) := Finset.sum_le_sum (fun j _ => norm_fc_sub_one_le hq)
    _ = 2 * (∑ j, |θ j|) * (q * (1 - q)) := by rw [Finset.mul_sum, Finset.sum_mul]

lemma continuous_fc' (c : ℝ) : Continuous (fun x : ℝ => fc c x) := by
  unfold fc; fun_prop

lemma continuous_Fth (θ : Fin n → ℝ) : Continuous (Fth θ) := by
  unfold Fth
  exact continuous_finsetProd _ (fun j _ => continuous_fc' (θ j))

lemma Fth_zero (θ : Fin n → ℝ) : Fth θ 0 = 1 := by
  unfold Fth fc; simp

lemma Fth_one (θ : Fin n → ℝ) : Fth θ 1 = 1 := by
  unfold Fth fc; simp

/-- A measurable function bounded on `(0,1)` is integrable there. -/
lemma integrableOn_Ioo01 {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ q ∈ Ioo (0 : ℝ) 1, |f q| ≤ C) :
    IntegrableOn f (Ioo (0 : ℝ) 1) :=
  Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq => by rw [Real.norm_eq_abs]; exact hC q hq))

/-- `|sin(2πmq)| / (q(1-q)) ≤ 4π|m|` on `(0,1)`. -/
lemma abs_sin_div_le {m : ℝ} (hm : ∃ k : ℤ, m = k) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    |Real.sin (2 * Real.pi * m * q)| / (q * (1 - q)) ≤ 4 * Real.pi * |m| := by
  obtain ⟨k, rfl⟩ := hm
  have hq0 := hq.1
  have hq1 : 0 < 1 - q := by linarith [hq.2]
  have hs : 0 < q * (1 - q) := mul_pos hq0 hq1
  rw [div_le_iff₀ hs]
  have h1 : |Real.sin (2 * Real.pi * k * q)| ≤ 2 * Real.pi * |(k : ℝ)| * q := by
    calc |Real.sin (2 * Real.pi * k * q)| ≤ |2 * Real.pi * k * q| := Real.abs_sin_le_abs
      _ = 2 * Real.pi * |(k : ℝ)| * q := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hq0]; norm_num
  have h2 : |Real.sin (2 * Real.pi * k * q)| ≤ 2 * Real.pi * |(k : ℝ)| * (1 - q) := by
    have : Real.sin (2 * Real.pi * k * q) = -Real.sin (2 * Real.pi * k * (1 - q)) := by
      have e : 2 * Real.pi * k * q = (k : ℝ) * (2 * Real.pi) - 2 * Real.pi * k * (1 - q) := by ring
      rw [e, Real.sin_int_mul_two_pi_sub]
    rw [this, abs_neg]
    calc |Real.sin (2 * Real.pi * k * (1 - q))| ≤ |2 * Real.pi * k * (1 - q)| := Real.abs_sin_le_abs
      _ = 2 * Real.pi * |(k : ℝ)| * (1 - q) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hq1]; norm_num
  have hk : 0 ≤ 2 * Real.pi * |(k : ℝ)| := by positivity
  rcases le_total q (1 / 2) with hh | hh
  · nlinarith
  · nlinarith

end Poincare11b
