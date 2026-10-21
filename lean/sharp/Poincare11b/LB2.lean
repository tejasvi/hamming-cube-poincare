/-
Lower bound, part 2: the transfer from the cube to the Gaussian. If `C` is a valid constant, then
`E|g(Z) - E g(Z)| ≤ C E|g'(Z)|` for every bounded continuous `g` with a bounded, continuous, Lipschitz derivative
(test functions `f_n(x) = g(t_n(x))`, the uniform estimate `|∇f_n| = |g'(t_n)| + O(n^{-1/2})`, and the central limit
theorem of `LB1.lean`).
-/
import Poincare11b.LB1

namespace Poincare11b

open Poincare11a MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BoundedContinuousFunction

variable {n : ℕ}

lemma xb_not (b : Bool) : xb (!b) = -xb b := by cases b <;> simp [xb]

lemma xb_sq (b : Bool) : xb b ^ 2 = 1 := by cases b <;> simp [xb]

lemma tn_flip (x : Cube n) (j : Fin n) :
    tn n (Poincare11a.flip j x) = tn n x - (Real.sqrt n)⁻¹ * (2 * xb (x j)) := by
  unfold tn Poincare11a.flip
  have h : ∀ i, xb (Function.update x j (!x j) i) = xb (x i) + (if i = j then -2 * xb (x j) else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij; rw [Function.update_self, xb_not]; simp only [ite_true]; ring
    · rw [Function.update_of_ne hij]; simp [hij]
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Taylor bound with a Lipschitz derivative: `|g t - g (t - h) - h g'(t)| ≤ L h²`. -/
lemma taylor_lip {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, |g' x - g' y| ≤ L * |x - y|) (t h : ℝ) :
    |g t - g (t - h) - h * g' t| ≤ L * h ^ 2 := by
  have hφ : ∀ s ∈ uIcc (t - h) t, HasDerivWithinAt (fun s => g s - s * g' t) (g' s - g' t) (uIcc (t - h) t) s := by
    intro s _
    have := (hd s).fun_sub ((hasDerivAt_id' s).mul_const (g' t))
    convert this.hasDerivWithinAt using 1
    ring
  have hb : ∀ s ∈ uIcc (t - h) t, ‖g' s - g' t‖ ≤ L * |h| := by
    intro s hs
    rw [Real.norm_eq_abs]
    refine (hL s t).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    have := abs_sub_right_of_mem_uIcc hs
    rw [abs_sub_comm] at this
    simpa using this
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hb (convex_uIcc _ _) left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs, sub_sub_cancel] at this
  calc |g t - g (t - h) - h * g' t| = |g t - t * g' t - (g (t - h) - (t - h) * g' t)| := by ring_nf
    _ ≤ L * |h| * |h| := this
    _ = L * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- Reverse triangle inequality for the Euclidean norm. -/
lemma abs_sqrt_sum_sub_le (a b : Fin n → ℝ) :
    |Real.sqrt (∑ j, a j ^ 2) - Real.sqrt (∑ j, b j ^ 2)| ≤ Real.sqrt (∑ j, (a j - b j) ^ 2) := by
  have h := abs_norm_sub_norm_le (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 b)
  rw [← WithLp.toLp_sub] at h
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Pi.sub_apply] at h
  exact h

/-- The uniform gradient estimate `|∇f_n| = |g'(t_n)| + O(n^{-1/2})` for `f_n = g ∘ t_n`. -/
lemma gradNorm_approx {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, |g' x - g' y| ≤ L * |x - y|) (hn : 0 < n) (x : Cube n) :
    abs (gradNorm (fun y => g (tn n y)) x - abs (g' (tn n x))) ≤ 2 * L / Real.sqrt n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  set t := tn n x with ht
  set u : Fin n → ℝ := fun j => (Real.sqrt n)⁻¹ * xb (x j) * g' t with hu
  have hu2 : Real.sqrt (∑ j, u j ^ 2) = |g' t| := by
    have : ∑ j, u j ^ 2 = g' t ^ 2 := by
      have e : ∀ j, u j ^ 2 = g' t ^ 2 / n := by
        intro j
        simp only [hu, mul_pow, inv_pow, xb_sq, hsq]
        field_simp
      simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [this, Real.sqrt_sq_eq_abs]
  have hD : ∀ j, |D (fun y => g (tn n y)) j x - u j| ≤ 2 * L / n := by
    intro j
    show |(g (tn n x) - g (tn n (Poincare11a.flip j x))) / 2 - u j| ≤ _
    rw [tn_flip, ← ht]
    set h := (Real.sqrt n)⁻¹ * (2 * xb (x j)) with hh
    have hT := taylor_lip hd hL0 hL t h
    have hh2 : h ^ 2 = 4 / n := by
      simp only [hh, mul_pow, inv_pow, hsq, xb_sq]; ring
    have e : (g t - g (t - h)) / 2 - u j = (g t - g (t - h) - h * g' t) / 2 := by
      simp only [hu, hh]; ring
    rw [e, abs_div, abs_two]
    rw [hh2] at hT
    have : L * (4 / n) / 2 = 2 * L / n := by ring
    linarith [div_le_div_of_nonneg_right hT (by norm_num : (0 : ℝ) ≤ 2)]
  unfold gradNorm
  rw [← hu2]
  refine (abs_sqrt_sum_sub_le _ _).trans ?_
  have hsum : ∑ j, (D (fun y => g (tn n y)) j x - u j) ^ 2 ≤ n * (2 * L / n) ^ 2 := by
    calc _ ≤ ∑ _j : Fin n, (2 * L / n) ^ 2 := Finset.sum_le_sum (fun j _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hD j) 2)
      _ = n * (2 * L / n) ^ 2 := by simp
  calc Real.sqrt (∑ j, (D (fun y => g (tn n y)) j x - u j) ^ 2) ≤ Real.sqrt (n * (2 * L / n) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = 2 * L / Real.sqrt n := by
        rw [Real.sqrt_mul hn'.le, Real.sqrt_sq (by positivity)]
        field_simp
        rw [hsq]
        ring

lemma abs_avg_sub_le {F G : Cube n → ℝ} {ε : ℝ} (h : ∀ x, |F x - G x| ≤ ε) : |avg F - avg G| ≤ ε := by
  unfold avg
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  rw [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp, ← Finset.sum_sub_distrib]
  calc |∑ x, (F x - G x)| ≤ ∑ x, |F x - G x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Cube n, ε := Finset.sum_le_sum (fun x _ => h x)
    _ = ε * 2 ^ n := by simp [mul_comm]

/-- Transfer: a valid constant `C` gives `E|g(Z) - E g(Z)| ≤ C E|g'(Z)|`. -/
theorem transfer {C : ℝ}
    (hC : ∀ (m : ℕ) (f : Cube m → ℝ), avg (fun x => |f x - avg f|) ≤ C * avg (gradNorm f))
    (g g' : ℝ →ᵇ ℝ) (hd : ∀ x, HasDerivAt g (g' x) x) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, |g' x - g' y| ≤ L * |x - y|) :
    ∫ s, |g s - ∫ r, g r ∂(gaussianReal 0 1)| ∂(gaussianReal 0 1) ≤ C * ∫ s, |g' s| ∂(gaussianReal 0 1) := by
  set c := ∫ r, g r ∂(gaussianReal 0 1) with hc
  -- the bounded continuous test functions
  let F1 : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun s => |g s - c|)
    ((g.continuous.sub continuous_const).abs) (‖g‖ + |c|) (fun s => by
      rw [Real.norm_eq_abs, abs_abs]
      have h1 := g.norm_coe_le_norm s
      rw [Real.norm_eq_abs] at h1
      have h2 := abs_add_le (g s) (-c)
      rw [abs_neg, ← sub_eq_add_neg] at h2
      linarith)
  let F2 : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun s => |g' s|)
    g'.continuous.abs ‖g'‖ (fun s => by rw [Real.norm_eq_abs, abs_abs]; exact g'.norm_coe_le_norm s)
  have ha := tendsto_avg_tn g
  have h1 := tendsto_avg_tn F1
  have h2 := tendsto_avg_tn F2
  -- b_n → E|g - c|
  have hb : Tendsto (fun n => avg (fun x => |g (tn n x) - avg (fun y => g (tn n y))|)) atTop
      (𝓝 (∫ s, |g s - c| ∂(gaussianReal 0 1))) := by
    have hdiff : Tendsto (fun n => avg (fun x => |g (tn n x) - avg (fun y => g (tn n y))|) -
        avg (fun x => F1 (tn n x))) atTop (𝓝 0) := by
      have hz : Tendsto (fun n => ‖avg (fun x => g (tn n x)) - c‖) atTop (𝓝 0) := by
        simpa using (tendsto_sub_nhds_zero_iff.mpr ha).norm
      refine squeeze_zero_norm (fun n => ?_) hz
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      refine abs_avg_sub_le (fun x => ?_)
      show abs (abs (g (tn n x) - avg (fun y => g (tn n y))) - abs (g (tn n x) - c)) ≤ _
      refine (abs_abs_sub_abs_le_abs_sub _ _).trans (le_of_eq ?_)
      rw [show g (tn n x) - avg (fun y => g (tn n y)) - (g (tn n x) - c) =
        -(avg (fun y => g (tn n y)) - c) by ring, abs_neg]
    have := hdiff.add h1
    simp only [sub_add_cancel, zero_add] at this
    simpa [F1, BoundedContinuousFunction.coe_ofNormedAddCommGroup] using this
  -- d_n → E|g'|
  have hd' : Tendsto (fun n => avg (gradNorm (fun y => g (tn n y)))) atTop
      (𝓝 (∫ s, |g' s| ∂(gaussianReal 0 1))) := by
    have hdiff : Tendsto (fun n => avg (gradNorm (fun y => g (tn n y))) - avg (fun x => F2 (tn n x)))
        atTop (𝓝 0) := by
      have hlim : Tendsto (fun n : ℕ => 2 * L / Real.sqrt n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [Real.norm_eq_abs]
      exact abs_avg_sub_le (fun x => gradNorm_approx hd hL0 hL hn x)
    have := hdiff.add h2
    simp only [sub_add_cancel, zero_add] at this
    simpa [F2, BoundedContinuousFunction.coe_ofNormedAddCommGroup] using this
  exact le_of_tendsto_of_tendsto' hb (hd'.const_mul C) (fun n => hC n _)

end Poincare11b
