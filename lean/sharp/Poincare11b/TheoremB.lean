/-
Theorem B at every frequency (HB): `C_v(λ) ≤ C_v(|λ|)`.
Lemma B1's algebra (`E e^{ivS^λ} = conj(A) B`, `E e^{ivS^{|λ|}} = conj(A) conj(B)`), the kernel
`W(k,l) = ∫_0^1 sin(2πkq) sin(2πlq) dq/(q(1-q)) ≥ 0` (Lemma B4), and the sine series of HSSL.
-/
import Poincare11b.SSL
import Poincare11b.FcBounds

namespace Poincare11b

open Poincare11a Complex Real MeasureTheory Set Filter

variable {n : ℕ}

/-! ### The expectation as a product -/

lemma sum_cube_prod (g : Fin n → Bool → ℂ) :
    ∑ z : Cube n, ∏ j, g j (z j) = ∏ j, (g j true + g j false) := by
  rw [← Fintype.prod_sum]; simp

lemma xi_sum (q c : ℝ) :
    (xiProb q true : ℂ) * Complex.exp (((c * (eta true - q)) : ℝ) * I) +
      (xiProb q false : ℂ) * Complex.exp (((c * (eta false - q)) : ℝ) * I) =
    (starRingEnd ℂ) (fc c q) := by
  unfold fc
  simp only [xiProb, eta, ite_true, Bool.false_eq_true, ite_false, map_add, map_mul, map_sub, map_one,
    Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
  push_cast
  ring_nf

/-- `cosGap v q λ = 1 - Re ∏_j conj(f_{vλ_j}(q))`. -/
lemma cosGap_eq (v q : ℝ) (lam : Fin n → ℝ) :
    cosGap v q lam = 1 - (∏ j, (starRingEnd ℂ) (fc (v * lam j) q)).re := by
  have hP : ∑ z : Cube n, ∏ j, xiProb q (z j) = 1 := by
    have h := sum_cube_prod (n := n) (fun _ b => ((xiProb q b : ℝ) : ℂ))
    have h2 : ∀ j : Fin n, ((xiProb q true : ℝ) : ℂ) + ((xiProb q false : ℝ) : ℂ) = 1 := by
      intro j; simp only [xiProb]; push_cast; ring
    rw [Finset.prod_congr rfl (fun j _ => h2 j), Finset.prod_const_one] at h
    exact_mod_cast h
  have hE : (∑ z : Cube n, (∏ j, xiProb q (z j)) * Real.cos (v * ∑ j, lam j * (eta (z j) - q))) =
      (∏ j, (starRingEnd ℂ) (fc (v * lam j) q)).re := by
    have h := sum_cube_prod (n := n)
      (fun j b => ((xiProb q b : ℝ) : ℂ) * Complex.exp (((v * lam j * (eta b - q)) : ℝ) * I))
    simp only [xi_sum] at h
    rw [← h, Complex.re_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Complex.ofReal_prod]
    have : ∑ j, ((v * lam j * (eta (z j) - q) : ℝ) : ℂ) * I =
        ((v * ∑ j, lam j * (eta (z j) - q) : ℝ) : ℂ) * I := by
      rw [← Finset.sum_mul]; congr 1; push_cast; rw [Finset.mul_sum]; congr 1; funext j; ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hsplit : cosGap v q lam = ∑ z : Cube n, ∏ j, xiProb q (z j) -
      ∑ z : Cube n, (∏ j, xiProb q (z j)) * Real.cos (v * ∑ j, lam j * (eta (z j) - q)) := by
    unfold cosGap; rw [← Finset.sum_sub_distrib]; congr 1; funext z; ring
  rw [hsplit, hP, hE]

lemma abs_cosGap_le (v q : ℝ) (lam : Fin n → ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    |cosGap v q lam| ≤ 2 * (∑ j, |v * lam j|) * (q * (1 - q)) := by
  rw [cosGap_eq]
  have h1 : |1 - (∏ j, (starRingEnd ℂ) (fc (v * lam j) q)).re| ≤ ‖(∏ j, (starRingEnd ℂ) (fc (v * lam j) q)) - 1‖ := by
    rw [← norm_neg, neg_sub]
    calc |1 - (∏ j, (starRingEnd ℂ) (fc (v * lam j) q)).re|
        = |(1 - ∏ j, (starRingEnd ℂ) (fc (v * lam j) q)).re| := by simp
      _ ≤ ‖1 - ∏ j, (starRingEnd ℂ) (fc (v * lam j) q)‖ := Complex.abs_re_le_norm _
  refine h1.trans ?_
  rw [← map_prod, ← map_one (starRingEnd ℂ), ← map_sub, Complex.norm_conj]
  exact norm_Fth_sub_one_le (fun j => v * lam j) hq

lemma continuous_cosGap (v : ℝ) (lam : Fin n → ℝ) : Continuous (fun q => cosGap v q lam) := by
  have : (fun q => cosGap v q lam) = fun q => 1 - (∏ j, (starRingEnd ℂ) (fc (v * lam j) q)).re :=
    funext (fun q => cosGap_eq v q lam)
  rw [this]
  refine continuous_const.sub (Complex.continuous_re.comp ?_)
  exact continuous_finsetProd _ (fun j _ => Complex.continuous_conj.comp (continuous_fc' _))

lemma measurable_div_s {f : ℝ → ℝ} (hf : Continuous f) : Measurable (fun q => f q / (q * (1 - q))) :=
  hf.measurable.div (by fun_prop)

lemma integrableOn_cosGap (v : ℝ) (lam : Fin n → ℝ) :
    IntegrableOn (fun q => cosGap v q lam / (q * (1 - q))) (Ioo (0 : ℝ) 1) := by
  refine integrableOn_Ioo01 (measurable_div_s (continuous_cosGap v lam)) (2 * ∑ j, |v * lam j|) (fun q hq => ?_)
  have hs : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  exact abs_cosGap_le v q lam ⟨hq.1.le, hq.2.le⟩

/-! ### Positive and negative parts -/

lemma conj_fc_split (v q l : ℝ) :
    (starRingEnd ℂ) (fc (v * l) q) =
      (starRingEnd ℂ) (fc (v * max l 0) q) * fc (v * max (-l) 0) q := by
  rcases le_total 0 l with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -l ≤ 0), mul_zero, fc_zero_c, mul_one]
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -l), mul_zero, fc_zero_c, map_one, one_mul,
      show v * -l = -(v * l) by ring, fc_neg]

lemma conj_fc_split_abs (v q l : ℝ) :
    (starRingEnd ℂ) (fc (v * |l|) q) =
      (starRingEnd ℂ) (fc (v * max l 0) q) * (starRingEnd ℂ) (fc (v * max (-l) 0) q) := by
  rcases le_total 0 l with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : -l ≤ 0), mul_zero, fc_zero_c,
      map_one, mul_one]
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : 0 ≤ -l), mul_zero, fc_zero_c,
      map_one, one_mul]

/-- `cosGap v q |λ| - cosGap v q λ = 2 Im A Im B` with `A = F_{vλ⁺}`, `B = F_{vλ⁻}`. -/
lemma cosGap_abs_sub (v q : ℝ) (lam : Fin n → ℝ) :
    cosGap v q (fun j => |lam j|) - cosGap v q lam =
      2 * (Fth (fun j => v * max (lam j) 0) q).im * (Fth (fun j => v * max (-lam j) 0) q).im := by
  rw [cosGap_eq, cosGap_eq]
  have e1 : ∏ j, (starRingEnd ℂ) (fc (v * |lam j|) q) =
      (starRingEnd ℂ) (Fth (fun j => v * max (lam j) 0) q) *
        (starRingEnd ℂ) (Fth (fun j => v * max (-lam j) 0) q) := by
    rw [Finset.prod_congr rfl (fun j _ => conj_fc_split_abs v q (lam j)), Finset.prod_mul_distrib,
      ← map_prod, ← map_prod]
    rfl
  have e2 : ∏ j, (starRingEnd ℂ) (fc (v * lam j) q) =
      (starRingEnd ℂ) (Fth (fun j => v * max (lam j) 0) q) * Fth (fun j => v * max (-lam j) 0) q := by
    rw [Finset.prod_congr rfl (fun j _ => conj_fc_split v q (lam j)), Finset.prod_mul_distrib, ← map_prod]
    rfl
  rw [e1, e2]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-! ### The kernel W (Lemma B4) -/

/-- `Cin(X) = ∫_0^X (1 - cos u)/u du`. -/
noncomputable def Cin (X : ℝ) : ℝ := ∫ u in (0 : ℝ)..X, (1 - Real.cos u) / u

lemma abs_one_sub_cos_div_le (u : ℝ) : |(1 - Real.cos u) / u| ≤ |u| / 2 := by
  rcases eq_or_ne u 0 with h | h
  · subst h; simp
  have h1 : 0 ≤ 1 - Real.cos u := by linarith [Real.cos_le_one u]
  have h2 : 1 - Real.cos u ≤ u ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := u)]
  rw [abs_div, abs_of_nonneg h1, div_le_div_iff₀ (abs_pos.mpr h) (by norm_num)]
  have : u ^ 2 = |u| * |u| := by rw [← sq_abs]; ring
  nlinarith [abs_nonneg u]

lemma intervalIntegrable_cin (a b : ℝ) : IntervalIntegrable (fun u => (1 - Real.cos u) / u) volume a b := by
  have hm : Measurable (fun u : ℝ => (1 - Real.cos u) / u) := by fun_prop
  refine (intervalIntegrable_iff.mpr ?_)
  refine Measure.integrableOn_of_bounded (M := (|a| + |b|) / 2) (by simp) hm.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc (fun u hu => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_one_sub_cos_div_le u).trans ?_
  have : |u| ≤ |a| + |b| := by
    rcases hu with ⟨h1, h2⟩
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab] at h1; rw [max_eq_right hab] at h2
      rcases le_total 0 u with h0 | h0
      · rw [abs_of_nonneg h0]; linarith [le_abs_self b, abs_nonneg a]
      · rw [abs_of_nonpos h0]; linarith [neg_abs_le a, abs_nonneg b]
    · rw [min_eq_right hab] at h1; rw [max_eq_left hab] at h2
      rcases le_total 0 u with h0 | h0
      · rw [abs_of_nonneg h0]; linarith [le_abs_self a, abs_nonneg b]
      · rw [abs_of_nonpos h0]; linarith [neg_abs_le b, abs_nonneg a]
  linarith

lemma cin_mono {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) : Cin A ≤ Cin B := by
  unfold Cin
  have h := intervalIntegral.integral_interval_sub_left (intervalIntegrable_cin 0 B) (intervalIntegrable_cin 0 A)
  have hnn : 0 ≤ ∫ u in A..B, (1 - Real.cos u) / u :=
    intervalIntegral.integral_nonneg hAB (fun u hu => div_nonneg (by linarith [Real.cos_le_one u])
      (by linarith [hu.1]))
  linarith

/-- `∫_0^1 (1 - cos(xq))/q dq = Cin |x|`. -/
lemma integral_one_sub_cos_div (x : ℝ) :
    ∫ q in (0 : ℝ)..1, (1 - Real.cos (x * q)) / q = Cin |x| := by
  have key : ∀ y : ℝ, 0 < y → ∫ q in (0 : ℝ)..1, (1 - Real.cos (y * q)) / q = Cin y := by
    intro y hy
    have h := intervalIntegral.integral_comp_mul_left (fun u => (1 - Real.cos u) / u) (a := 0) (b := 1) hy.ne'
    simp only [mul_zero, mul_one, smul_eq_mul] at h
    unfold Cin
    rw [← mul_inv_cancel_left₀ hy.ne' (∫ u in (0 : ℝ)..y, (1 - Real.cos u) / u), ← h,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun q _ => ?_)
    rcases eq_or_ne q 0 with hq | hq
    · simp [hq]
    · field_simp
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [abs_of_neg hx, ← key (-x) (by linarith)]
    refine intervalIntegral.integral_congr (fun q _ => ?_)
    simp only [neg_mul, Real.cos_neg]
  · subst hx; simp [Cin]
  · rw [abs_of_pos hx, key x hx]

lemma intervalIntegrable01_of_bound {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ q ∈ Ioc (0 : ℝ) 1, |f q| ≤ C) : IntervalIntegrable f volume 0 1 := by
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr ?_
  exact Measure.integrableOn_of_bounded (M := C) (by simp) hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun q hq => by rw [Real.norm_eq_abs]; exact hC q hq))

lemma sin_two_pi_nat_reflect (K : ℝ) (hK : ∃ k : ℕ, K = k) (q : ℝ) :
    Real.sin (2 * Real.pi * K * (1 - q)) = -Real.sin (2 * Real.pi * K * q) := by
  obtain ⟨k, rfl⟩ := hK
  rw [show 2 * Real.pi * (k : ℝ) * (1 - q) = ((k : ℤ) : ℝ) * (2 * Real.pi) - 2 * Real.pi * k * q by
    push_cast; ring, Real.sin_int_mul_two_pi_sub]

/-- Lemma B4: `W(k,l) = ∫_0^1 sin(2πkq) sin(2πlq) dq/(q(1-q)) ≥ 0` for integers `k, l ≥ 1`. -/
lemma W_nonneg (k l : ℕ) :
    0 ≤ ∫ q in Ioo (0 : ℝ) 1, Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q) *
      Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q) / (q * (1 - q)) := by
  set a : ℝ := 2 * Real.pi * ((k : ℝ) + 1) with ha
  set b : ℝ := 2 * Real.pi * ((l : ℝ) + 1) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set sf : ℝ → ℝ := fun q => Real.sin (a * q) * Real.sin (b * q) with hsf
  have hrefl : ∀ q, sf (1 - q) = sf q := by
    intro q
    simp only [hsf]
    rw [show a * (1 - q) = 2 * Real.pi * ((k : ℝ) + 1) * (1 - q) by rw [ha],
      show b * (1 - q) = 2 * Real.pi * ((l : ℝ) + 1) * (1 - q) by rw [hb],
      sin_two_pi_nat_reflect _ ⟨k + 1, by push_cast; ring⟩, sin_two_pi_nat_reflect _ ⟨l + 1, by push_cast; ring⟩]
    rw [← ha, ← hb]; ring
  have hmeas : Measurable sf := by simp only [hsf]; fun_prop
  -- integrability of s/q and s/(1-q)
  have hI1 : IntervalIntegrable (fun q => sf q / q) volume 0 1 := by
    refine intervalIntegrable01_of_bound (hmeas.div measurable_id) a (fun q hq => ?_)
    simp only [hsf]
    rw [abs_div, abs_mul, abs_of_pos hq.1, div_le_iff₀ hq.1]
    have h1 : |Real.sin (a * q)| ≤ a * q := by
      calc |Real.sin (a * q)| ≤ |a * q| := Real.abs_sin_le_abs
        _ = a * q := abs_of_nonneg (mul_nonneg ha0 hq.1.le)
    have h2 : |Real.sin (b * q)| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [abs_nonneg (Real.sin (a * q)), abs_nonneg (Real.sin (b * q))]
  have hI2 : IntervalIntegrable (fun q => sf q / (1 - q)) volume 0 1 := by
    have hm : Measurable (fun q : ℝ => sf q / (1 - q)) := hmeas.div (by fun_prop)
    refine intervalIntegrable01_of_bound hm b (fun q hq => ?_)
    rcases eq_or_lt_of_le hq.2 with h1 | h1
    · subst h1; simpa using hb0
    have hq1 : 0 < 1 - q := by linarith
    simp only [hsf]
    rw [abs_div, abs_mul, abs_of_pos hq1, div_le_iff₀ hq1]
    have h1 : |Real.sin (b * q)| ≤ b * (1 - q) := by
      have e : Real.sin (b * q) = -Real.sin (2 * Real.pi * ((l : ℝ) + 1) * (1 - q)) := by
        rw [sin_two_pi_nat_reflect _ ⟨l + 1, by push_cast; ring⟩, neg_neg, ← hb]
      rw [e, abs_neg]
      calc |Real.sin (2 * Real.pi * ((l : ℝ) + 1) * (1 - q))| ≤ |2 * Real.pi * ((l : ℝ) + 1) * (1 - q)| :=
            Real.abs_sin_le_abs
        _ = b * (1 - q) := by rw [← hb]; exact abs_of_nonneg (mul_nonneg hb0 hq1.le)
    have h2 : |Real.sin (a * q)| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [abs_nonneg (Real.sin (a * q)), abs_nonneg (Real.sin (b * q))]
  have hcos_int : ∀ x : ℝ, IntervalIntegrable (fun q => (1 - Real.cos (x * q)) / q) volume 0 1 := by
    intro x
    have hm : Measurable (fun q : ℝ => (1 - Real.cos (x * q)) / q) := by fun_prop
    refine intervalIntegrable01_of_bound hm (x ^ 2 / 2) (fun q hq => ?_)
    have h1 : 0 ≤ 1 - Real.cos (x * q) := by linarith [Real.cos_le_one (x * q)]
    have h2 : 1 - Real.cos (x * q) ≤ (x * q) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := x * q)]
    rw [abs_div, abs_of_nonneg h1, abs_of_pos hq.1, div_le_iff₀ hq.1]
    have : (x * q) ^ 2 / 2 ≤ x ^ 2 / 2 * q := by
      have hq2 : q ^ 2 ≤ q := by nlinarith [hq.1, hq.2]
      have : (x * q) ^ 2 = x ^ 2 * q ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg x]
    linarith
  -- convert to interval integrals
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hsplit : ∫ q in (0 : ℝ)..1, Real.sin (a * q) * Real.sin (b * q) / (q * (1 - q)) =
      (∫ q in (0 : ℝ)..1, sf q / q) + ∫ q in (0 : ℝ)..1, sf q / (1 - q) := by
    rw [← intervalIntegral.integral_add hI1 hI2]
    refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one (fun q hq => ?_)
    have hq0 : q ≠ 0 := hq.1.ne'
    have hq1 : 1 - q ≠ 0 := by linarith [hq.2]
    simp only [hsf]
    field_simp
    ring
  have hsym : ∫ q in (0 : ℝ)..1, sf q / (1 - q) = ∫ q in (0 : ℝ)..1, sf q / q := by
    have h := intervalIntegral.integral_comp_sub_left (fun x => sf x / (1 - x)) (a := 0) (b := 1) 1
    simp only [sub_zero, sub_self] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun q _ => ?_)
    simp only [hrefl, sub_sub_cancel]
  have hprod : ∫ q in (0 : ℝ)..1, sf q / q =
      ((∫ q in (0 : ℝ)..1, (1 - Real.cos ((a + b) * q)) / q) -
        ∫ q in (0 : ℝ)..1, (1 - Real.cos ((a - b) * q)) / q) / 2 := by
    rw [← intervalIntegral.integral_sub (hcos_int _) (hcos_int _), ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr (fun q _ => ?_)
    simp only [hsf]
    rcases eq_or_ne q 0 with hq | hq
    · simp [hq]
    · rw [show (a + b) * q = a * q + b * q by ring, show (a - b) * q = a * q - b * q by ring,
        Real.cos_add, Real.cos_sub]
      field_simp
      ring
  rw [hsplit, hsym, hprod, integral_one_sub_cos_div, integral_one_sub_cos_div]
  have hmono : Cin |a - b| ≤ Cin |a + b| := by
    apply cin_mono (abs_nonneg _)
    rw [abs_of_nonneg (by linarith : 0 ≤ a + b)]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  linarith

/-- Positivity of the q-form pairing of two nonnegative sine series (the proof of Theorem B at frequency v). -/
lemma sine_pair_nonneg {h1 h2 : ℝ → ℝ} {β γ : ℕ → ℝ} (hβ0 : ∀ k, 0 ≤ β k) (hβs : Summable β)
    (hγ0 : ∀ k, 0 ≤ γ k) (hγs : Summable γ)
    (h1s : ∀ q ∈ Icc (0 : ℝ) 1, HasSum (fun k : ℕ => β k * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q)) (h1 q))
    (h2s : ∀ q ∈ Icc (0 : ℝ) 1, HasSum (fun k : ℕ => γ k * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q)) (h2 q))
    (h1m : Continuous h1) (C : ℝ) (hC : ∀ q ∈ Ioo (0 : ℝ) 1, |h1 q| ≤ C * (q * (1 - q))) :
    0 ≤ ∫ q in Ioo (0 : ℝ) 1, h1 q * h2 q / (q * (1 - q)) := by
  set μ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  have hfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩; simp [μ]
  have hsinm : ∀ m : ℕ, Measurable (fun q : ℝ => Real.sin (2 * Real.pi * ((m : ℝ) + 1) * q)) :=
    fun m => by fun_prop
  have hwm : Measurable (fun q : ℝ => q * (1 - q)) := by fun_prop
  -- outer swap over γ
  have outer : HasSum (fun l : ℕ => ∫ q in Ioo (0 : ℝ) 1,
      h1 q * (γ l * Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q)) / (q * (1 - q)))
      (∫ q in Ioo (0 : ℝ) 1, h1 q * h2 q / (q * (1 - q))) := by
    refine hasSum_integral_of_dominated_convergence (fun l _ => C * γ l) (fun l => ?_) (fun l => ?_) ?_ ?_ ?_
    · exact ((h1m.measurable.mul ((hsinm l).const_mul _)).div hwm).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq => ?_)
      have hs : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, div_le_iff₀ hs, abs_mul, abs_mul, abs_of_nonneg (hγ0 l)]
      have := hC q hq
      have h3 := Real.abs_sin_le_one (2 * Real.pi * ((l : ℝ) + 1) * q)
      have hC0 : 0 ≤ C := by
        have := (abs_nonneg (h1 q)).trans this
        exact nonneg_of_mul_nonneg_left this hs
      calc |h1 q| * (γ l * |Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q)|)
          ≤ (C * (q * (1 - q))) * (γ l * 1) := by
            apply mul_le_mul this (mul_le_mul_of_nonneg_left h3 (hγ0 l))
              (mul_nonneg (hγ0 l) (abs_nonneg _)) (mul_nonneg hC0 hs.le)
        _ = C * γ l * (q * (1 - q)) := by ring
    · exact Eventually.of_forall (fun _ => hγs.mul_left C)
    · exact integrable_const _
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq => ?_)
      have := ((h2s q ⟨hq.1.le, hq.2.le⟩).mul_left (h1 q)).div_const (q * (1 - q))
      exact this
  refine outer.nonneg (fun l => ?_)
  -- inner: ∫ h1 sin_l w = ∑ β_k W(k,l) ≥ 0
  have inner : HasSum (fun k : ℕ => ∫ q in Ioo (0 : ℝ) 1, β k * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q) *
      Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q) / (q * (1 - q)))
      (∫ q in Ioo (0 : ℝ) 1, h1 q * Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q) / (q * (1 - q))) := by
    refine hasSum_integral_of_dominated_convergence (fun k _ => β k * (4 * Real.pi * ((l : ℝ) + 1)))
      (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
    · exact ((((hsinm k).const_mul _).mul (hsinm l)).div hwm).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq => ?_)
      have hs : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
      have hb := abs_sin_div_le (m := (l : ℝ) + 1) ⟨l + 1, by push_cast; ring⟩ hq
      rw [abs_of_pos (by positivity : (0 : ℝ) < (l : ℝ) + 1)] at hb
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_nonneg (hβ0 k), abs_of_pos hs]
      have h3 := Real.abs_sin_le_one (2 * Real.pi * ((k : ℝ) + 1) * q)
      calc β k * |Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q)| * |Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q)| /
            (q * (1 - q))
          = β k * |Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q)| *
            (|Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q)| / (q * (1 - q))) := by ring
        _ ≤ β k * 1 * (4 * Real.pi * ((l : ℝ) + 1)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h3 (hβ0 k)) hb (by positivity)
              (mul_nonneg (hβ0 k) zero_le_one)
        _ = β k * (4 * Real.pi * ((l : ℝ) + 1)) := by ring
    · exact Eventually.of_forall (fun _ => hβs.mul_right _)
    · exact integrable_const _
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun q hq => ?_)
      have := ((h1s q ⟨hq.1.le, hq.2.le⟩).mul_right (Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q))).div_const
        (q * (1 - q))
      exact this
  have hW : 0 ≤ ∫ q in Ioo (0 : ℝ) 1, h1 q * Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q) / (q * (1 - q)) := by
    refine inner.nonneg (fun k => ?_)
    have : (fun q => β k * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q) * Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q) /
        (q * (1 - q))) = fun q => β k * (Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q) *
          Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q) / (q * (1 - q))) := by
      funext q; ring
    rw [this, integral_const_mul]
    exact mul_nonneg (hβ0 k) (W_nonneg k l)
  have : (fun q => h1 q * (γ l * Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q)) / (q * (1 - q))) =
      fun q => γ l * (h1 q * Real.sin (2 * Real.pi * ((l : ℝ) + 1) * q) / (q * (1 - q))) := by
    funext q; ring
  rw [this, integral_const_mul]
  exact mul_nonneg (hγ0 l) hW

/-- HB: Theorem B at every frequency. -/
theorem hB : HB := by
  intro n lam v hv
  set θ : Fin n → ℝ := fun j => v * max (lam j) 0 with hθ
  set φ : Fin n → ℝ := fun j => v * max (-lam j) 0 with hφ
  have hθ0 : ∀ j, 0 ≤ θ j := fun j => mul_nonneg hv.le (le_max_right _ _)
  have hφ0 : ∀ j, 0 ≤ φ j := fun j => mul_nonneg hv.le (le_max_right _ _)
  obtain ⟨β, hβ0, hβs, hβ⟩ := sine_series θ hθ0
  obtain ⟨γ, hγ0, hγs, hγ⟩ := sine_series φ hφ0
  have hG : 0 ≤ ∫ q in Ioo (0 : ℝ) 1, (Fth θ q).im * (Fth φ q).im / (q * (1 - q)) := by
    refine sine_pair_nonneg hβ0 hβs hγ0 hγs hβ hγ
      (Complex.continuous_im.comp (continuous_Fth θ)) (2 * ∑ j, |θ j|) (fun q hq => ?_)
    calc |(Fth θ q).im| = |(Fth θ q - 1).im| := by simp
      _ ≤ ‖Fth θ q - 1‖ := Complex.abs_im_le_norm _
      _ ≤ 2 * (∑ j, |θ j|) * (q * (1 - q)) := norm_Fth_sub_one_le θ ⟨hq.1.le, hq.2.le⟩
  have hint2 : IntegrableOn (fun q => 2 * ((Fth θ q).im * (Fth φ q).im / (q * (1 - q)))) (Ioo (0 : ℝ) 1) := by
    refine integrableOn_Ioo01 ?_ (2 * (2 * ∑ j, |θ j|)) (fun q hq => ?_)
    · exact (((Complex.continuous_im.comp (continuous_Fth θ)).mul
        (Complex.continuous_im.comp (continuous_Fth φ))).measurable.div (by fun_prop)).const_mul 2
    · have hs : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
      have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
      have h1 : |(Fth θ q).im| ≤ 2 * (∑ j, |θ j|) * (q * (1 - q)) := by
        calc |(Fth θ q).im| = |(Fth θ q - 1).im| := by simp
          _ ≤ ‖Fth θ q - 1‖ := Complex.abs_im_le_norm _
          _ ≤ _ := norm_Fth_sub_one_le θ hq'
      have h2 : |(Fth φ q).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (norm_Fth_le φ hq')
      rw [abs_mul, abs_div, abs_mul, abs_of_pos hs, abs_two]
      rw [mul_le_mul_iff_of_pos_left two_pos, div_le_iff₀ hs]
      calc |(Fth θ q).im| * |(Fth φ q).im| ≤ (2 * (∑ j, |θ j|) * (q * (1 - q))) * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 2 * (∑ j, |θ j|) * (q * (1 - q)) := by ring
  have heq : Cfreq v (fun j => |lam j|) = Cfreq v lam +
      ∫ q in Ioo (0 : ℝ) 1, 2 * ((Fth θ q).im * (Fth φ q).im / (q * (1 - q))) := by
    unfold Cfreq
    rw [← integral_add (integrableOn_cosGap v lam) hint2]
    refine setIntegral_congr_fun measurableSet_Ioo (fun q _ => ?_)
    have := cosGap_abs_sub v q lam
    simp only [← hθ, ← hφ] at this
    rw [show cosGap v q (fun j => |lam j|) = cosGap v q lam +
      2 * (Fth θ q).im * (Fth φ q).im by linarith]
    ring
  rw [heq, integral_const_mul]
  linarith

end Poincare11b
