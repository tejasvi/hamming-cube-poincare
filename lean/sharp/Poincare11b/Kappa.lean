/-
The Fourier coefficients `κ_c(k) = (2 - 2 cos c)/(c - 2πk)²` of `f_c` on `[0,1]`, and their decomposition
`κ_c = shift_m s₀ + shift_{m+1} s₁` with symmetric unimodal `s₀, s₁` (`c ≥ 0`). This replaces the continuous mixture of
discrete Laplace laws in Lemma B3 by explicit series.
-/
import Poincare11b.SU

namespace Poincare11b

open Real Filter Topology

/-- The convexity inequality `1/(A+1)² - 1/(B+1)² ≤ 1/A² - 1/B²` for `0 < A ≤ B`. -/
lemma inv_sq_shift_ineq {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    1 / (A + 1) ^ 2 - 1 / (B + 1) ^ 2 ≤ 1 / A ^ 2 - 1 / B ^ 2 := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ B = A + d := ⟨B - A, by linarith, by ring⟩
  have h1 : A ≠ 0 := hA.ne'
  have h2 : A + d ≠ 0 := by positivity
  have h3 : A + 1 ≠ 0 := by positivity
  have h4 : A + d + 1 ≠ 0 := by positivity
  have h : (1 / A ^ 2 - 1 / (A + d) ^ 2) - (1 / (A + 1) ^ 2 - 1 / (A + d + 1) ^ 2) =
      d * (6 * A ^ 4 + 12 * A ^ 3 * d + 12 * A ^ 3 + 8 * A ^ 2 * d ^ 2 + 18 * A ^ 2 * d + 8 * A ^ 2
        + 2 * A * d ^ 3 + 8 * A * d ^ 2 + 8 * A * d + 2 * A + d ^ 3 + 2 * d ^ 2 + d) /
        (A ^ 2 * (A + d) ^ 2 * (A + 1) ^ 2 * (A + d + 1) ^ 2) := by
    field_simp
    ring
  have hpos : 0 ≤ d * (6 * A ^ 4 + 12 * A ^ 3 * d + 12 * A ^ 3 + 8 * A ^ 2 * d ^ 2 + 18 * A ^ 2 * d
      + 8 * A ^ 2 + 2 * A * d ^ 3 + 8 * A * d ^ 2 + 8 * A * d + 2 * A + d ^ 3 + 2 * d ^ 2 + d) /
        (A ^ 2 * (A + d) ^ 2 * (A + 1) ^ 2 * (A + d + 1) ^ 2) := by positivity
  linarith

lemma summable_inv_sq_lin {a : ℝ} (ha : 0 < a) : Summable (fun l : ℕ => 1 / (a + 2 * l) ^ 2) := by
  have h1 : Summable (fun l : ℕ => 1 / ((l : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine this.congr (fun l => ?_)
    push_cast; ring
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) (h1.mul_left (1 / (min a 1) ^ 2))
  have hm : 0 < min a 1 := lt_min ha one_pos
  have hle : min a 1 * ((l : ℝ) + 1) ≤ a + 2 * l := by
    have h2 : min a 1 ≤ a := min_le_left _ _
    have h3 : min a 1 ≤ 1 := min_le_right _ _
    have h4 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  rw [div_mul_div_comm, one_mul, ← mul_pow]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hle 2)

/-- `T(a,b) = ∑_{l ≥ 0} (1/(a+2l)² - 1/(b+2l)²)`. -/
noncomputable def Tser (a b : ℝ) : ℝ := ∑' l : ℕ, (1 / (a + 2 * l) ^ 2 - 1 / (b + 2 * l) ^ 2)

lemma Tser_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tser a b = (∑' l : ℕ, 1 / (a + 2 * l) ^ 2) - ∑' l : ℕ, 1 / (b + 2 * l) ^ 2 :=
  (summable_inv_sq_lin ha).tsum_sub (summable_inv_sq_lin hb)

lemma Tser_add {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Tser a b + Tser b c = Tser a c := by
  rw [Tser_eq ha hb, Tser_eq hb hc, Tser_eq ha hc]; ring

lemma Tser_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : 0 ≤ Tser a b :=
  tsum_nonneg (fun l => sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ (by positivity) (by linarith) 2)))

lemma Tser_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Tser (a + 1) (b + 1) ≤ Tser a b := by
  have hb : 0 < b := by linarith
  refine Summable.tsum_le_tsum (fun l => ?_)
    ((summable_inv_sq_lin (by linarith : 0 < a + 1)).sub (summable_inv_sq_lin (by linarith : 0 < b + 1)))
    ((summable_inv_sq_lin ha).sub (summable_inv_sq_lin hb))
  have h := inv_sq_shift_ineq (A := a + 2 * l) (B := b + 2 * l) (by positivity) (by linarith)
  rw [show a + 1 + 2 * (l : ℝ) = a + 2 * l + 1 by ring, show b + 1 + 2 * (l : ℝ) = b + 2 * l + 1 by ring]
  exact h

lemma Tser_tele {a : ℝ} (ha : 0 < a) : Tser a (a + 2) = 1 / a ^ 2 := by
  set f : ℕ → ℝ := fun l => 1 / (a + 2 * l) ^ 2 with hf
  have hterm : ∀ l : ℕ, 1 / (a + 2 * l) ^ 2 - 1 / (a + 2 + 2 * l) ^ 2 = f l - f (l + 1) := by
    intro l; simp only [hf, Nat.cast_add, Nat.cast_one]; ring_nf
  have hnn : ∀ l, 0 ≤ f l - f (l + 1) := by
    intro l
    rw [← hterm]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity) (by linarith) 2))
  have hlim : Tendsto f atTop (𝓝 0) := (summable_inv_sq_lin ha).tendsto_atTop_zero
  have hs : HasSum (fun l => f l - f (l + 1)) (f 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    simp_rw [Finset.sum_range_sub']
    simpa using (tendsto_const_nhds (x := f 0)).sub hlim
  unfold Tser
  simp_rw [hterm]
  rw [hs.tsum_eq]
  simp [hf]

/-- The Fourier coefficients of `f_c` on `[0,1]`. -/
noncomputable def kap (c : ℝ) (k : ℤ) : ℝ :=
  if c = 2 * Real.pi * k then 1 else (2 - 2 * Real.cos c) / (c - 2 * Real.pi * k) ^ 2

lemma kap_nonneg (c : ℝ) (k : ℤ) : 0 ≤ kap c k := by
  unfold kap
  split_ifs
  · norm_num
  · exact div_nonneg (by linarith [Real.cos_le_one c]) (sq_nonneg _)

lemma kap_summable (c : ℝ) : Summable (kap c) := by
  have hg : Summable (fun k : ℤ => 4 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr one_lt_two).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  -- outside the finite set |k| ≤ N the bound holds, N := ⌈|c|/π⌉
  set N : ℕ := ⌈|c| / Real.pi⌉₊ with hN
  have hfin : {k : ℤ | ¬ (‖kap c k‖ ≤ 4 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2))}.Finite := by
    refine (Set.finite_Icc (-(N : ℤ)) N).subset (fun k hk => ?_)
    simp only [Set.mem_ofPred_eq] at hk
    simp only [Set.mem_Icc]
    by_contra hcon
    apply hk
    have hkN : (N : ℝ) < |(k : ℝ)| := by
      have : (N : ℤ) < |k| := by
        rcases le_or_gt 0 k with h0 | h0
        · rw [abs_of_nonneg h0]; omega
        · rw [abs_of_neg h0]; omega
      exact_mod_cast this
    have hpi := Real.pi_pos
    have hcN : |c| ≤ Real.pi * N := by
      have := Nat.le_ceil (|c| / Real.pi)
      rw [← hN] at this
      rw [div_le_iff₀ hpi] at this; linarith
    have hk0 : (0 : ℝ) < |(k : ℝ)| := lt_of_le_of_lt (Nat.cast_nonneg N) hkN
    -- |c - 2πk| ≥ π|k|
    have hgap : Real.pi * |(k : ℝ)| ≤ |c - 2 * Real.pi * k| := by
      have h1 : |2 * Real.pi * (k : ℝ)| = 2 * Real.pi * |(k : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have h2 := abs_sub_abs_le_abs_sub (2 * Real.pi * (k : ℝ)) c
      rw [abs_sub_comm] at h2
      nlinarith
    have hne : c ≠ 2 * Real.pi * k := by
      intro h; rw [h, sub_self, abs_zero] at hgap; nlinarith
    rw [Real.norm_of_nonneg (kap_nonneg c k)]
    unfold kap
    rw [ite_eq_right hne]
    have hsq : (Real.pi * |(k : ℝ)|) ^ 2 ≤ (c - 2 * Real.pi * k) ^ 2 := by
      rw [← sq_abs (c - 2 * Real.pi * k)]
      exact pow_le_pow_left₀ (by positivity) hgap 2
    have hnum : 2 - 2 * Real.cos c ≤ 4 := by linarith [Real.neg_one_le_cos c]
    have hnum0 : 0 ≤ 2 - 2 * Real.cos c := by linarith [Real.cos_le_one c]
    have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
      have : (k : ℝ) ≠ 0 := fun h => by rw [h, abs_zero] at hk0; exact lt_irrefl 0 hk0
      positivity
    calc (2 - 2 * Real.cos c) / (c - 2 * Real.pi * k) ^ 2
        ≤ 4 / (Real.pi * |(k : ℝ)|) ^ 2 := by
          apply div_le_div₀ (by norm_num) hnum (by positivity) hsq
      _ = 4 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) := by
          rw [mul_pow, sq_abs]; field_simp
  exact hfin

/-- `κ_c = shift_m s₀ + shift_{m+1} s₁` with symmetric unimodal `s₀, s₁`, for `c ≥ 0`. -/
theorem kap_decomp {c : ℝ} (hc : 0 ≤ c) :
    ∃ m : ℕ, ∃ s0 s1 : ℤ → ℝ, SU s0 ∧ SU s1 ∧ ∀ k : ℤ, kap c k = s0 (k - m) + s1 (k - m - 1) := by
  have hpi := Real.pi_pos
  set x : ℝ := c / (2 * Real.pi) with hx
  have hx0 : 0 ≤ x := div_nonneg hc (by positivity)
  set m : ℕ := ⌊x⌋₊ with hm
  set y : ℝ := x - m with hy
  have hy0 : 0 ≤ y := sub_nonneg.mpr (Nat.floor_le hx0)
  have hy1 : y < 1 := by
    have := Nat.lt_floor_add_one x
    rw [← hm] at this; linarith
  have hcxy : c = 2 * Real.pi * (m + y) := by
    rw [hy, add_sub_cancel, hx]; field_simp
  have hdiff : ∀ k : ℤ, c - 2 * Real.pi * k = 2 * Real.pi * (y - ((k : ℝ) - m)) := by
    intro k; rw [hcxy]; ring
  rcases eq_or_lt_of_le hy0 with hy00 | hypos
  · -- `c = 2πm`: `κ_c` is the point mass at `m`
    refine ⟨m, delta0, 0, SU_delta0, SU_zero, fun k => ?_⟩
    have hcm : c = (m : ℝ) * (2 * Real.pi) := by rw [hcxy, ← hy00]; ring
    have hcos : Real.cos c = 1 := by rw [hcm]; exact Real.cos_nat_mul_two_pi m
    simp only [Pi.zero_apply, add_zero, delta0]
    unfold kap
    by_cases hk : k = m
    · subst hk
      simp only [sub_self, ite_true]
      rw [ite_eq_left]; rw [hcm]; push_cast; ring
    · have hk' : k - m ≠ 0 := sub_ne_zero.mpr hk
      rw [ite_eq_right hk', hcos]
      have hne : c ≠ 2 * Real.pi * k := by
        intro h
        apply hk
        have : (m : ℝ) = k := by
          have h2 : (m : ℝ) * (2 * Real.pi) = k * (2 * Real.pi) := by rw [← hcm, h]; ring
          exact mul_right_cancel₀ (by positivity) h2
        exact_mod_cast this.symm
      rw [ite_eq_right hne]; ring
  · -- `0 < y < 1`
    set C : ℝ := (2 - 2 * Real.cos c) / (4 * Real.pi ^ 2) with hC
    have hC0 : 0 ≤ C := div_nonneg (by linarith [Real.cos_le_one c]) (by positivity)
    set s0 : ℤ → ℝ := fun j => C * Tser (|(j : ℝ)| + y) (|(j : ℝ)| + 2 - y) with hs0
    set s1 : ℤ → ℝ := fun j => C * Tser (|(j : ℝ)| + 1 - y) (|(j : ℝ)| + 1 + y) with hs1
    have hs0nn : ∀ j, 0 ≤ s0 j := fun j => mul_nonneg hC0 (Tser_nonneg (by positivity) (by linarith))
    have hs1nn : ∀ j, 0 ≤ s1 j := fun j => mul_nonneg hC0
      (Tser_nonneg (by have := abs_nonneg (j : ℝ); linarith) (by linarith))
    have hkapj : ∀ j : ℤ, kap c (j + m) = C / ((j : ℝ) - y) ^ 2 := by
      intro j
      have hne : c ≠ 2 * Real.pi * ((j + m : ℤ) : ℝ) := by
        intro h
        have h2 := hdiff (j + m)
        rw [h, sub_self] at h2
        push_cast at h2
        have h3 : y - ((j : ℝ) + m - m) = 0 := by
          rcases mul_eq_zero.mp h2.symm with h4 | h4
          · exact absurd h4 (by positivity)
          · exact h4
        have h5 : y = (j : ℝ) := by linarith
        have h6 : (0 : ℝ) < j := by linarith
        have h7 : (j : ℝ) < 1 := by linarith
        have h8 : (0 : ℤ) < j := by exact_mod_cast h6
        have h9 : j < (1 : ℤ) := by exact_mod_cast h7
        omega
      unfold kap
      rw [ite_eq_right hne, hdiff (j + m)]
      push_cast
      rw [hC, mul_pow]
      field_simp
      ring
    have hid : ∀ j : ℤ, kap c (j + m) = s0 j + s1 (j - 1) := by
      intro j
      rw [hkapj j]
      simp only [hs0, hs1]
      push_cast
      rcases le_or_gt 1 j with hj | hj
      · have hJ : (1 : ℝ) ≤ j := by exact_mod_cast hj
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ j), abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) - 1)]
        rw [show (j : ℝ) - 1 + 1 - y = (j : ℝ) - y by ring, show (j : ℝ) - 1 + 1 + y = (j : ℝ) + y by ring,
          ← mul_add, add_comm (Tser ((j : ℝ) + y) _), Tser_add (by linarith) (by linarith) (by linarith),
          show (j : ℝ) + 2 - y = ((j : ℝ) - y) + 2 by ring, Tser_tele (by linarith)]
        ring
      · have hJ : (j : ℝ) ≤ 0 := by
          have : j ≤ 0 := by omega
          exact_mod_cast this
        rw [abs_of_nonpos hJ, abs_of_nonpos (by linarith : (j : ℝ) - 1 ≤ 0)]
        rw [show -((j : ℝ) - 1) + 1 - y = 2 - (j : ℝ) - y by ring,
          show -((j : ℝ) - 1) + 1 + y = 2 - (j : ℝ) + y by ring,
          show -(j : ℝ) + y = y - j by ring, show -(j : ℝ) + 2 - y = 2 - (j : ℝ) - y by ring,
          ← mul_add, Tser_add (by linarith) (by linarith) (by linarith),
          show 2 - (j : ℝ) + y = (y - j) + 2 by ring, Tser_tele (by linarith)]
        rw [show ((j : ℝ) - y) ^ 2 = (y - j) ^ 2 by ring]
        ring
    have hkapS : Summable (fun j : ℤ => kap c (j + m)) := by
      have := (Equiv.addRight (m : ℤ)).summable_iff.mpr (kap_summable c)
      exact this.congr (fun j => by simp only [Function.comp_apply, Equiv.coe_addRight])
    have hkapS1 : Summable (fun j : ℤ => kap c (j + 1 + m)) := by
      have := (Equiv.addRight (1 : ℤ)).summable_iff.mpr hkapS
      exact this.congr (fun j => by simp only [Function.comp_apply, Equiv.coe_addRight])
    refine ⟨m, s0, s1, ⟨⟨hs0nn, ?_⟩, fun j => ?_, fun k => ?_⟩, ⟨⟨hs1nn, ?_⟩, fun j => ?_, fun k => ?_⟩, fun k => ?_⟩
    · refine Summable.of_nonneg_of_le hs0nn (fun j => ?_) hkapS
      rw [hid j]; linarith [hs1nn (j - 1)]
    · simp only [hs0]; push_cast; rw [abs_neg]
    · simp only [hs0]; push_cast
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), abs_of_nonneg (Nat.cast_nonneg k)]
      apply mul_le_mul_of_nonneg_left _ hC0
      have := Tser_anti (a := (k : ℝ) + y) (b := (k : ℝ) + 2 - y) (by positivity) (by linarith)
      rw [show (k : ℝ) + y + 1 = (k : ℝ) + 1 + y by ring, show (k : ℝ) + 2 - y + 1 = (k : ℝ) + 1 + 2 - y by ring]
        at this
      exact this
    · refine Summable.of_nonneg_of_le hs1nn (fun j => ?_) hkapS1
      have := hid (j + 1)
      rw [add_sub_cancel_right] at this
      rw [this]; linarith [hs0nn (j + 1)]
    · simp only [hs1]; push_cast; rw [abs_neg]
    · simp only [hs1]; push_cast
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), abs_of_nonneg (Nat.cast_nonneg k)]
      apply mul_le_mul_of_nonneg_left _ hC0
      have := Tser_anti (a := (k : ℝ) + 1 - y) (b := (k : ℝ) + 1 + y) (by linarith) (by linarith)
      rw [show (k : ℝ) + 1 - y + 1 = (k : ℝ) + 1 + 1 - y by ring,
        show (k : ℝ) + 1 + y + 1 = (k : ℝ) + 1 + 1 + y by ring] at this
      exact this
    · have := hid (k - m)
      rw [sub_add_cancel] at this
      rw [this]

end Poincare11b
