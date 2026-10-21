/-
Paper Theorem 4.2 (`K ≤ 71/50`, with `J` the interval integral of Defs.lean), and two facts showing that `J` is the
genuine integral: its integrand is interval integrable, and `J(e_1) = 1`.
-/
import Poincare11a.Assembly
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Poincare11a

open Finset Poincare11a.Cert MeasureTheory Set

variable {n : ℕ}

/-! ### The `ξ`-form of the paper equals the `δ`-form used in the proofs -/

lemma xiProb_eq_wt (m : ℝ) (b : Bool) : xiProb ((1 + m) / 2) b = wt m b := by
  cases b <;> simp [xiProb, wt]; ring

lemma xiVal_eq_dl {m c : ℝ} (hc : 0 < c) (hcm : c ^ 2 = 1 - m ^ 2) (b : Bool) :
    xiVal ((1 + m) / 2) b = dl m c b := by
  have hm1 : m < 1 := by nlinarith [sq_nonneg (m - 1), sq_nonneg c]
  have hm2 : -1 < m := by nlinarith [sq_nonneg (m + 1), sq_nonneg c]
  have h1m : (0 : ℝ) < 1 - m := by linarith
  have h1p : (0 : ℝ) < 1 + m := by linarith
  cases b
  · simp only [xiVal, dl, Bool.false_eq_true, ite_false]
    rw [neg_div, neg_inj]
    rw [show (1 : ℝ) - (1 + m) / 2 = (1 - m) / 2 by ring, div_div_div_cancel_right₀ two_ne_zero]
    rw [Real.sqrt_eq_iff_mul_self_eq (div_nonneg h1p.le h1m.le) (div_nonneg h1p.le hc.le)]
    rw [div_mul_div_comm, div_eq_div_iff h1m.ne' (by positivity)]
    linear_combination (1 + m) * hcm
  · simp only [xiVal, dl, ite_true]
    rw [show (1 : ℝ) - (1 + m) / 2 = (1 - m) / 2 by ring, div_div_div_cancel_right₀ two_ne_zero]
    rw [Real.sqrt_eq_iff_mul_self_eq (div_nonneg h1m.le h1p.le) (div_nonneg h1m.le hc.le)]
    rw [div_mul_div_comm, div_eq_div_iff h1p.ne' (by positivity)]
    linear_combination (1 - m) * hcm

lemma absMoment_eq_Phi {θ : ℝ} (hc : 0 < Real.cos θ) (lam : Fin n → ℝ) :
    absMoment ((1 + Real.sin θ) / 2) lam = Phi (Real.sin θ) (Real.cos θ) lam := by
  have hcm : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
  simp only [absMoment, Phi, Ex, Ssum, xiProb_eq_wt, xiVal_eq_dl hc hcm]

/-! ### Bounds and integrability of the integrand of `J` -/

lemma Phi_le_half {m c : ℝ} (hc : 0 < c) (hcm : c ^ 2 = 1 - m ^ 2) (lam : Fin n → ℝ) :
    Phi m c lam ≤ (1 + psum lam 2) / 2 := by
  have hmom := moments_hold (wt m) (dl m c) (mom_dl_0 hc hcm) (mom_dl_1 hc hcm) (mom_dl_2 hc hcm) lam
  obtain ⟨e0, -, e2, -⟩ := hmom
  have h : ∀ z, |Ssum (dl m c) lam z| ≤ (1 / 2) * Ssum (dl m c) lam z ^ 0 + (1 / 2) * Ssum (dl m c) lam z ^ 2 :=
    fun z => by
      have := sq_nonneg (|Ssum (dl m c) lam z| - 1)
      rw [pow_zero, ← sq_abs (Ssum (dl m c) lam z)]; nlinarith
  calc Phi m c lam ≤ Ex (wt m) (fun z => (1 / 2) * Ssum (dl m c) lam z ^ 0 + (1 / 2) * Ssum (dl m c) lam z ^ 2) :=
        Ex_mono _ (wt_nonneg_of hc hcm) h
    _ = (1 + psum lam 2) / 2 := by
        rw [Ex_add, Ex_smul, Ex_smul]
        simp only at e0 e2
        rw [e0, e2]; ring

lemma absMoment_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (lam : Fin n → ℝ) : 0 ≤ absMoment p lam := by
  unfold absMoment
  refine Finset.sum_nonneg (fun z _ => mul_nonneg (Finset.prod_nonneg (fun j _ => ?_)) (abs_nonneg _))
  cases z j <;> simp [xiProb] <;> linarith

lemma absMoment_one (lam : Fin n → ℝ) : absMoment 1 lam = 0 := by
  have : ∀ b, xiVal 1 b = 0 := fun b => by cases b <;> simp [xiVal]
  simp [absMoment, this]

/-- On `[0, π/2]` the integrand of `J` lies in `[0, (1 + |λ|²)/2]`. -/
lemma absMoment_mem {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) (lam : Fin n → ℝ) :
    0 ≤ absMoment ((1 + Real.sin θ) / 2) lam ∧ absMoment ((1 + Real.sin θ) / 2) lam ≤ (1 + psum lam 2) / 2 := by
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  refine ⟨absMoment_nonneg (by linarith) (by linarith) lam, ?_⟩
  have hP : 0 ≤ psum lam 2 := psum_even_nonneg lam 1
  rcases h1.lt_or_eq with h1 | h1
  · have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
    rw [absMoment_eq_Phi hc]
    exact Phi_le_half hc (by linarith [Real.sin_sq_add_cos_sq θ]) lam
  · rw [h1, Real.sin_pi_div_two, show (1 + 1 : ℝ) / 2 = 1 by norm_num, absMoment_one]
    linarith

lemma measurable_absMoment (lam : Fin n → ℝ) :
    Measurable (fun θ : ℝ => absMoment ((1 + Real.sin θ) / 2) lam) := by
  unfold absMoment
  refine Finset.measurable_sum _ (fun z _ => Measurable.mul ?_ ?_)
  · refine Finset.measurable_prod _ (fun j _ => ?_)
    cases z j <;> simp only [xiProb] <;> fun_prop
  · refine Measurable.comp (g := fun x : ℝ => |x|) continuous_abs.measurable ?_
    refine Finset.measurable_sum _ (fun j _ => Measurable.const_mul ?_ _)
    cases z j <;> simp only [xiVal]
    · exact (Measurable.sqrt (by fun_prop)).neg
    · exact Measurable.sqrt (by fun_prop)

/-- The integrand of `J` is interval integrable on every subinterval of `[0, π/2]`. -/
lemma absMoment_intervalIntegrable (lam : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    IntervalIntegrable (fun θ => absMoment ((1 + Real.sin θ) / 2) lam) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := (1 + psum lam 2) / 2) ?_
    (measurable_absMoment lam).aestronglyMeasurable ?_
  · simp [Real.volume_Icc]
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun θ hθ => ?_))
    have h := absMoment_mem (le_trans ha hθ.1) (le_trans hθ.2 hb) lam
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2

/-- The integrand of `J` is interval integrable on `[0, π/2]` (so `J` is not a junk value). -/
theorem J_intervalIntegrable (lam : Fin n → ℝ) :
    IntervalIntegrable (fun θ => absMoment ((1 + Real.sin θ) / 2) lam) volume 0 (Real.pi / 2) :=
  absMoment_intervalIntegrable lam le_rfl (by positivity) le_rfl

/-- `J(e_1) = 1` (paper Remark 2.3(i)), a value check of the definition of `J`. -/
theorem J_e1 : J (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
  have h : ∀ θ ∈ Set.uIcc 0 (Real.pi / 2), absMoment ((1 + Real.sin θ) / 2) (fun _ : Fin 1 => (1 : ℝ)) =
      Real.cos θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by positivity)] at hθ
    rcases hθ.2.lt_or_eq with h1 | h1
    · have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], h1⟩
      have hcm : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
      rw [absMoment_eq_Phi hc]
      simp only [Phi, Ex, Ssum, Fin.prod_univ_one, Fin.sum_univ_one, one_mul]
      rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
      simp only [Equiv.funUnique_symm_apply, uniqueElim_const, wt, dl, ite_true, Bool.false_eq_true, ite_false]
      have hm1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
      have hm0 : -1 ≤ Real.sin θ := Real.neg_one_le_sin θ
      rw [abs_of_nonneg (div_nonneg (by linarith) hc.le), abs_of_nonpos (by
        rw [neg_div]; exact neg_nonpos.2 (div_nonneg (by linarith) hc.le))]
      field_simp
      nlinarith [hcm]
    · rw [h1, Real.sin_pi_div_two, Real.cos_pi_div_two, show (1 + 1 : ℝ) / 2 = 1 by norm_num, absMoment_one]
  rw [J, intervalIntegral.integral_congr h, integral_cos, Real.sin_pi_div_two, Real.sin_zero, sub_zero]

/-! ### Theorem 4.2 -/

/-- Left end of interval `k` of the partition (`π/2`-side end `T = 2^32` past the last interval). -/
def TLat (ivs : List Ivl) (k : ℕ) : Int := ((ivs[k]?).map Ivl.TL).getD P32

lemma chain_TLat : ∀ (t : Int) (ivs : List Ivl), chainOK t ivs = true →
    TLat ivs 0 = t ∧ ∀ k (hk : k < ivs.length), ivs[k].TR = TLat ivs (k + 1)
  | t, [], h => by
    simp only [chainOK, decide_eq_true_eq] at h
    exact ⟨by simp [TLat, h], fun k hk => absurd hk (by simp)⟩
  | t, iv :: ivs, h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, -⟩, h3⟩ := h
    obtain ⟨b1, b2⟩ := chain_TLat iv.TR ivs h3
    refine ⟨by simp [TLat, h1], fun k hk => ?_⟩
    cases k with
    | zero => simpa [TLat] using b1.symm
    | succ k =>
      have := b2 k (by simpa using hk)
      simpa [TLat] using this

lemma list_sum_eq_range {α : Type*} (g : α → ℝ) : ∀ L : List α,
    (L.map g).sum = ∑ k ∈ Finset.range L.length, ((L[k]?).map g).getD 0
  | [] => by simp
  | x :: L => by
    rw [List.map_cons, List.sum_cons, list_sum_eq_range g L, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- Theorem 4.2 from the certificate facts: `J(λ) ≤ 71/50` for every unit vector in every dimension. -/
theorem K_le_of_cert (lib : LibT) (hlib : lib.allPos = true) (ivs : List Ivl) (hpart : partOK ivs = true)
    (t : QT) (ht : t.OK lib ivs 0 0 0) (lam : Fin n → ℝ) (hl : ∑ j, lam j ^ 2 = 1) : J lam ≤ 71 / 50 := by
  have hpart' := hpart
  simp only [partOK, Bool.and_eq_true, decide_eq_true_eq] at hpart'
  obtain ⟨-, hchain⟩ := hpart'
  obtain ⟨hivs, -⟩ := chain_facts 0 ivs hchain
  obtain ⟨hT0, hTs⟩ := chain_TLat 0 ivs hchain
  obtain ⟨L, hL, hb, hs⟩ := cert_sound lib hlib ivs hpart t ht lam hl
  set a : ℕ → ℝ := fun k => thetaOf (TLat ivs k)
  have ha0 : a 0 = 0 := by simp only [a, hT0, thetaOf_zero]
  have haN : a ivs.length = Real.pi / 2 := by simp [a, TLat, thetaOf_P32]
  have hak : ∀ k (hk : k < ivs.length), a k = thetaOf ivs[k].TL ∧ a (k + 1) = thetaOf ivs[k].TR := by
    intro k hk
    refine ⟨by simp [a, TLat, hk], by simp only [a]; rw [hTs k hk]⟩
  -- each interval lies in [0, π/2]
  have hrange : ∀ k (hk : k < ivs.length), 0 ≤ a k ∧ a k < a (k + 1) ∧ a (k + 1) ≤ Real.pi / 2 := by
    intro k hk
    obtain ⟨e1, e2⟩ := hak k hk
    obtain ⟨h0, hlt, hle, -⟩ := ivs[k].ok_facts (hivs _ (List.getElem_mem ..))
    rw [e1, e2]
    exact ⟨thetaOf_nonneg h0, thetaOf_strictMono hlt, thetaOf_le_pi_div_two hle⟩
  have hint : ∀ k < ivs.length, IntervalIntegrable (fun θ => absMoment ((1 + Real.sin θ) / 2) lam) volume
      (a k) (a (k + 1)) := fun k hk =>
    absMoment_intervalIntegrable lam (hrange k hk).1 (hrange k hk).2.1.le (hrange k hk).2.2
  have hlen : L.length = ivs.length := by rw [hL, List.length_map]
  -- the bound on each interval
  set g : Ivl × ℝ → ℝ := fun x => (thetaOf x.1.TR - thetaOf x.1.TL) * x.2
  have hU : ∀ k (hk : k < ivs.length), ∫ θ in a k..a (k + 1), absMoment ((1 + Real.sin θ) / 2) lam ≤
      g (L[k]'(hlen ▸ hk)) := by
    intro k hk
    have hx := hb (L[k]'(hlen ▸ hk)) (List.getElem_mem ..)
    have hfst : (L[k]'(hlen ▸ hk)).1 = ivs[k] := by simp [hL]
    obtain ⟨e1, e2⟩ := hak k hk
    calc ∫ θ in a k..a (k + 1), absMoment ((1 + Real.sin θ) / 2) lam
        ≤ ∫ θ in a k..a (k + 1), (L[k]'(hlen ▸ hk)).2 := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo (hrange k hk).2.1.le (hint k hk)
            intervalIntegrable_const (fun θ hθ => ?_)
          rw [e1, e2] at hθ
          have hiv := hivs _ (List.getElem_mem (h := hk))
          obtain ⟨hc, -⟩ := cos_facts ivs[k] hiv θ hθ
          rw [absMoment_eq_Phi hc]
          rw [hfst] at hx
          exact hx.2 θ hθ
      _ = (a (k + 1) - a k) * (L[k]'(hlen ▸ hk)).2 := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = g (L[k]'(hlen ▸ hk)) := by simp only [g]; rw [hfst, e1, e2]
  calc J lam = ∫ θ in a 0..a ivs.length, absMoment ((1 + Real.sin θ) / 2) lam := by rw [J, ha0, haN]
    _ = ∑ k ∈ Finset.range ivs.length, ∫ θ in a k..a (k + 1), absMoment ((1 + Real.sin θ) / 2) lam :=
        (intervalIntegral.sum_integral_adjacent_intervals hint).symm
    _ ≤ ∑ k ∈ Finset.range ivs.length, ((L[k]?).map g).getD 0 :=
        Finset.sum_le_sum (fun k hk => by
          have hk' := Finset.mem_range.1 hk
          rw [List.getElem?_eq_getElem (hlen ▸ hk'), Option.map_some, Option.getD_some]
          exact hU k hk')
    _ = (L.map g).sum := by rw [list_sum_eq_range, hlen]
    _ ≤ 71 / 50 := hs

end Poincare11a
