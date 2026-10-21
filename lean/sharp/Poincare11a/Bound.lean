/-
The moment bound for one θ (paper Lemmas 3.1-3.3) in the variable `v = 4/cos²θ`, and its exact maximization over a
`v`-interval and a box of power sums (convex in `v`, affine in the power sums).
-/
import Poincare11a.Semigroup
import Poincare11a.Bernstein
import Poincare11a.Region
import Poincare11a.Prims

namespace Poincare11a

open Finset Poincare11a.Cert

variable {n : ℕ}

/-! ### Expectation lemmas -/

lemma Ex_mono (prob : Bool → ℝ) (hp : ∀ b, 0 ≤ prob b) {F G : Cube n → ℝ} (h : ∀ z, F z ≤ G z) :
    Ex prob F ≤ Ex prob G := by
  unfold Ex
  exact Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h z)
    (Finset.prod_nonneg (fun j _ => hp (z j))))

/-! ### The law of `δ` (paper Lemma 3.1 in the variable `v = 4/c²`) -/

section DeltaLaw

variable {m c : ℝ} (hc : 0 < c) (hcm : c ^ 2 = 1 - m ^ 2)
include hc hcm

lemma mom_dl_0 : mom (wt m) (dl m c) 0 = 1 := by simp [mom, wt]; ring

lemma mom_dl_1 : mom (wt m) (dl m c) 1 = 0 := by
  simp only [mom, wt, dl, pow_one, ite_true, Bool.false_eq_true, ite_false]
  field_simp; ring

lemma mom_dl_2 : mom (wt m) (dl m c) 2 = 1 := by
  simp only [mom, wt, dl, ite_true, Bool.false_eq_true, ite_false]
  have hc0 : c ≠ 0 := hc.ne'
  calc (1 + m) / 2 * ((1 - m) / c) ^ 2 + (1 - m) / 2 * (-(1 + m) / c) ^ 2 = (1 - m ^ 2) / c ^ 2 := by
        field_simp; ring
    _ = 1 := by rw [← hcm]; field_simp

lemma mom_dl_3_sq : mom (wt m) (dl m c) 3 ^ 2 = 4 / c ^ 2 - 4 := by
  simp only [mom, wt, dl, ite_true, Bool.false_eq_true, ite_false]
  have hc0 : c ≠ 0 := hc.ne'
  have h3 : (1 + m) / 2 * ((1 - m) / c) ^ 3 + (1 - m) / 2 * (-(1 + m) / c) ^ 3 = -2 * m / c := by
    calc (1 + m) / 2 * ((1 - m) / c) ^ 3 + (1 - m) / 2 * (-(1 + m) / c) ^ 3
        = (1 - m ^ 2) * (-4 * m) / (2 * c ^ 3) := by field_simp; ring
      _ = c ^ 2 * (-4 * m) / (2 * c ^ 3) := by rw [hcm]
      _ = -2 * m / c := by field_simp; ring
  rw [h3]
  calc (-2 * m / c) ^ 2 = 4 * m ^ 2 / c ^ 2 := by ring
    _ = 4 * (1 - c ^ 2) / c ^ 2 := by rw [show m ^ 2 = 1 - c ^ 2 by linarith]
    _ = 4 / c ^ 2 - 4 := by field_simp

lemma mom_dl_4 : mom (wt m) (dl m c) 4 = 4 / c ^ 2 - 3 := by
  simp only [mom, wt, dl, ite_true, Bool.false_eq_true, ite_false]
  have hc0 : c ≠ 0 := hc.ne'
  calc (1 + m) / 2 * ((1 - m) / c) ^ 4 + (1 - m) / 2 * (-(1 + m) / c) ^ 4
      = (1 - m ^ 2) * (1 + 3 * m ^ 2) / c ^ 4 := by field_simp; ring
    _ = c ^ 2 * (4 - 3 * c ^ 2) / c ^ 4 := by rw [← hcm, show 1 + 3 * m ^ 2 = 4 - 3 * c ^ 2 by linarith]
    _ = 4 / c ^ 2 - 3 := by field_simp

lemma mom_dl_6 : mom (wt m) (dl m c) 6 = (4 / c ^ 2) ^ 2 - 5 * (4 / c ^ 2) + 5 := by
  simp only [mom, wt, dl, ite_true, Bool.false_eq_true, ite_false]
  have hc0 : c ≠ 0 := hc.ne'
  have hm2 : m ^ 2 = 1 - c ^ 2 := by linarith
  calc (1 + m) / 2 * ((1 - m) / c) ^ 6 + (1 - m) / 2 * (-(1 + m) / c) ^ 6
      = (1 - m ^ 2) * (1 + 10 * m ^ 2 + 5 * (m ^ 2) ^ 2) / c ^ 6 := by field_simp; ring
    _ = c ^ 2 * (16 - 20 * c ^ 2 + 5 * c ^ 4) / c ^ 6 := by rw [← hcm, hm2]; ring
    _ = (4 / c ^ 2) ^ 2 - 5 * (4 / c ^ 2) + 5 := by field_simp; ring

end DeltaLaw

/-! ### The bound for one θ -/

/-- The bound `E(v, P4, P3², P6) = a + b + c m4 + d m6` of Lemmas 3.2-3.3 for the polynomial `p`. -/
noncomputable def Ereal (p : Poly) (v x4 x3 x6 : ℝ) : ℝ :=
  ((p.A + p.B + 3 * p.C + 15 * p.D : ℝ) + (p.C + 15 * p.D) * (v - 6) * x4 + 10 * p.D * (v - 4) * x3 +
    p.D * (v ^ 2 - 30 * v + 120) * x6) / (DLIB : ℝ)

lemma wt_nonneg_of {m c : ℝ} (_hc : 0 < c) (hcm : c ^ 2 = 1 - m ^ 2) (b : Bool) : 0 ≤ wt m b := by
  have h1 : m ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
  have : -1 ≤ m ∧ m ≤ 1 := ⟨by nlinarith [sq_nonneg (m + 1)], by nlinarith [sq_nonneg (m - 1)]⟩
  exact wt_nonneg this.1 this.2 b

/-- `E|S| ≤ 1` for a unit vector (from `|S| ≤ (1 + S²)/2` and `E S² = 1`). -/
theorem Phi_le_one {m c : ℝ} (hc : 0 < c) (hcm : c ^ 2 = 1 - m ^ 2) (lam : Fin n → ℝ)
    (hl : psum lam 2 = 1) : Phi m c lam ≤ 1 := by
  have hmom := moments_hold (wt m) (dl m c) (mom_dl_0 hc hcm) (mom_dl_1 hc hcm) (mom_dl_2 hc hcm) lam
  obtain ⟨e0, -, e2, -⟩ := hmom
  have h : ∀ z, |Ssum (dl m c) lam z| ≤ (1 / 2) * Ssum (dl m c) lam z ^ 0 + (1 / 2) * Ssum (dl m c) lam z ^ 2 :=
    fun z => by
      have := sq_nonneg (|Ssum (dl m c) lam z| - 1)
      rw [pow_zero, ← sq_abs (Ssum (dl m c) lam z)]; nlinarith
  calc Phi m c lam ≤ Ex (wt m) (fun z => (1 / 2) * Ssum (dl m c) lam z ^ 0 + (1 / 2) * Ssum (dl m c) lam z ^ 2) :=
        Ex_mono _ (wt_nonneg_of hc hcm) h
    _ = 1 := by
        rw [Ex_add, Ex_smul, Ex_smul]
        simp only at e0 e2
        rw [e0, e2, hl]; norm_num

/-- `E|S| ≤ E(v, P4, P3², P6)` for a unit vector and a polynomial that passes `posOK`, with `v = 4/c²`. -/
theorem Phi_le_Ereal {m c : ℝ} (hc : 0 < c) (hcm : c ^ 2 = 1 - m ^ 2) (lam : Fin n → ℝ)
    (hl : psum lam 2 = 1) (p : Poly) (hp : p.posOK = true) :
    Phi m c lam ≤ Ereal p (4 / c ^ 2) (psum lam 4) (psum lam 3 ^ 2) (psum lam 6) := by
  have hmom := moments_hold (wt m) (dl m c) (mom_dl_0 hc hcm) (mom_dl_1 hc hcm) (mom_dl_2 hc hcm) lam
  obtain ⟨e0, -, e2, -, e4, -, e6⟩ := hmom
  simp only at e0 e2 e4 e6
  have h : ∀ z, |Ssum (dl m c) lam z| ≤
      ((p.A : ℝ) / DLIB) * Ssum (dl m c) lam z ^ 0 + ((p.B : ℝ) / DLIB) * Ssum (dl m c) lam z ^ 2 +
        ((p.C : ℝ) / DLIB) * Ssum (dl m c) lam z ^ 4 + ((p.D : ℝ) / DLIB) * Ssum (dl m c) lam z ^ 6 := by
    intro z
    have := p.abs_le_h hp (Ssum (dl m c) lam z)
    rw [Poly.h] at this
    rw [pow_zero]
    calc |Ssum (dl m c) lam z| ≤ _ := this
      _ = _ := by ring
  calc Phi m c lam ≤ Ex (wt m) (fun z => ((p.A : ℝ) / DLIB) * Ssum (dl m c) lam z ^ 0 +
        ((p.B : ℝ) / DLIB) * Ssum (dl m c) lam z ^ 2 + ((p.C : ℝ) / DLIB) * Ssum (dl m c) lam z ^ 4 +
        ((p.D : ℝ) / DLIB) * Ssum (dl m c) lam z ^ 6) := Ex_mono _ (wt_nonneg_of hc hcm) h
    _ = Ereal p (4 / c ^ 2) (psum lam 4) (psum lam 3 ^ 2) (psum lam 6) := by
        rw [Ex_add, Ex_add, Ex_add, Ex_smul, Ex_smul, Ex_smul, Ex_smul, e0, e2, e4, e6, hl,
          mom_dl_4 hc hcm, mom_dl_6 hc hcm]
        have h3 := mom_dl_3_sq hc hcm
        rw [Ereal, h3]
        have := DLIB_pos
        field_simp
        ring

/-! ### Exact maximization over the v-interval (convexity) and the box (vertices) -/

/-- `E` is convex in `v` when `D ≥ 0` and `P6 ≥ 0`: its maximum over `[vl, vh]` is at an endpoint. -/
lemma Ereal_le_max (p : Poly) (hD : 0 ≤ (p.D : ℝ)) {vl v vh x4 x3 x6 : ℝ} (h1 : vl ≤ v) (h2 : v ≤ vh)
    (hx6 : 0 ≤ x6) :
    Ereal p v x4 x3 x6 ≤ max (Ereal p vl x4 x3 x6) (Ereal p vh x4 x3 x6) := by
  rcases eq_or_lt_of_le (h1.trans h2) with he | hlt
  · have : v = vl := le_antisymm (he ▸ h2) h1
    rw [this]; exact le_max_left _ _
  have key : (vh - vl) * Ereal p v x4 x3 x6 =
      (vh - v) * Ereal p vl x4 x3 x6 + (v - vl) * Ereal p vh x4 x3 x6 -
        (p.D : ℝ) * x6 / DLIB * ((vh - v) * (v - vl) * (vh - vl)) := by
    unfold Ereal; have := DLIB_pos; field_simp; ring
  have hγ : 0 ≤ (p.D : ℝ) * x6 / DLIB * ((vh - v) * (v - vl) * (vh - vl)) := by
    have := DLIB_pos
    apply mul_nonneg (div_nonneg (mul_nonneg hD hx6) this.le)
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  set M := max (Ereal p vl x4 x3 x6) (Ereal p vh x4 x3 x6)
  have hl : Ereal p vl x4 x3 x6 ≤ M := le_max_left _ _
  have hh : Ereal p vh x4 x3 x6 ≤ M := le_max_right _ _
  have : (vh - vl) * Ereal p v x4 x3 x6 ≤ (vh - vl) * M := by
    rw [key]; nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ vh - v),
      mul_le_mul_of_nonneg_left hh (by linarith : (0 : ℝ) ≤ v - vl)]
  exact le_of_mul_le_mul_left this (by linarith)

/-- Bound of `w · x` over `x ∈ [lo, hi]` by `sel`. -/
lemma mul_le_sel (w lo hi : Int) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    (w : ℝ) * x ≤ (sel w lo hi : ℝ) := by
  unfold sel
  rcases w with w | w
  · have h0 : (0 : ℝ) ≤ ((Int.ofNat w : ℤ) : ℝ) := by rw [Int.ofNat_eq_natCast]; positivity
    rw [Int.cast_mul]; exact mul_le_mul_of_nonneg_left hhi h0
  · have h0 : ((Int.negSucc w : ℤ) : ℝ) < 0 := by exact_mod_cast Int.negSucc_lt_zero w
    rw [Int.cast_mul]; exact mul_le_mul_of_nonpos_left hlo h0.le

/-- The scaled bound at one end of the `v`-range dominates the true bound over the box. -/
theorem Ereal_le_evalE (p : Poly) (S0 S1 T0 T1 V : Int) (x4 x3 x6 : ℝ)
    (h4 : (S0 : ℝ) ≤ (P60 : ℝ) * x4 ∧ (P60 : ℝ) * x4 ≤ S1) (h3 : 0 ≤ x3 ∧ (P60 : ℝ) * x3 ≤ S1)
    (h6 : (T0 : ℝ) ≤ (P60 : ℝ) * x6 ∧ (P60 : ℝ) * x6 ≤ T1) :
    Ereal p ((V : ℝ) / VSC) x4 x3 x6 * ONE ≤
      (evalE (mkRunC p S0 S1 T0 T1) ((V - 6 * VSC) * VSC) ((V - 4 * VSC) * VSC)
        (V * V - 30 * VSC * V + 120 * VSC * VSC) : ℝ) := by
  have hONE : (ONE : ℝ) = DLIB * VSC * VSC * P60 := by exact_mod_cast ONE_eq
  have hK : (K0SC : ℝ) = VSC * VSC * P60 := by exact_mod_cast K0SC_eq
  have hV : (0 : ℝ) < VSC := by norm_num [VSC]
  have hD := DLIB_pos
  set X4 := (P60 : ℝ) * x4
  set X3 := (P60 : ℝ) * x3
  set X6 := (P60 : ℝ) * x6
  have key : Ereal p ((V : ℝ) / VSC) x4 x3 x6 * ONE =
      ((p.A + p.B + 3 * p.C + 15 * p.D) * K0SC : Int) +
        (((V - 6 * VSC) * VSC : Int) : ℝ) * ((p.C + 15 * p.D : Int) * X4) +
        (((V - 4 * VSC) * VSC : Int) : ℝ) * ((10 * p.D : Int) * X3) +
        ((V * V - 30 * VSC * V + 120 * VSC * VSC : Int) : ℝ) * ((p.D : Int) * X6) := by
    rw [hONE, Ereal]; push_cast; rw [hK]; field_simp; ring
  rw [key]
  simp only [evalE, mkRunC, imin_eq, imax_eq]
  push_cast
  have e4 := mul_le_sel ((V - 6 * VSC) * VSC) (min ((p.C + 15 * p.D) * S0) ((p.C + 15 * p.D) * S1))
    (max ((p.C + 15 * p.D) * S0) ((p.C + 15 * p.D) * S1)) ((p.C + 15 * p.D : Int) * X4) ?_ ?_
  rotate_left
  · push_cast
    rcases le_total (0 : ℝ) ((p.C : ℝ) + 15 * p.D) with he | he
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h4.1 he)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h4.2 he)
  · push_cast
    rcases le_total (0 : ℝ) ((p.C : ℝ) + 15 * p.D) with he | he
    · exact (mul_le_mul_of_nonneg_left h4.2 he).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left h4.1 he).trans (le_max_left _ _)
  have hX3 : 0 ≤ X3 := mul_nonneg (by norm_num [P60]) h3.1
  have e3 := mul_le_sel ((V - 4 * VSC) * VSC) (min 0 (10 * p.D * S1)) (max 0 (10 * p.D * S1))
    ((10 * p.D : Int) * X3) ?_ ?_
  rotate_left
  · push_cast
    rcases le_total (0 : ℝ) (10 * (p.D : ℝ)) with he | he
    · exact (min_le_left _ _).trans (mul_nonneg he hX3)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h3.2 he)
  · push_cast
    rcases le_total (0 : ℝ) (10 * (p.D : ℝ)) with he | he
    · exact (mul_le_mul_of_nonneg_left h3.2 he).trans (le_max_right _ _)
    · exact (mul_nonpos_of_nonpos_of_nonneg he hX3).trans (le_max_left _ _)
  have e6 := mul_le_sel (V * V - 30 * VSC * V + 120 * VSC * VSC) (min (p.D * T0) (p.D * T1))
    (max (p.D * T0) (p.D * T1)) ((p.D : Int) * X6) ?_ ?_
  rotate_left
  · push_cast
    rcases le_total (0 : ℝ) (p.D : ℝ) with he | he
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h6.1 he)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h6.2 he)
  · push_cast
    rcases le_total (0 : ℝ) (p.D : ℝ) with he | he
    · exact (mul_le_mul_of_nonneg_left h6.2 he).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left h6.1 he).trans (le_max_left _ _)
  push_cast at e4 e3 e6
  linarith

end Poincare11a
