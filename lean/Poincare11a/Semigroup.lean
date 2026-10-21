/-
The heat semigroup of the cube in the variable `m = e^{-t} = sin θ` (paper Lemma 2.1 and the first part of the proof of
Theorem 2.2): `P(m, x) = ∑_z ∏_j w(m, z_j) f(x ⊙ z)` with `w(m, true) = (1+m)/2`, `w(m, false) = (1-m)/2`.
-/
import Poincare11a.Defs
import Poincare11a.Moments
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace Poincare11a

open Finset

variable {n : ℕ}

/-- Coordinatewise product on `{-1,1}^n` (`true` ↦ +1): `(x ⊙ z)_j = x_j z_j`. -/
def cmul (x z : Cube n) : Cube n := fun j => (x j == z j)

lemma cmul_cmul (x z : Cube n) : cmul (cmul x z) z = x := by
  funext j; simp only [cmul]; cases x j <;> cases z j <;> rfl

lemma cmul_comm (x z : Cube n) : cmul x z = cmul z x := by
  funext j; simp only [cmul]; cases x j <;> cases z j <;> rfl

lemma cmul_true (x : Cube n) : cmul x (fun _ => true) = x := by
  funext j; simp only [cmul]; cases x j <;> rfl

/-- For fixed `z`, `x ↦ x ⊙ z` is a bijection of the cube. -/
def cmulEquiv (z : Cube n) : Cube n ≃ Cube n where
  toFun x := cmul x z
  invFun x := cmul x z
  left_inv x := cmul_cmul x z
  right_inv x := cmul_cmul x z

lemma flip_apply_self (j : Fin n) (x : Cube n) : flip j x j = !x j := by simp [flip]

lemma flip_apply_ne {i j : Fin n} (h : i ≠ j) (x : Cube n) : flip j x i = x i := by
  simp [flip, Function.update_of_ne h]

lemma flip_flip (j : Fin n) (x : Cube n) : flip j (flip j x) = x := by
  funext i
  by_cases h : i = j
  · subst h; simp [flip_apply_self]
  · simp [flip_apply_ne h]

/-- `flip j` as an involutive bijection. -/
def flipEquiv (j : Fin n) : Cube n ≃ Cube n where
  toFun := flip j
  invFun := flip j
  left_inv := flip_flip j
  right_inv := flip_flip j

lemma cmul_flip (x z : Cube n) (k : Fin n) : cmul x (flip k z) = flip k (cmul x z) := by
  funext i
  by_cases h : i = k
  · subst h; simp only [cmul, flip_apply_self]; cases x i <;> cases z i <;> rfl
  · simp only [cmul, flip_apply_ne h]

/-- One-coordinate weight `w(m, b)`. -/
noncomputable def wt (m : ℝ) (b : Bool) : ℝ := if b then (1 + m) / 2 else (1 - m) / 2

/-- Sign `σ(b) = ±1`. -/
noncomputable def sg (b : Bool) : ℝ := if b then 1 else -1

/-- Product weight `W(m, z) = ∏_j w(m, z_j)`. -/
noncomputable def W (m : ℝ) (z : Cube n) : ℝ := ∏ j, wt m (z j)

/-- Product weight without coordinate `k`. -/
noncomputable def Wk (m : ℝ) (k : Fin n) (z : Cube n) : ℝ := ∏ j ∈ univ.erase k, wt m (z j)

/-- The semigroup `P(m, x) = ∑_z W(m, z) f(x ⊙ z)`. -/
noncomputable def Psg (f : Cube n → ℝ) (m : ℝ) (x : Cube n) : ℝ := ∑ z, W m z * f (cmul x z)

lemma wt_nonneg {m : ℝ} (h1 : -1 ≤ m) (h2 : m ≤ 1) (b : Bool) : 0 ≤ wt m b := by
  unfold wt; split_ifs <;> linarith

lemma W_nonneg {m : ℝ} (h1 : -1 ≤ m) (h2 : m ≤ 1) (z : Cube n) : 0 ≤ W m z :=
  Finset.prod_nonneg (fun j _ => wt_nonneg h1 h2 (z j))

lemma W_eq_wt_mul_Wk (m : ℝ) (k : Fin n) (z : Cube n) : W m z = wt m (z k) * Wk m k z :=
  (Finset.mul_prod_erase univ (fun j => wt m (z j)) (Finset.mem_univ k)).symm

lemma Wk_flip (m : ℝ) (k : Fin n) (z : Cube n) : Wk m k (flip k z) = Wk m k z := by
  unfold Wk
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [flip_apply_ne (Finset.ne_of_mem_erase hj)]

lemma Psg_one (f : Cube n → ℝ) (x : Cube n) : Psg f 1 x = f x := by
  unfold Psg
  rw [Finset.sum_eq_single (fun _ => true)]
  · simp [W, wt, cmul_true]
  · intro z _ hz
    obtain ⟨j, hj⟩ : ∃ j, z j = false := by
      by_contra h; push Not at h; exact hz (funext fun j => by simpa using h j)
    have : W 1 z = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [wt, hj])
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma Psg_zero (f : Cube n → ℝ) (x : Cube n) : Psg f 0 x = avg f := by
  unfold Psg avg
  have hW : ∀ z : Cube n, W 0 z = (1 / 2) ^ n := fun z => by
    simp only [W, wt]
    rw [Finset.prod_congr rfl (g := fun _ => (1 : ℝ) / 2) (fun j _ => by split_ifs <;> norm_num)]
    simp
  simp only [hW, ← Finset.mul_sum]
  have : ∑ z, f (cmul x z) = ∑ y, f y := by
    simp_rw [cmul_comm x]
    exact Equiv.sum_comp (cmulEquiv x) f
  rw [this, one_div, inv_pow, div_eq_inv_mul]

/-- Derivative of the product weight in `m`. -/
lemma hasDerivAt_W (m : ℝ) (z : Cube n) :
    HasDerivAt (fun m => W m z) (∑ k, Wk m k z * (sg (z k) / 2)) m := by
  unfold W Wk
  have h : ∀ j ∈ (univ : Finset (Fin n)), HasDerivAt (fun m => wt m (z j)) (sg (z j) / 2) m := by
    intro j _
    unfold wt sg
    cases z j
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ((hasDerivAt_id m).const_sub 1).div_const 2 |>.congr_deriv (by ring)
    · simp only [↓reduceIte]
      exact ((hasDerivAt_id m).const_add 1).div_const 2 |>.congr_deriv (by ring)
  have := HasDerivAt.fun_finsetProd (u := univ) (x := m) h
  simpa [smul_eq_mul] using this

/-- `dW/dm` summed against `f(x ⊙ z)`. -/
noncomputable def dPsg (f : Cube n → ℝ) (m : ℝ) (x : Cube n) : ℝ :=
  ∑ z, (∑ k, Wk m k z * (sg (z k) / 2)) * f (cmul x z)

lemma hasDerivAt_Psg_sin (f : Cube n → ℝ) (x : Cube n) (θ : ℝ) :
    HasDerivAt (fun θ => Psg f (Real.sin θ) x) (Real.cos θ * dPsg f (Real.sin θ) x) θ := by
  unfold Psg dPsg
  rw [Finset.mul_sum]
  apply HasDerivAt.fun_sum
  intro z _
  have h1 := (hasDerivAt_W (Real.sin θ) z).comp θ (Real.hasDerivAt_sin θ)
  exact (h1.mul_const (f (cmul x z))).congr_deriv (by ring)

/-- Flip pairing (the step `f(x ζ^{j,+}) - f(x ζ^{j,-}) = 2 ζ_j D_j f(x ζ)` of Lemma 2.1). -/
lemma pairing (f : Cube n → ℝ) (m : ℝ) (x : Cube n) (k : Fin n) :
    ∑ z, sg (z k) * Wk m k z * f (cmul x z) = ∑ z, Wk m k z * sg (z k) * D f k (cmul x z) := by
  have hre : ∑ z, Wk m k z * sg (z k) * f (flip k (cmul x z)) = -∑ z, sg (z k) * Wk m k z * f (cmul x z) := by
    rw [← Equiv.sum_comp (flipEquiv k)]
    simp only [flipEquiv, Equiv.coe_fn_mk]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Wk_flip, flip_apply_self, ← cmul_flip, flip_flip]
    cases z k <;> simp [sg]
  have : ∑ z, Wk m k z * sg (z k) * D f k (cmul x z) =
      (∑ z, sg (z k) * Wk m k z * f (cmul x z) - ∑ z, Wk m k z * sg (z k) * f (flip k (cmul x z))) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    unfold D; ring
  rw [this, hre]; ring

/-- The biased standardized sign in the `δ`-form: `δ(true) = (1-m)/c`, `δ(false) = -(1+m)/c`, `c = cos θ`. -/
noncomputable def dl (m c : ℝ) (b : Bool) : ℝ := if b then (1 - m) / c else -(1 + m) / c

lemma wt_mul_dl {m c : ℝ} (hc : c ≠ 0) (hcm : c ^ 2 = 1 - m ^ 2) (b : Bool) :
    wt m b * dl m c b = sg b * (c / 2) := by
  unfold wt dl sg
  cases b <;> simp <;> field_simp <;> nlinarith [hcm]

/-- `cos θ · dP/dm = E_ζ ∑_k δ_k D_k f(x ⊙ ζ)` (the derivative identity of Lemma 2.1, `θ`-form). -/
lemma dPsg_eq {m c : ℝ} (hc : c ≠ 0) (hcm : c ^ 2 = 1 - m ^ 2) (f : Cube n → ℝ) (x : Cube n) :
    c * dPsg f m x = ∑ z, W m z * ∑ k, dl m c (z k) * D f k (cmul x z) := by
  unfold dPsg
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hp := pairing f m x k
  have lhs : ∑ z, c * (Wk m k z * (sg (z k) / 2) * f (cmul x z)) =
      (c / 2) * ∑ z, sg (z k) * Wk m k z * f (cmul x z) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun z _ => by ring)
  have rhs : ∑ z, W m z * (dl m c (z k) * D f k (cmul x z)) =
      (c / 2) * ∑ z, Wk m k z * sg (z k) * D f k (cmul x z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [W_eq_wt_mul_Wk m k z]
    have := wt_mul_dl hc hcm (z k)
    calc wt m (z k) * Wk m k z * (dl m c (z k) * D f k (cmul x z))
        = (wt m (z k) * dl m c (z k)) * Wk m k z * D f k (cmul x z) := by ring
      _ = c / 2 * (Wk m k z * sg (z k) * D f k (cmul x z)) := by rw [this]; ring
  rw [lhs, rhs, hp]

/-- `Φ(a, θ) = E|∑_k a_k δ_k|` in terms of `m = sin θ`, `c = cos θ`. -/
noncomputable def Phi (m c : ℝ) (a : Fin n → ℝ) : ℝ := Ex (wt m) (fun z => |Ssum (dl m c) a z|)

/-- The gradient vector `∇f(y) = (D_1 f(y), …, D_n f(y))`. -/
noncomputable def grad (f : Cube n → ℝ) (y : Cube n) : Fin n → ℝ := fun k => D f k y

/-- `∑_x |c · dP/dm| ≤ ∑_y Φ(∇f(y))` (triangle inequality and the bijection `x ↦ x ⊙ z`). -/
lemma sum_abs_dPsg_le {m c : ℝ} (hc : c ≠ 0) (hcm : c ^ 2 = 1 - m ^ 2) (hm1 : -1 ≤ m) (hm2 : m ≤ 1)
    (f : Cube n → ℝ) :
    ∑ x, |c * dPsg f m x| ≤ ∑ y, Phi m c (grad f y) := by
  have step1 : ∀ x, |c * dPsg f m x| ≤ ∑ z, W m z * |∑ k, dl m c (z k) * D f k (cmul x z)| := by
    intro x
    rw [dPsg_eq hc hcm]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [abs_mul, abs_of_nonneg (W_nonneg hm1 hm2 z)]
  refine (Finset.sum_le_sum (fun x _ => step1 x)).trans (le_of_eq ?_)
  calc ∑ x, ∑ z, W m z * |∑ k, dl m c (z k) * D f k (cmul x z)|
      = ∑ z, W m z * ∑ x, |∑ k, dl m c (z k) * D f k (cmul x z)| := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun z _ => (Finset.mul_sum _ _ _).symm)
    _ = ∑ z, W m z * ∑ y, |∑ k, dl m c (z k) * D f k y| := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        congr 1
        exact Equiv.sum_comp (cmulEquiv z) (fun y => |∑ k, dl m c (z k) * D f k y|)
    _ = ∑ y, ∑ z, W m z * |∑ k, D f k y * dl m c (z k)| := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
        congr 2
        exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    _ = ∑ y, Phi m c (grad f y) := by
        simp only [Phi, Ex, Ssum, grad, W]

end Poincare11a
