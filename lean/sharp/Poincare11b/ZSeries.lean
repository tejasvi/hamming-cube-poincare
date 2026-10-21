/-
Sequences on ℤ: Fourier series `∑ a_k e^{2πikq}`, discrete convolution, and the product formula.
-/
import Mathlib

namespace Poincare11b

open Complex Real Finset

/-- `ex k q = e^{2πikq}`. -/
noncomputable def ex (k : ℤ) (q : ℝ) : ℂ := Complex.exp (((2 * Real.pi * k * q : ℝ) : ℂ) * Complex.I)

lemma norm_ex (k : ℤ) (q : ℝ) : ‖ex k q‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma ex_add (k j : ℤ) (q : ℝ) : ex (k + j) q = ex k q * ex j q := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_zero (q : ℝ) : ex 0 q = 1 := by simp [ex]

lemma ex_im (k : ℤ) (q : ℝ) : (ex k q).im = Real.sin (2 * Real.pi * k * q) := by
  unfold ex; rw [Complex.exp_ofReal_mul_I_im]

/-- Fourier series of a real sequence on ℤ. -/
noncomputable def fser (a : ℤ → ℝ) (q : ℝ) : ℂ := ∑' k, (a k : ℂ) * ex k q

/-- Discrete convolution on ℤ. -/
noncomputable def conv (a b : ℤ → ℝ) (k : ℤ) : ℝ := ∑' j, a j * b (k - j)

/-- Shift: `(shiftZ m a) k = a (k - m)`. -/
def shiftZ (m : ℤ) (a : ℤ → ℝ) (k : ℤ) : ℝ := a (k - m)

/-- Nonnegative summable sequences. -/
def NS (a : ℤ → ℝ) : Prop := (∀ k, 0 ≤ a k) ∧ Summable a

lemma summable_norm_term {a : ℤ → ℝ} (ha : NS a) (q : ℝ) :
    Summable (fun k => ‖(a k : ℂ) * ex k q‖) := by
  refine ha.2.congr (fun k => ?_)
  rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_of_nonneg (ha.1 k)]

lemma summable_term {a : ℤ → ℝ} (ha : NS a) (q : ℝ) : Summable (fun k => (a k : ℂ) * ex k q) :=
  (summable_norm_term ha q).of_norm

/-- The reindexing `(k, j) ↦ (j, k - j)` of `ℤ × ℤ`. -/
def convEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

lemma summable_prod_conv {a b : ℤ → ℝ} (ha : NS a) (hb : NS b) :
    Summable (fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2)) := by
  have h := Summable.mul_of_nonneg ha.2 hb.2 (fun k => ha.1 k) (fun k => hb.1 k)
  exact (convEquiv.summable_iff.mpr h)

lemma NS_conv {a b : ℤ → ℝ} (ha : NS a) (hb : NS b) : NS (conv a b) := by
  refine ⟨fun k => tsum_nonneg (fun j => mul_nonneg (ha.1 j) (hb.1 _)), ?_⟩
  exact (summable_prod_conv ha hb).prod

lemma fser_mul {a b : ℤ → ℝ} (ha : NS a) (hb : NS b) (q : ℝ) :
    fser a q * fser b q = fser (conv a b) q := by
  unfold fser
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_term ha q) (summable_norm_term hb q)]
  set g : ℤ × ℤ → ℂ := fun z => (a z.1 : ℂ) * ex z.1 q * ((b z.2 : ℂ) * ex z.2 q) with hg
  have h1 : ∑' z, g z = ∑' p, g (convEquiv p) := (convEquiv.tsum_eq g).symm
  have h2 : (fun p => g (convEquiv p)) =
      fun p : ℤ × ℤ => ((a p.2 * b (p.1 - p.2) : ℝ) : ℂ) * ex p.1 q := by
    funext p
    simp only [hg, convEquiv, Equiv.coe_fn_mk]
    have : ex p.1 q = ex p.2 q * ex (p.1 - p.2) q := by rw [← ex_add]; congr 1; ring
    rw [this]; push_cast; ring
  have hs : Summable (fun p : ℤ × ℤ => ((a p.2 * b (p.1 - p.2) : ℝ) : ℂ) * ex p.1 q) := by
    refine Summable.of_norm ?_
    refine (summable_prod_conv ha hb).congr (fun p => ?_)
    rw [norm_mul, norm_ex, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (ha.1 _) (hb.1 _))]
  rw [h1, h2, hs.tsum_prod]
  congr 1; funext k
  dsimp only
  rw [tsum_mul_right, ← Complex.ofReal_tsum]
  rfl

lemma fser_shift (m : ℤ) (a : ℤ → ℝ) (q : ℝ) : ex m q * fser a q = fser (shiftZ m a) q := by
  unfold fser shiftZ
  rw [← tsum_mul_left]
  conv_rhs => rw [← (Equiv.addRight m).tsum_eq]
  congr 1; funext j
  simp only [Equiv.coe_addRight, add_sub_cancel_right, ex_add]
  ring

lemma NS_shift {a : ℤ → ℝ} (ha : NS a) (m : ℤ) : NS (shiftZ m a) :=
  ⟨fun _ => ha.1 _, (Equiv.subRight m).summable_iff.mpr ha.2⟩

lemma NS_add {a b : ℤ → ℝ} (ha : NS a) (hb : NS b) : NS (a + b) :=
  ⟨fun k => add_nonneg (ha.1 k) (hb.1 k), ha.2.add hb.2⟩

lemma NS_zero : NS 0 := ⟨fun _ => le_rfl, summable_zero⟩

lemma fser_add {a b : ℤ → ℝ} (ha : NS a) (hb : NS b) (q : ℝ) :
    fser (a + b) q = fser a q + fser b q := by
  unfold fser
  rw [← (summable_term ha q).tsum_add (summable_term hb q)]
  congr 1; funext k; simp only [Pi.add_apply]; push_cast; ring

lemma fser_zero (q : ℝ) : fser 0 q = 0 := by simp [fser]

/-- The delta sequence at 0. -/
def delta0 (k : ℤ) : ℝ := if k = 0 then 1 else 0

lemma fser_delta0 (q : ℝ) : fser delta0 q = 1 := by
  unfold fser delta0
  rw [tsum_eq_single 0 (fun _ hk => by simp [hk])]
  simp [ex_zero]

/-- Imaginary part of a Fourier series with nonnegative summable coefficients, as a sine series over `k ≥ 1`. -/
lemma im_fser_hasSum {p : ℤ → ℝ} (hp : NS p) (q : ℝ) :
    HasSum (fun k : ℕ => (p ((k : ℤ) + 1) - p (-((k : ℤ) + 1))) * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q))
      (fser p q).im := by
  have h0 : HasSum (fun k : ℤ => (p k : ℂ) * ex k q) (fser p q) := (summable_term hp q).hasSum
  have h1 : HasSum (fun k : ℤ => p k * Real.sin (2 * Real.pi * k * q)) (fser p q).im := by
    have := Complex.hasSum_im h0
    refine this.congr_fun (fun k => ?_)
    simp only [Complex.im_ofReal_mul, ex_im]
  have h2 := h1.nat_add_neg
  simp only [Int.cast_zero, mul_zero, zero_mul, Real.sin_zero, add_zero] at h2
  have h3 : HasSum (fun n : ℕ => (p n - p (-n)) * Real.sin (2 * Real.pi * n * q)) (fser p q).im := by
    refine h2.congr_fun (fun n => ?_)
    push_cast
    rw [show 2 * Real.pi * (-(n : ℝ)) * q = -(2 * Real.pi * n * q) by ring, Real.sin_neg]
    ring
  have h4 := (hasSum_nat_add_iff' 1).mpr h3
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, sub_self, zero_mul,
    sub_zero] at h4
  refine h4.congr_fun (fun k => ?_)
  push_cast; ring_nf

end Poincare11b
