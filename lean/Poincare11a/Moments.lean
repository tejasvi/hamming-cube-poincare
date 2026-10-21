/-
Moments of `S = ∑_j a_j X_j` for independent copies `X_j` of a two-point law with mean 0 and variance 1
(paper Lemma 3.2, for a general vector `a`, not necessarily of unit length).
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

namespace Poincare11a

open Finset

section Moments

variable (prob val : Bool → ℝ)

/-- Expectation over the product law on `{true, false}^n` with marginal `prob`. -/
noncomputable def Ex {n : ℕ} (F : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ z : Fin n → Bool, (∏ j, prob (z j)) * F z

/-- `S(z) = ∑_j a_j val(z_j)`. -/
noncomputable def Ssum {n : ℕ} (a : Fin n → ℝ) (z : Fin n → Bool) : ℝ := ∑ j, a j * val (z j)

/-- The `r`-th moment of the two-point law. -/
noncomputable def mom (r : ℕ) : ℝ := prob true * val true ^ r + prob false * val false ^ r

/-- Power sum `P_k = ∑_j a_j^k`. -/
noncomputable def psum {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ := ∑ j, a j ^ k

lemma sum_cube_succ {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ z, F z = ∑ b : Bool, ∑ w : Fin n → Bool, F (Fin.cons b w) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma Ex_succ {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    Ex prob F = ∑ b : Bool, prob b * Ex prob (fun w : Fin n → Bool => F (Fin.cons b w)) := by
  simp only [Ex]
  rw [sum_cube_succ]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

lemma Ssum_cons {n : ℕ} (a : Fin (n + 1) → ℝ) (b : Bool) (w : Fin n → Bool) :
    Ssum val a (Fin.cons b w) = a 0 * val b + Ssum val (fun j => a j.succ) w := by
  simp only [Ssum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma Ex_add {n : ℕ} (F G : (Fin n → Bool) → ℝ) :
    Ex prob (fun z => F z + G z) = Ex prob F + Ex prob G := by
  simp only [Ex, mul_add, Finset.sum_add_distrib]

lemma Ex_smul {n : ℕ} (c : ℝ) (F : (Fin n → Bool) → ℝ) :
    Ex prob (fun z => c * F z) = c * Ex prob F := by
  simp only [Ex, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  ring

lemma Ex_const {n : ℕ} (hp : prob true + prob false = 1) (c : ℝ) :
    Ex prob (fun _ : Fin n → Bool => c) = c := by
  induction n with
  | zero => simp [Ex]
  | succ n ih =>
    rw [Ex_succ]
    simp only [Fintype.sum_bool, ih]
    linear_combination c * hp

/-- Binomial expansion of one step of the induction. -/
lemma Ex_pow_succ {n : ℕ} (a : Fin (n + 1) → ℝ) (r : ℕ) :
    Ex prob (fun z => Ssum val a z ^ r) =
      ∑ i ∈ range (r + 1), (r.choose i : ℝ) * a 0 ^ i * mom prob val i *
        Ex prob (fun w => Ssum val (fun j => a j.succ) w ^ (r - i)) := by
  rw [Ex_succ]
  simp only [Ssum_cons, add_pow]
  have key : ∀ b : Bool, Ex prob (fun w : Fin n → Bool => ∑ i ∈ range (r + 1),
      (a 0 * val b) ^ i * Ssum val (fun j => a j.succ) w ^ (r - i) * (r.choose i : ℝ)) =
      ∑ i ∈ range (r + 1), (a 0 * val b) ^ i * (r.choose i : ℝ) *
        Ex prob (fun w => Ssum val (fun j => a j.succ) w ^ (r - i)) := by
    intro b
    simp only [Ex, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun w _ => ?_))
    ring
  simp only [key, Fintype.sum_bool, Finset.mul_sum, ← Finset.sum_add_distrib, mom]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The moment identities of order 0..6 (cumulant expansion), for a law with mean 0 and variance 1. -/
def MomentsHold {n : ℕ} (a : Fin n → ℝ) : Prop :=
  let E := fun r => Ex prob (fun z => Ssum val a z ^ r)
  let P := psum a
  let m := mom prob val
  E 0 = 1 ∧ E 1 = 0 ∧ E 2 = P 2 ∧ E 3 = m 3 * P 3 ∧
  E 4 = 3 * P 2 ^ 2 + (m 4 - 3) * P 4 ∧
  E 5 = 10 * m 3 * P 2 * P 3 + (m 5 - 10 * m 3) * P 5 ∧
  E 6 = 15 * P 2 ^ 3 + 15 * (m 4 - 3) * P 2 * P 4 + 10 * m 3 ^ 2 * P 3 ^ 2 +
    (m 6 - 15 * m 4 - 10 * m 3 ^ 2 + 30) * P 6

theorem moments_hold (h0 : mom prob val 0 = 1) (h1 : mom prob val 1 = 0) (h2 : mom prob val 2 = 1) :
    ∀ {n : ℕ} (a : Fin n → ℝ), MomentsHold prob val a := by
  intro n
  induction n with
  | zero =>
    intro a
    have hp : prob true + prob false = 1 := by simpa [mom] using h0
    simp only [MomentsHold, psum, Finset.univ_eq_empty, Finset.sum_empty]
    have hS : ∀ z : Fin 0 → Bool, Ssum val a z = 0 := fun z => by simp [Ssum]
    simp only [hS]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Ex]
  | succ n ih =>
    intro a
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := ih (fun j => a j.succ)
    simp only [MomentsHold] at *
    have hP : ∀ k, psum a k = a 0 ^ k + psum (fun j => a j.succ) k := fun k => by
      simp [psum, Fin.sum_univ_succ]
    simp only [hP]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      rw [Ex_pow_succ]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.sub_self,
        Nat.succ_sub_succ_eq_sub, Nat.sub_zero, e0, e1, e2, e3, e4, e5, e6, h0, h1, h2]
      norm_num
      try ring

end Moments

end Poincare11a
