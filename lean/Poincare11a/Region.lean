/-
The power sums of a unit vector lie in the region of paper Lemma 3.4:
`P4² ≤ P6`, `P6² ≤ P4³` (i.e. `P6 ≤ P4^{3/2}`), `P3² ≤ P4`, `0 ≤ P4 ≤ 1`.
-/
import Poincare11a.Moments

namespace Poincare11a

open Finset

variable {n : ℕ}

lemma psum_even_nonneg (a : Fin n → ℝ) (k : ℕ) : 0 ≤ psum a (2 * k) := by
  unfold psum
  exact Finset.sum_nonneg (fun j _ => by rw [pow_mul]; positivity)

lemma psum4_sq_le (a : Fin n → ℝ) : psum a 4 ^ 2 ≤ psum a 2 * psum a 6 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun j => a j ^ 3)
  simp only [psum]
  calc (∑ j, a j ^ 4) ^ 2 = (∑ j, a j * a j ^ 3) ^ 2 := by
        congr 1; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ (∑ j, a j ^ 2) * ∑ j, (a j ^ 3) ^ 2 := h
    _ = (∑ j, a j ^ 2) * ∑ j, a j ^ 6 := by
        congr 1; exact Finset.sum_congr rfl (fun j _ => by ring)

lemma psum3_sq_le (a : Fin n → ℝ) : psum a 3 ^ 2 ≤ psum a 2 * psum a 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun j => a j ^ 2)
  simp only [psum]
  calc (∑ j, a j ^ 3) ^ 2 = (∑ j, a j * a j ^ 2) ^ 2 := by
        congr 1; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ (∑ j, a j ^ 2) * ∑ j, (a j ^ 2) ^ 2 := h
    _ = (∑ j, a j ^ 2) * ∑ j, a j ^ 4 := by
        congr 1; exact Finset.sum_congr rfl (fun j _ => by ring)

lemma psum6_sq_le (a : Fin n → ℝ) : psum a 6 ^ 2 ≤ psum a 4 ^ 3 := by
  have h4 : 0 ≤ psum a 4 := psum_even_nonneg a 2
  have h6 : 0 ≤ psum a 6 := psum_even_nonneg a 3
  set r := Real.sqrt (psum a 4)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r ^ 2 = psum a 4 := Real.sq_sqrt h4
  have hj : ∀ j, a j ^ 2 ≤ r := fun j => by
    apply Real.le_sqrt_of_sq_le
    have : a j ^ 4 ≤ psum a 4 := by
      unfold psum
      exact Finset.single_le_sum (f := fun j => a j ^ 4) (fun i _ => by positivity) (Finset.mem_univ j)
    calc (a j ^ 2) ^ 2 = a j ^ 4 := by ring
      _ ≤ psum a 4 := this
  have hle : psum a 6 ≤ r * psum a 4 := by
    unfold psum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => by
      have := hj j
      have h4j : 0 ≤ a j ^ 4 := by positivity
      calc a j ^ 6 = a j ^ 2 * a j ^ 4 := by ring
        _ ≤ r * a j ^ 4 := mul_le_mul_of_nonneg_right this h4j)
  calc psum a 6 ^ 2 ≤ (r * psum a 4) ^ 2 := pow_le_pow_left₀ h6 hle 2
    _ = r ^ 2 * psum a 4 ^ 2 := by ring
    _ = psum a 4 ^ 3 := by rw [hrr]; ring

lemma psum4_le_one (a : Fin n → ℝ) (h : psum a 2 = 1) : psum a 4 ≤ 1 := by
  have hj : ∀ j, a j ^ 2 ≤ 1 := fun j => by
    rw [← h]; unfold psum
    exact Finset.single_le_sum (f := fun j => a j ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)
  calc psum a 4 = ∑ j, a j ^ 2 * a j ^ 2 := by
        unfold psum; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, 1 * a j ^ 2 := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hj j) (by positivity))
    _ = 1 := by simp only [one_mul]; exact h

end Poincare11a
