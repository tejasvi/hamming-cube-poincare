/- Specifications of the kernel-friendly integer primitives of the checker. -/
import Poincare11a.Checker
import Mathlib.Tactic

namespace Poincare11a.Cert

lemma ile_iff (a b : Int) : ile a b = true ↔ a ≤ b := by
  unfold ile
  rcases hd : b - a with k | k
  · simp only [Int.ofNat_eq_natCast] at hd; simp only [true_iff]; omega
  · simp only [Bool.false_eq_true, false_iff, not_le]; have := Int.negSucc_lt_zero k; omega

lemma ilt_iff (a b : Int) : ilt a b = true ↔ a < b := by
  unfold ilt
  rcases hd : a - b with k | k
  · simp only [Int.ofNat_eq_natCast] at hd; simp only [Bool.false_eq_true, false_iff, not_lt]; omega
  · simp only [true_iff]; have := Int.negSucc_lt_zero k; omega

lemma ipos_iff (a : Int) : ipos a = true ↔ 0 < a := by
  unfold ipos
  rcases a with (_ | k) | k
  · simp
  · simp only [true_iff, Int.ofNat_eq_natCast]; omega
  · simp only [Bool.false_eq_true, false_iff, not_lt]; have := Int.negSucc_lt_zero k; omega

lemma imax_eq (a b : Int) : imax a b = max a b := by
  unfold imax
  cases h : ile a b
  · have : ¬ a ≤ b := fun h' => by rw [(ile_iff a b).2 h'] at h; exact absurd h (by simp)
    simp only; omega
  · have := (ile_iff a b).1 h; simp only; omega

lemma imin_eq (a b : Int) : imin a b = min a b := by
  unfold imin
  cases h : ile a b
  · have : ¬ a ≤ b := fun h' => by rw [(ile_iff a b).2 h'] at h; exact absurd h (by simp)
    simp only; omega
  · have := (ile_iff a b).1 h; simp only; omega

end Poincare11a.Cert
