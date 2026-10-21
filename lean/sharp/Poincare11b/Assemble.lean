/-
Assembly: the sharp bound `J(λ) ≤ √(π/2) |λ|` and the sharp L¹ Poincaré inequality from the named hypotheses
`HFreq`, `HB`, `HPFA`, `HG` of `Statements.lean`, and Theorem 2.2 (`Poincare11a.reduction`).
-/
import Poincare11b.Statements
import Poincare11a.Reduction
import Poincare11a.Constant

namespace Poincare11b

open Poincare11a MeasureTheory Set

variable {n : ℕ}

lemma vnorm_abs (lam : Fin n → ℝ) : vnorm (fun j => |lam j|) = vnorm lam := by
  simp [vnorm, sq_abs]

/-- `J(λ) ≤ √(π/2) |λ|` for every `λ`, from the four named hypotheses. -/
theorem J_le_of (hF : HFreq) (hB : HB) (hA : HPFA) (hG : HG) (lam : Fin n → ℝ) :
    J lam ≤ Real.sqrt (Real.pi / 2) * vnorm lam := by
  obtain ⟨hint, hJ⟩ := hF n lam
  obtain ⟨hint', hval⟩ := hG (vnorm lam) (Real.sqrt_nonneg _)
  have hmono : ∫ v in Ioi (0 : ℝ), Cfreq v lam / v ^ 2 ≤ ∫ v in Ioi (0 : ℝ), CG (v * vnorm lam) / v ^ 2 := by
    refine setIntegral_mono_on hint hint' measurableSet_Ioi (fun v hv => ?_)
    have h1 := hB n lam v hv
    have h2 := hA n (fun j => |lam j|) v (fun j => abs_nonneg _) hv
    rw [vnorm_abs] at h2
    exact div_le_div_of_nonneg_right (h1.trans h2) (sq_nonneg v)
  rw [hJ]
  calc 1 / Real.pi * ∫ v in Ioi (0 : ℝ), Cfreq v lam / v ^ 2
      ≤ 1 / Real.pi * ∫ v in Ioi (0 : ℝ), CG (v * vnorm lam) / v ^ 2 :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = Real.sqrt (Real.pi / 2) * vnorm lam := by
        rw [hval]; field_simp

/-- `K ≤ √(π/2)`: `J(λ) ≤ √(π/2)` for every unit vector, from the four named hypotheses. -/
theorem K_le_sqrt_of (hF : HFreq) (hB : HB) (hA : HPFA) (hG : HG) (n : ℕ) (lam : Fin n → ℝ)
    (h : ∑ j, lam j ^ 2 = 1) : J lam ≤ Real.sqrt (Real.pi / 2) := by
  have := J_le_of hF hB hA hG lam
  rwa [vnorm, h, Real.sqrt_one, mul_one] at this

/-- Theorem 1.1 with any constant `c` that bounds `J` on unit vectors (Theorem 2.2 + the bound on `K`). -/
theorem poincare_of_K {c : ℝ} (hK : ∀ (m : ℕ) (lam : Fin m → ℝ), ∑ j, lam j ^ 2 = 1 → J lam ≤ c)
    {n : ℕ} (f : Cube n → ℝ) : avg (fun x => |f x - avg f|) ≤ c * avg (gradNorm f) := by
  refine (reduction n f).trans ?_
  unfold avg
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity), Finset.mul_sum]
  refine Finset.sum_le_sum (fun y _ => ?_)
  by_cases h : gradNorm f y = 0
  · rw [h]; simp
  · have hpos : 0 < gradNorm f y := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h)
    have hunit : ∑ j, (D f j y / gradNorm f y) ^ 2 = 1 := by
      simp only [div_pow, ← Finset.sum_div]
      rw [show gradNorm f y ^ 2 = ∑ j, D f j y ^ 2 from Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
      exact div_self (by rw [← Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (D f j y)))]; exact pow_ne_zero 2 h)
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hK n _ hunit) hpos.le

/-- The sharp L¹ Poincaré inequality, from the four named hypotheses. -/
theorem poincare_L1_sharp_of (hF : HFreq) (hB : HB) (hA : HPFA) (hG : HG) (n : ℕ) (f : Cube n → ℝ) :
    avg (fun x => |f x - avg f|) ≤ Real.sqrt (Real.pi / 2) * avg (gradNorm f) :=
  poincare_of_K (fun m lam h => K_le_sqrt_of hF hB hA hG m lam h) f

/-- `C11a ≤ √(π/2)`, from the four named hypotheses. -/
theorem C11a_le_sqrt_of (hF : HFreq) (hB : HB) (hA : HPFA) (hG : HG) : C11a ≤ Real.sqrt (Real.pi / 2) :=
  C11a_le_of_valid (poincare_L1_sharp_of hF hB hA hG)

end Poincare11b
