/-
The constant `C11a` (an infimum): `1 ≤ C11a`, and `C11a ≤ c` for every valid `c`.
-/
import Poincare11a.Defs
import Mathlib.Tactic

namespace Poincare11a

lemma sum_cube_one (g : Cube 1 → ℝ) : ∑ x, g x = g (fun _ => true) + g (fun _ => false) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]; rfl

/-- Every valid constant is at least 1 (test function: the indicator of one point of `{-1,1}^1`). -/
theorem one_le_of_valid {C : ℝ}
    (hC : ∀ (m : ℕ) (f : Cube m → ℝ), avg (fun x => |f x - avg f|) ≤ C * avg (gradNorm f)) : 1 ≤ C := by
  have h := hC 1 (fun x => if x 0 then 1 else 0)
  simp only [avg, gradNorm, D, sum_cube_one, flip, Fin.sum_univ_one, Function.update_self] at h
  norm_num at h
  linarith

/-- `C11a ≤ c` for every valid constant `c`. -/
theorem C11a_le_of_valid {c : ℝ}
    (hc : ∀ (m : ℕ) (f : Cube m → ℝ), avg (fun x => |f x - avg f|) ≤ c * avg (gradNorm f)) : C11a ≤ c :=
  csInf_le ⟨1, fun _ hC => one_le_of_valid hC⟩ hc

/-- `1 ≤ C11a`, given that some constant is valid (so that the infimum is over a nonempty set). -/
theorem one_le_C11a_of_valid {c : ℝ}
    (hc : ∀ (m : ℕ) (f : Cube m → ℝ), avg (fun x => |f x - avg f|) ≤ c * avg (gradNorm f)) : 1 ≤ C11a :=
  le_csInf ⟨c, hc⟩ (fun _ hC => one_le_of_valid hC)

end Poincare11a
