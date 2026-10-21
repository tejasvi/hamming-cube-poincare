/-
The sharp L¹ Poincaré inequality on the Hamming cube: `E|f - Ef| ≤ √(π/2) E|∇f|` for every `n` and every
`f : {-1,1}^n → ℝ`, with the definitions of `Poincare11a.Defs`. Kernel-checked, standard axioms only.
-/
import Poincare11b.Assemble
import Poincare11b.Freq
import Poincare11b.Gauss
import Poincare11b.TheoremB
import Poincare11b.PFA3

namespace Poincare11b

open Poincare11a

/-- `J(λ) ≤ √(π/2) |λ|` for every `λ ∈ ℝⁿ`. -/
theorem J_le (n : ℕ) (lam : Fin n → ℝ) : J lam ≤ Real.sqrt (Real.pi / 2) * vnorm lam :=
  J_le_of hFreq hB hPFA hG lam

/-- `K ≤ √(π/2)`: `J(λ) ≤ √(π/2)` for every unit vector `λ`, in every dimension. -/
theorem K_le_sqrt (n : ℕ) (lam : Fin n → ℝ) (h : ∑ j, lam j ^ 2 = 1) : J lam ≤ Real.sqrt (Real.pi / 2) :=
  K_le_sqrt_of hFreq hB hPFA hG n lam h

/-- The sharp L¹ Poincaré inequality: `E|f - Ef| ≤ √(π/2) E|∇f|` for every `n` and every `f : {-1,1}^n → ℝ`. -/
theorem poincare_L1_sharp (n : ℕ) (f : Cube n → ℝ) :
    avg (fun x => |f x - avg f|) ≤ Real.sqrt (Real.pi / 2) * avg (gradNorm f) :=
  poincare_L1_sharp_of hFreq hB hPFA hG n f

/-- `C11a ≤ √(π/2)`. -/
theorem C11a_le_sqrt : C11a ≤ Real.sqrt (Real.pi / 2) :=
  C11a_le_sqrt_of hFreq hB hPFA hG

/-- The trivial lower bound `1 ≤ C11a` (the infimum is over a nonempty set that is bounded below). -/
theorem one_le_C11a : 1 ≤ C11a :=
  one_le_C11a_of_valid (fun m f => poincare_L1_sharp m f)

end Poincare11b
