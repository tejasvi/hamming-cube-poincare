/-
Definitions for the L¹ Poincaré inequality on the Hamming cube (constant 11a).
The cube {-1,1}^n is encoded as `Fin n → Bool` (`true` ↦ +1, `false` ↦ -1); flipping coordinate `j` is `!`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Poincare11a

open scoped BigOperators

/-- The Hamming cube `{-1,1}^n`, coordinates encoded as `Bool` (`true` ↦ +1, `false` ↦ -1). -/
abbrev Cube (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- `x^(j)`: the point `x` with coordinate `j` changed. -/
def flip (j : Fin n) (x : Cube n) : Cube n := Function.update x j (!x j)

/-- Uniform average `E g = 2^{-n} ∑_x g(x)` over the cube. -/
noncomputable def avg (g : Cube n → ℝ) : ℝ := (∑ x, g x) / 2 ^ n

/-- Discrete partial derivative `D_j f(x) = (f(x) - f(x^(j)))/2`. -/
noncomputable def D (f : Cube n → ℝ) (j : Fin n) (x : Cube n) : ℝ := (f x - f (flip j x)) / 2

/-- Length of the discrete gradient `|∇f|(x) = (∑_j D_j f(x)^2)^{1/2}`. -/
noncomputable def gradNorm (f : Cube n → ℝ) (x : Cube n) : ℝ := Real.sqrt (∑ j, D f j x ^ 2)

/-- The L¹ Poincaré constant: the infimum of the constants `C` with `E|f - Ef| ≤ C E|∇f|` for all `n` and `f`. -/
noncomputable def C11a : ℝ :=
  sInf {C : ℝ | ∀ (m : ℕ) (f : Cube m → ℝ), avg (fun x => |f x - avg f|) ≤ C * avg (gradNorm f)}

/-- Values of the standardized biased sign `ξ^(p)`: `√((1-p)/p)` (probability `p`) and `-√(p/(1-p))`. -/
noncomputable def xiVal (p : ℝ) : Bool → ℝ
  | true => Real.sqrt ((1 - p) / p)
  | false => -Real.sqrt (p / (1 - p))

/-- Probabilities of the two values of `ξ^(p)`. -/
def xiProb (p : ℝ) : Bool → ℝ
  | true => p
  | false => 1 - p

/-- `E|∑_j λ_j ξ_j^(p)|` for independent copies `ξ_1, …, ξ_n` of `ξ^(p)` (exact finite expectation). -/
noncomputable def absMoment (p : ℝ) (lam : Fin n → ℝ) : ℝ :=
  ∑ z : Cube n, (∏ j, xiProb p (z j)) * |∑ j, lam j * xiVal p (z j)|

/-- `J(λ) = ∫_0^{π/2} E|∑_j λ_j ξ_j^(p(θ))| dθ` with `p(θ) = (1 + sin θ)/2`. -/
noncomputable def J (lam : Fin n → ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2), absMoment ((1 + Real.sin θ) / 2) lam

end Poincare11a
