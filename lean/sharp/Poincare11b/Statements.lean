/-
Definitions and named hypotheses for the sharp L¹ Poincaré inequality on the Hamming cube (constant √(π/2)).
All objects of `Poincare11a.Defs` (`Cube`, `avg`, `D`, `gradNorm`, `xiProb`, `absMoment`, `J`, `C11a`) are used unchanged.
-/
import Poincare11a.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Poincare11b

open Poincare11a MeasureTheory Set

variable {n : ℕ}

/-- The Bernoulli variable: `true ↦ 1` (probability `q = xiProb q true`), `false ↦ 0`. -/
def eta (b : Bool) : ℝ := if b then 1 else 0

/-- `E(1 - cos(v S_q))`, where `S_q = ∑_j λ_j (η_j - q)` and `η_1, …, η_n` are independent Bernoulli(q) variables
(exact finite expectation). -/
noncomputable def cosGap (v q : ℝ) (lam : Fin n → ℝ) : ℝ :=
  ∑ z : Cube n, (∏ j, xiProb q (z j)) * (1 - Real.cos (v * ∑ j, lam j * (eta (z j) - q)))

/-- The frequency functional `C_v(λ) = ∫_0^1 E(1 - cos(v S_q)) dq / (q(1-q))`. -/
noncomputable def Cfreq (v : ℝ) (lam : Fin n → ℝ) : ℝ :=
  ∫ q in Ioo (0 : ℝ) 1, cosGap v q lam / (q * (1 - q))

/-- The Gaussian frequency functional `C_G(r) = ∫_0^1 (1 - exp(-r² q(1-q)/2)) dq / (q(1-q))`. -/
noncomputable def CG (r : ℝ) : ℝ :=
  ∫ q in Ioo (0 : ℝ) 1, (1 - Real.exp (-(r ^ 2 * (q * (1 - q)) / 2))) / (q * (1 - q))

/-- Euclidean length `|λ|`. -/
noncomputable def vnorm (lam : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, lam j ^ 2)

/-- `f_c(q) = (1-q) e^{icq} + q e^{-ic(1-q)} = E exp(-ic(η - q))`, `η` Bernoulli(q). -/
noncomputable def fc (c q : ℝ) : ℂ :=
  (1 - q) * Complex.exp (c * q * Complex.I) + q * Complex.exp (-(c * (1 - q)) * Complex.I)

/-- `F_θ(q) = ∏_j f_{θ_j}(q)`. -/
noncomputable def Fth (θ : Fin n → ℝ) (q : ℝ) : ℂ := ∏ j, fc (θ j) q

/-! ## Named hypotheses (each is proved in its own module; `Main.lean` assembles them) -/

/-- (H_freq) Frequency representation of `J`: `J(λ) = (1/π) ∫_0^∞ v^{-2} C_v(λ) dv` (q-form of `J`, the formula
`|x| = (2/π) ∫_0^∞ (1 - cos(vx)) v^{-2} dv`, and Tonelli). -/
def HFreq : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ),
    IntegrableOn (fun v => Cfreq v lam / v ^ 2) (Ioi 0) ∧
      J lam = 1 / Real.pi * ∫ v in Ioi (0 : ℝ), Cfreq v lam / v ^ 2

/-- (H_B) Theorem B at every frequency: `C_v(λ) ≤ C_v(|λ|)`. -/
def HB : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (v : ℝ), 0 < v → Cfreq v lam ≤ Cfreq v (fun j => |lam j|)

/-- (H_PFA) Theorem A at every frequency, for nonnegative directions: `C_v(λ) ≤ C_G(v|λ|)`. -/
def HPFA : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (v : ℝ), (∀ j, 0 ≤ lam j) → 0 < v → Cfreq v lam ≤ CG (v * vnorm lam)

/-- (H_G) The Gaussian frequency integral: `∫_0^∞ v^{-2} C_G(vρ) dv = π √(π/2) ρ`. -/
def HG : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ →
    IntegrableOn (fun v => CG (v * ρ) / v ^ 2) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), CG (v * ρ) / v ^ 2 = Real.pi * Real.sqrt (Real.pi / 2) * ρ

/-- (SSL, used by H_B and H_PFA) For `θ ≥ 0`, `Im F_θ` is a sine series with nonnegative summable coefficients:
`Im F_θ(q) = ∑_{k ≥ 1} β_k sin(2πkq)` on `[0,1]` (Lemmas B2, B3). -/
def HSSL : Prop :=
  ∀ (n : ℕ) (θ : Fin n → ℝ), (∀ j, 0 ≤ θ j) →
    ∃ β : ℕ → ℝ, (∀ k, 0 ≤ β k) ∧ Summable β ∧
      ∀ q ∈ Icc (0 : ℝ) 1, (Fth θ q).im = ∑' k, β k * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q)

end Poincare11b
