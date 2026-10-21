# Lean 4 formalization: the L¹ Poincaré constant of the Hamming cube is √(π/2)

This directory contains a Lean 4 / Mathlib proof that for every `n` and every `f : {-1,1}^n → ℝ`,

    E|f − Ef| ≤ √(π/2) E|∇f|,

where `E` is the uniform average over the cube, `D_j f(x) = (f(x) − f(x^(j)))/2` and `|∇f|` is the Euclidean norm of
`(D_1 f, …, D_n f)`, and that the constant `√(π/2)` is optimal: the best constant `C11a` equals `√(π/2)`.

Toolchain: Lean `leanprover/lean4:v4.35.0-rc3`, Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`
(see `lean-toolchain` and `lake-manifest.json`).

## What is proved

Kernel-checked, standard axioms only (namespace `Poincare11b`, files `Poincare11b/Main.lean` and `Poincare11b/LB3.lean`):

| statement | Lean |
|---|---|
| the sharp inequality | `poincare_L1_sharp (n : ℕ) (f : Cube n → ℝ) : avg (fun x => \|f x - avg f\|) ≤ Real.sqrt (Real.pi / 2) * avg (gradNorm f)` |
| the best constant | `C11a_eq : C11a = Real.sqrt (Real.pi / 2)` |
| the two halves | `C11a_le_sqrt : C11a ≤ Real.sqrt (Real.pi / 2)`, `sqrt_le_C11a : Real.sqrt (Real.pi / 2) ≤ C11a` |
| `K ≤ √(π/2)` | `K_le_sqrt (n : ℕ) (lam : Fin n → ℝ) (h : ∑ j, lam j ^ 2 = 1) : J lam ≤ Real.sqrt (Real.pi / 2)` |
| `J(λ) ≤ √(π/2) \|λ\|` | `J_le (n : ℕ) (lam : Fin n → ℝ) : J lam ≤ Real.sqrt (Real.pi / 2) * vnorm lam` |

`lake env lean Axioms.lean` prints, for each of these theorems (and for `one_le_C11a : 1 ≤ C11a`),

    depends on axioms: [propext, Classical.choice, Quot.sound]

There is no `sorry`, `axiom`, `native_decide` or `implemented_by` in the sources.

## Definitions

All statements use the definitions of `Poincare11a/Defs.lean` (identical to the file of the same name in the Lean
project for the constant 71/50) and Mathlib:

```lean
abbrev Cube (n : ℕ) := Fin n → Bool                      -- true ↦ +1, false ↦ -1
def flip (j : Fin n) (x : Cube n) : Cube n := Function.update x j (!x j)
noncomputable def avg (g : Cube n → ℝ) : ℝ := (∑ x, g x) / 2 ^ n
noncomputable def D (f : Cube n → ℝ) (j : Fin n) (x : Cube n) : ℝ := (f x - f (flip j x)) / 2
noncomputable def gradNorm (f : Cube n → ℝ) (x : Cube n) : ℝ := Real.sqrt (∑ j, D f j x ^ 2)
noncomputable def C11a : ℝ :=
  sInf {C : ℝ | ∀ (m : ℕ) (f : Cube m → ℝ), avg (fun x => |f x - avg f|) ≤ C * avg (gradNorm f)}
noncomputable def xiVal (p : ℝ) : Bool → ℝ
  | true => Real.sqrt ((1 - p) / p)
  | false => -Real.sqrt (p / (1 - p))
def xiProb (p : ℝ) : Bool → ℝ
  | true => p
  | false => 1 - p
noncomputable def absMoment (p : ℝ) (lam : Fin n → ℝ) : ℝ :=
  ∑ z : Cube n, (∏ j, xiProb p (z j)) * |∑ j, lam j * xiVal p (z j)|
noncomputable def J (lam : Fin n → ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2), absMoment ((1 + Real.sin θ) / 2) lam
```

`Poincare11b/Statements.lean` adds the auxiliary functionals of the proof: `cosGap v q λ = E(1 − cos(v S_q))` with
`S_q = ∑_j λ_j (η_j − q)` (`η_j` independent Bernoulli(q)), `Cfreq v λ = ∫_0^1 cosGap v q λ dq/(q(1−q))`,
`CG r = ∫_0^1 (1 − exp(−r² q(1−q)/2)) dq/(q(1−q))`, `vnorm λ = |λ|`, `fc c q = (1−q)e^{icq} + q e^{−ic(1−q)}` and
`Fth θ q = ∏_j fc (θ_j) q`, together with the intermediate statements `HFreq`, `HB`, `HPFA`, `HG`, `HSSL` (each a
`Prop`, each proved below).

## Structure of the proof

1. **Reduction** (`Poincare11a/Reduction.lean`, unchanged from the 71/50 project): `E|f − Ef| ≤ E_y[|∇f(y)| J(∇f(y)/|∇f(y)|)]`.
   `Assemble.lean` turns any bound `J(λ) ≤ c` on unit vectors into `E|f − Ef| ≤ c E|∇f|`.
2. **Frequency representation** (`Freq.lean`, `hFreq`): `J(λ) = (1/π) ∫_0^∞ v⁻² C_v(λ) dv`, from
   `|x| = (2/π) ∫_0^∞ (1 − cos vx) v⁻² dv` (`M4/AbsCos.lean`), the substitution `q = (1 + sin θ)/2` and the symmetry
   `q ↔ 1 − q` (`M4/Arcsin.lean`), and Tonelli.
3. **Theorem B at every frequency** (`TheoremB.lean`, `hB`): `C_v(λ) ≤ C_v(|λ|)`. Writing `E e^{ivS_q}` as
   `conj(F_{vλ⁺}) F_{vλ⁻}`, the gap is `2 ∫_0^1 Im F_{vλ⁺} Im F_{vλ⁻} dq/(q(1−q))`; both imaginary parts are sine series with
   nonnegative coefficients (item 6) and `W(k,l) = ∫_0^1 sin 2πkq sin 2πlq dq/(q(1−q)) ≥ 0`.
4. **Theorem A at every frequency** (`PFA1.lean`–`PFA3.lean`, `hPFA`): `C_v(λ) ≤ C_G(v|λ|)` for `λ ≥ 0`. Along the path
   `θ − t` (all coordinates decrease at unit speed, the lost variance goes into a Gaussian factor `G_τ`),
   `d/dt [G_τ F_θ] = i q(1−q) G_τ ∂_q F_θ`; two integrations by parts give `d/dt C = ∫_0^1 G_τ'' I_θ ≥ 0`, with
   `I_θ(q) = ∫_0^q Im F_θ ≥ 0` (item 6). Induction on the number of coordinates.
5. **Gaussian frequency integral** (`Gauss.lean`, `hG`): `∫_0^∞ v⁻² C_G(vρ) dv = π √(π/2) ρ`.
6. **Sine series** (`ZSeries.lean`, `SU.lean`, `Kappa.lean`, `FourierFc.lean`, `SSL.lean`, `hSSL`): for `θ ≥ 0`,
   `Im F_θ(q) = ∑_{k≥1} β_k sin 2πkq` on `[0,1]` with `β_k ≥ 0` summable. The Fourier coefficients of `f_c` on `[0,1]` are
   `κ_c(k) = (2 − 2 cos c)/(c − 2πk)²`; `F_θ` has the convolution of these as coefficients, and this convolution is
   positively skewed.

Then `J(λ) = (1/π)∫ v⁻² C_v(λ) dv ≤ (1/π)∫ v⁻² C_G(v|λ|) dv = √(π/2)|λ|`.

7. **Lower bound** (`LB1.lean`–`LB3.lean`, `sqrt_le_C11a`): every valid constant is at least `√(π/2)`.
   - `LB1.lean`: the law of `t_n = n^{-1/2} ∑_j x_j` under the uniform measure on the cube converges weakly to `N(0,1)`
     (Lévy's continuity theorem and Mathlib's characteristic-function lemma for the central limit theorem).
   - `LB2.lean`: if `C` is valid, then `E|g(Z) − E g(Z)| ≤ C E|g'(Z)|` for every bounded continuous `g` with a bounded,
     continuous, Lipschitz derivative; test functions `g(t_n)`, with `|∇(g ∘ t_n)| = |g'(t_n)| + O(n^{-1/2})` uniformly.
   - `LB3.lean`: `g_ε(s) = ∫_0^s k_ε`, `k_ε(u) = (2/ε) max(0, 1 − |u|/ε)`; `E|g_ε'(Z)| ≤ 2φ(0)` and
     `E|g_ε(Z) − c| ≥ 1 − εφ(0)` for every `c`, so `C · 2φ(0) ≥ 1`, i.e. `C ≥ √(π/2)`.

## Presentation

Compared with the written proof, the formal proof differs in five places:

1. **Positive skew.** Instead of the continuous mixture of discrete Laplace laws, `κ_c = shift_m s₀ + shift_{m+1} s₁` with
   explicit symmetric unimodal sequences `s₀, s₁` given by telescoping series (`kap_decomp`). The convolution of two
   symmetric unimodal sequences is symmetric unimodal by a direct pairing argument (`SU_conv`).
2. **Fourier inversion** of `f_c` is Mathlib's theorem for continuous functions on the circle with summable
   coefficients (`fc_hasSum`).
3. **Theorem B.** The double series is used as two iterated sums, dominated by the constants coming from
   `|sin 2πlq|/(q(1−q)) ≤ 4π|l|` and `|Im F_θ(q)| ≤ 2|θ|₁ q(1−q)`; no logarithmic moment bound is needed.
4. **The constant π/2** in the formula for `|x|` comes from `1/v² = ∫_0^∞ t e^{−tv} dt`, Tonelli and `arctan`.
5. **Lower bound.** Instead of the family `2Φ(s/ε) − 1`, the test functions are the integrals of tent functions, for
   which only the bounds `E|g_ε'(Z)| ≤ 2φ(0)` and `E|g_ε(Z) − c| ≥ 1 − εφ(0)` are needed.

## Building

From a clean checkout of this directory:

    lake exe cache get        # Mathlib build cache for the pinned commit
    lake build                # all modules (Poincare11a: 14, Poincare11b: 20)
    lake env lean Axioms.lean

After the Mathlib cache is in place, building all project modules takes about 45 seconds on a 22-core machine; no module
needs more than a few GB of memory.

## Layout

- `Poincare11a/`: the definitions and the reduction, identical to the files of the same names in the 71/50 project
  (`Defs`, `Moments`, `Semigroup`, `Prims`, `Checker`, `Bernstein`, `Region`, `Bound`, `Partition`, `CertSound`, `Assembly`,
  `KLe`, `Reduction`, `Constant`; no certificate data is used).
- `Poincare11b/Statements.lean`: auxiliary definitions and the intermediate statements.
- `Poincare11b/Assemble.lean`: the final theorems from the intermediate statements.
- `Poincare11b/Main.lean`: the upper bound theorems; `Poincare11b/LB3.lean`: `sqrt_le_C11a` and `C11a_eq`.
- the other files: the proofs of items 2-7 above.
