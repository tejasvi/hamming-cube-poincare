# Lean 4 formalization: the L¹ Poincaré inequality on the Hamming cube with constant 71/50

This directory contains a Lean 4 / Mathlib proof of the main results of the accompanying paper. For every `n` and every
`f : {-1,1}^n → ℝ`,

    E|f − Ef| ≤ (71/50) E|∇f|,

where `E` is the uniform average over the cube, `D_j f(x) = (f(x) − f(x^(j)))/2` and `|∇f|` is the Euclidean norm of
`(D_1 f, …, D_n f)`.

Toolchain: Lean `leanprover/lean4:v4.35.0-rc3`, Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`
(see `lean-toolchain` and `lake-manifest.json`).

## What is proved

Kernel-checked, standard axioms only (namespace `Poincare11a.K`, files `MainK.lean` and `MainPaper.lean`):

| paper | Lean |
|---|---|
| Theorem 1.1 | `K.poincare_L1 (n : ℕ) (f : Cube n → ℝ) : avg (fun x => \|f x - avg f\|) ≤ 71 / 50 * avg (gradNorm f)` |
| Theorem 1.1, as `C ≤ 71/50` | `K.C11a_le : C11a ≤ 71 / 50` (and `K.one_le_C11a : 1 ≤ C11a`, so the infimum is over a nonempty, bounded-below set) |
| Theorem 4.2 | `K.K_le (n : ℕ) (lam : Fin n → ℝ) (h : ∑ j, lam j ^ 2 = 1) : J lam ≤ 71 / 50` |
| Theorem 2.2 (first inequality) | `K.reduction (n : ℕ) (f : Cube n → ℝ) : avg (fun x => \|f x - avg f\|) ≤ avg (fun y => gradNorm f y * J (fun j => D f j y / gradNorm f y))` |
| Theorem 1.1 via Theorems 2.2 and 4.2 | `K.poincare_L1_via_reduction` |
| Remark 2.3(i) | `J_e1 : J (fun _ : Fin 1 => 1) = 1`, and `J_intervalIntegrable` (the integrand of `J` is integrable, so `J` is the genuine integral) |

The same statements with the certificate computations closed by `native_decide` are in namespace `Poincare11a.N`
(`MainN.lean`: `N.poincare_L1`, `N.C11a_le`, `N.one_le_C11a`, `N.K_le`).

All statements use only the definitions of `Poincare11a/Defs.lean` and Mathlib:

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

## Building

From a clean checkout of this directory:

    lake exe cache get                                    # Mathlib build cache for the pinned commit
    lake build Poincare11a.MainK Poincare11a.MainPaper    # kernel-only track
    lake build Poincare11a.MainN                          # native_decide track

After the Mathlib cache is in place, building all project modules takes about 1.5 minutes on a 32-core machine. The
kernel evaluation of the certificate (the 49 modules in `CertK/`) takes about 20 CPU-minutes in total, about 4 seconds
per leaf square, and each of these modules needs less than 1 GB of memory. The modules that import Mathlib need up to
about 4 GB each. The `native_decide` checks of `CertN.lean` take a few seconds.

## Axioms

    import Poincare11a.MainK
    import Poincare11a.MainPaper
    import Poincare11a.MainN
    #print axioms Poincare11a.K.poincare_L1
    #print axioms Poincare11a.N.poincare_L1

prints, for every theorem of namespace `K` (and for `reduction`, `J_e1`, `J_intervalIntegrable`):

    'Poincare11a.K.poincare_L1' depends on axioms: [propext, Classical.choice, Quot.sound]

and for the theorems of namespace `N` the same three axioms plus one axiom per `native_decide` call:

    Poincare11a.CertN.ivs_partOK._native.native_decide.ax_1_1,
    Poincare11a.CertN.lib_allPos._native.native_decide.ax_1_1,
    Poincare11a.CertN.tree_check._native.native_decide.ax_1_1

## Layout

- `Defs.lean`: the definitions used in the statements.
- `Checker.lean`: the certificate checker. It uses Lean core only (no Mathlib) and integer arithmetic only.
- Proofs:
  - `Semigroup.lean`: the semigroup identity of Lemma 2.1, in the variable `θ`.
  - `Moments.lean`: the moment identities of Lemma 3.2.
  - `Region.lean`: Lemma 3.4.
  - `Bernstein.lean`: positivity of the polynomial majorants (Lemma 3.3).
  - `Bound.lean`: the moment bound for one `θ` and its exact maximization.
  - `Partition.lean`: the `θ`-partition.
  - `Prims.lean`: the integer primitives used by the checker.
  - `CertSound.lean`: Proposition 4.1.
  - `Assembly.lean`: Theorem 1.1 from the certificate.
  - `Constant.lean`: the constant `C11a`.
  - `KLe.lean`: Theorem 4.2.
  - `Reduction.lean`: Theorem 2.2.
- `Data/`: the certificate in Lean form, generated by `gen/export_lean.py`.
- `CertK/`: the kernel evaluations (`decide +kernel`), generated by `gen/export_certk.py`.
- `CertN.lean`: the same checks with `native_decide`.
- `MainK.lean`, `MainN.lean`, `MainPaper.lean`: the final theorems.

## Presentation

The mathematics is that of the paper. It is presented differently in five places, where this keeps analysis and floating
point out of the formal proof:

1. **Theorem 1.1 directly.** With `m = sin θ`, let `P(m, x) = ∑_z ∏_j w(m, z_j) f(x ⊙ z)` with `w(m, ±1) = (1 ± m)/2`.
   - Then `P(1, x) = f(x)`, `P(0, x) = Ef`, and `d/dθ P(sin θ, x) = E_ζ ∑_j δ_j D_j f(x ⊙ ζ)` when `cos θ > 0`.
   - On each `θ`-interval, the mean value theorem is applied to `∑_x s(x)(P(sin θ, x) − P(sin θ_i, x))`, with a fixed
     sign vector `s`. This replaces the integral over `θ`.
   - Theorem 2.2 is proved separately, by the fundamental theorem of calculus.
2. **Rational partition.**
   - The partition points are `θ_i = 2 arctan t_i`, with dyadic `t_i ≈ tan(iπ/4096)`, `t_0 = 0` and `t_1024 = 1`. So
     `sin θ_i` and `cos θ_i` are rational.
   - The intervals agree with the paper's `[iπ/2048, (i+1)π/2048]` to within `10^-9`, and they carry the same
     polynomial indices.
   - The interval lengths enter through `∑ |I_i| = π/2`, `sin |I_i| ≤ |I_i|` and `π < 3.141593`.
3. **Exact maximization.**
   - In the variable `v = 4/cos²θ`, the bound of Lemmas 3.2-3.3 is affine in `(P4, P3², P6)`.
   - It is convex in `v`: the coefficient of `v²` is `d·P6 ≥ 0`.
   - So its maximum over a `θ`-interval and a square is attained at an end of the `v`-range and at a corner of the box
     chosen by signs. The checker evaluates exactly these points, in integer arithmetic.
   - The upper bound `s1^{3/2}` for `P6` is replaced by a dyadic `r` with `r² ≥ s1³`.
   - With these changes the largest leaf sum is `1.4182152`, which is below `71/50`.
4. **Bernstein positivity.** Positivity of `H(u) = a − u + bu² + cu⁴ + du⁶` on `[0, ∞)` is checked by Bernstein subdivision
   of `(1 − s)^6 H(s/(1 − s))` on `[0, 1]`, instead of by Sturm sequences.
5. **Quadtree as a term.** The quadtree of squares is a Lean term, so the tiling of Proposition 4.1(a) holds by
   construction.

## Regenerating the data

The files in `Data/` and `CertK/` are generated deterministically from the certificate `../certificate/mom_c142.json`
(sha256 `931895626b499b932af4ecf332f5491e06a0ae94e2e031ef6e8ee45496fb0758`). The generated headers name the input file
`mom_c142_93189562.json`, so copy the certificate under that name before regenerating:

    cp ../certificate/mom_c142.json mom_c142_93189562.json
    python3 gen/export_lean.py mom_c142_93189562.json Poincare11a/Data
    python3 gen/export_certk.py mom_c142_93189562.json . 10

The output is byte-identical to the files in this directory (checked with CPython 3.12 on Linux x86-64; the partition
parameters are rounded from the platform's `math.tan`). `export_lean.py` also writes `Poincare11a/Data/manifest.json`,
which `export_certk.py` reads. It also runs an integer re-implementation of the leaf check and prints the largest leaf
sum.
