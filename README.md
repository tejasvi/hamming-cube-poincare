# The L¹ Poincaré constant of the Hamming cube

Certificates, programs and Lean formalization for the paper *The L¹ Poincaré constant of the Hamming cube* by Tejasvi
Singh Tomar (doi:10.5281/zenodo.23715900). They are archived at doi:10.5281/zenodo.23715901.

## Theorem

Let `x` be uniform on `{-1,1}^n`, let `D_j f(x) = (f(x) - f(x^(j)))/2`, where `x^(j)` is `x` with the sign of the
`j`th coordinate changed, and let `|grad f|` be the Euclidean norm of `(D_1 f, ..., D_n f)`. Let `C` be the smallest
constant such that

    E|f(x) - E f(x)| <= C E|grad f|(x)

for every `n` and every real-valued `f : {-1,1}^n -> R`. Then `C = sqrt(pi/2) = 1.2533...`. In dimension `n` the
inequality holds
with the constant

    c_n = sqrt(n) (1 - sum_{k=2}^n (k-2)! binom(n,k) n^(-k)) < sqrt(pi/2),

which is nondecreasing in `n` and tends to `sqrt(pi/2)`. The lower bound `sqrt(pi/2)` comes from the Gaussian case.
Both bounds, `C <= sqrt(pi/2)` and `C >= sqrt(pi/2)`, are verified in Lean 4 with Mathlib (`lean/sharp/`). This is constant
11a of the repository of optimization constants (https://teorth.github.io/optimizationproblems/). For complex-valued
`f` the best constant is not known; the paper (Remark 5.1) gives the upper bound `pi^(3/2)/4`.

## Proof outline

The proof of `C = sqrt(pi/2)` is analytic (Sections 2-5 of the paper; Section 6 gives a second, elementary proof of the
upper bound, which is the route of the Lean proof in `lean/sharp/`, Section 7). The Python programs in this repository
belong to an independent, computer-assisted proof of the weaker bound `C <= 71/50 = 1.42` (proved in the first version of the paper, which the current version cites), and to numerical
remarks.

1. **Reduction** (Theorem 2.2). For `p` in `(0,1)` let `xi^(p)` take the value `sqrt((1-p)/p)` with probability `p`
   and `-sqrt(p/(1-p))` with probability `1-p`. For a vector `lambda` put

       J(lambda) = int_0^{pi/2} E|sum_j lambda_j xi_j| dtheta,   xi_j independent copies of xi^(p), p = (1 + sin theta)/2.

   By the Pisier-type inequality of Ivanisvili, van Handel and Volberg (Ann. of Math. 192 (2020), Theorem 1.2),
   `E|f - E f|` is at most the average over the cube of `J(grad f)`. Hence `C <= K`, the supremum of `J` over all unit
   vectors in all dimensions.
2. **Nonnegative coordinates** (Section 3). For `lambda` with nonnegative coordinates,
   `J(lambda) = int_0^inf (1 - prod_j (1 + lambda_j t) e^(-lambda_j t)) t^(-2) dt` and `J(lambda) < sqrt(pi/2) |lambda|`;
   among unit vectors with nonnegative coordinates, `J` is largest at `(1, ..., 1)/sqrt(n)` (Corollary 3.8).
3. **Both signs** (Theorem 4.1). `J(lambda) <= J(|lambda_1|, ..., |lambda_n|)` for every `lambda`. As a function of
   `q`, the characteristic function `E exp(-ic(eta - q))` of a centred Bernoulli(q) variable has the Fourier
   coefficients `sinc(c/(2 pi) - k)^2`, a probability distribution on the integers; for `c >= 0` these laws and their
   convolutions put at least as much mass at `k` as at `-k`.
4. **The constant** (Section 5). Steps 2 and 3 give `K_n = J((1, ..., 1)/sqrt(n)) = c_n`, so `C = sqrt(pi/2)`.
5. **Elementary route** (Section 6). For `lambda >= 0` and every frequency `v`, a transport argument in `q` (each
   positive coordinate decreases at unit speed until it reaches 0, and the lost variance goes into a Gaussian factor)
   bounds the frequency functional by its Gaussian value; with step 3 at every frequency this gives `J(lambda) <= sqrt(pi/2) |lambda|` for every `lambda`.

The computer-assisted proof of `C <= 71/50` (first version of the paper):

1. **Moment bounds** (Section 3 of the first version). If `h(z) = a + b z^2 + c z^4 + d z^6 >= |z|` on the real line, then
   `E|S| <= a + b + c E S^4 + d E S^6` for `S = sum_j lambda_j xi_j`. With `q = p(1-p) = cos(theta)^2/4` (written
   `sigma^2` in the paper) and the power sums `P_r = sum_j lambda_j^r`,

       E S^4 = 3 + k4 P4,   E S^6 = 15 + 15 k4 P4 + 10 mu3sq P3^2 + k6 P6,
       k4 = (1 - 6q)/q,  mu3sq = (1 - 4q)/q,  k6 = (1 - 30q + 120q^2)/q^2,

   and `(P4, P6)` lies in `R = {0 <= P4 <= 1, P4^2 <= P6 <= P4^(3/2)}` with `0 <= P3^2 <= P4`. Nothing depends on
   the dimension.
2. **Certificate** (Section 4 of the first version). Dyadic squares in the `(P4, P6)`-plane tile `[0,1]^2`. Squares that miss `R` are
   listed as outside squares. For every other square (leaf) and each of the `N = 1024` intervals
   `[i pi/2048, (i+1) pi/2048]` of `theta`, the certificate names one polynomial `h` of its list, or the trivial bound
   `E|S| <= 1`. For every leaf, the sum over the intervals of the interval length times the bound is at most `71/50`.

## Contents

| Path | Content |
|---|---|
| `certificate/mom_c142.json` | the certificate (claim `71/50`, 1761 polynomials, 302 leaves, 149 outside squares, `N = 1024`) |
| `checker/check11a_mom.py` | the checker: exact Sturm sequences, exact tiling test, ball arithmetic (Arb through python-flint, 200 bits) |
| `independent/check11a_indep.py` | a second checker, which uses different methods for the polynomial test, the tiling test and the bound |
| `search/mom_bb.py` | the search program that produced the certificate (floating point; not part of the proof) |
| `controls/` | perturbed certificates for testing the two checkers: generator and runner |
| `lean/sharp/` | a Lean 4 / Mathlib proof of `C = sqrt(pi/2)` (both inequalities; Section 7), a self-contained Lake project with its own README |
| `lean/` (other files) | a Lean 4 / Mathlib proof of the bound `C <= 71/50`, of the first inequality of Theorem 2.2 and of Theorem 4.2 of the first version, with its own README |
| `numerics/` | programs for the numerical statements in Sections 2, 4 and 5 of the paper and for one remark of its first version (not part of the proofs) |
| `paper/` | the LaTeX source of the paper (`main.tex`) |

The programs in `checker/`, `independent/`, `controls/` and `search/`, the programs `j_values.py`, `is_route_limit.py`
and `moment_ceiling.py` in `numerics/`, the Lean files and `README.md` of `lean/` and the copies of the `lean/` files in
`lean/sharp/Poincare11a/` use the numbering of the first version of the paper (doi:10.5281/zenodo.23524864), in which
the computer-assisted proof occupied Sections 1-5. The programs `fixed_theta.py` and `dim2_check.py` use the numbering
of the current version. The files in `lean/sharp/Poincare11b/` and `lean/sharp/README.md` use the labels of the written
notes on which the formal proof is based; the last rows of the table give their correspondence.

| First version, or label in `lean/sharp` | Current version |
|---|---|
| Theorem 1.1 (`C <= 71/50`) | not in the current version, which cites the first version for it |
| Lemma 2.1, Theorem 2.2, Remarks 2.3, 2.4 | unchanged |
| Sections 3 and 4 (Lemmas 3.1-3.4, Proposition 4.1, Theorem 4.2) | not in the current version |
| Section 5, Remark 5.2 | Remark 2.5 |
| Section 5, Remark 5.1 | not in the current version (`numerics/moment_ceiling.py`) |
| Section 6, Lemmas 6.1-6.4, Theorem 6.5, Corollaries 6.6, 6.7, Remark 6.8 | Section 3, Lemmas 3.1, 3.2, 3.4, 3.5, Theorem 3.6, Corollaries 3.7, 3.8, Remark 3.9 |
| `lean/sharp`: Lemmas B1, B2, B2', B3, B4 | Lemmas 4.2, 4.3, Corollary 4.4, Lemmas 4.5, 4.6 |
| `lean/sharp`: Theorem B at every frequency (`HB`) | Corollary 4.7 |
| `lean/sharp`: Theorem A at every frequency (`HPFA`) | the last statement of Theorem 6.1 |
| `lean/sharp`: frequency representation (`HFreq`), Gaussian frequency integral (`HG`) | (4.5), Lemma 6.6 |
| `lean/sharp`: M4 (directory `M4/`) | Lemma 3.2, (4.5) and Lemma 6.6 |

## Checking

Requirements: Python 3.9 or later (tested with 3.12) and python-flint (tested with 0.9). The checkers use nothing else
outside the standard library.

    python3 -I checker/check11a_mom.py certificate/mom_c142.json
    python3 -I independent/check11a_indep.py certificate/mom_c142.json

The option `-I` keeps the interpreter away from the current directory and from the user site directory. If
python-flint was installed with `pip install --user`, run the programs without `-I`.

The first program prints

    library: 1761 polynomials verified (exact Sturm)
    tiling: 302 leaves + 149 outside boxes tile [0,1]^2; outside boxes miss R
    all 302 leaves: sum_i |I_i| min(1, bound) <= claimed; worst [1.4198937012229533845979510814753785258346677227271125154642 +/- 2.08e-59]
    RESULT: PASS  K = sup_lambda J(lambda) <= 71/50  hence C_11a <= 71/50

in under 10 seconds on one core. Its checks are `assert` statements, so it refuses to run under `python -O`.
The second program prints the largest leaf sum, `[1.41844884202192 +/- 2.87e-15]`, and ends with
`RESULT: PASS (claimed 71/50)` in 10 to 25 seconds. Its exit
status is 0 exactly when every check passes. Both programs exit with status 1 on five perturbed certificates: one
claiming the value 1.418, one with a polynomial that takes a negative value on `[0, infinity)`, one with a leaf missing,
one with a leaf declared outside although it meets `R`, and one in which all polynomials of a leaf are replaced by the
first polynomial of the list. They also exit with status 1 on malformed input such as `N = 0`, an index list that is
too short, or an index outside the list. To make these eight certificates and run both programs on them:

    cd controls
    python3 make_controls.py ../certificate/mom_c142.json out
    sh run_controls.sh out

Every line printed by `run_controls.sh` should end with `exit 1`. The script calls `python3 -I`, so first confirm that
`python3 -I` prints PASS on the unperturbed certificate (python-flint must be importable by that interpreter), and look
at the last output line of each control to see that it is rejected for its own reason.

What the first program checks:

- every polynomial `h = (a, b, c, d)` of the list has `a > 0`, `d > 0`, and `H(u) = a - u + b u^2 + c u^4 + d u^6`
  has no root in `(0, inf)` (Sturm sequence in exact rational arithmetic), so `h(z) >= |z|`;
- the leaves and the outside squares tile `[0,1]^2` (exact descent of the quadtree from the root);
- every outside square `[s0,s1] x [t0,t1]` satisfies `t1 < s0^2` or `t0^2 > s1^3`, so it misses `R`;
- for every leaf and every interval with a polynomial, the range of `q` excludes 0, and the bound
  `a + b + c m4 + d m6` is enclosed in ball arithmetic over the interval of `q`, the square (with `P6` restricted to
  `[max(t0, s0^2), min(t1, s1^(3/2))]`) and `P3^2` in `[0, s1]`;
- for every leaf, the sum over the intervals of `|I_i| min(1, bound)` (bound 1 for the trivial entries) is at most the
  claim;
- as a guard against typing errors, the moment formulas at 39 rational values of `p` and, by exact enumeration, on
  random small instances.

The second program checks the polynomials by certified isolation of the complex roots of the integer-scaled `H`,
the tiling by testing that no square contains another and that the areas sum to 1, and the bound by maximizing,
for fixed `q`, the expression (affine in `P4`, `P3^2`, `P6`) at the corners of the box, with `q` enclosed on four
subintervals of each interval of `theta`.

## Lean formalization

**The constant** (`lean/sharp/`, Section 7 of the paper). This project proves that
`E|f - E f| <= sqrt(pi/2) E|grad f|` for every `n` and every `f : {-1,1}^n -> R` (`Poincare11b.poincare_L1_sharp`), that
every valid constant is at least `sqrt(pi/2)` (`Poincare11b.sqrt_le_of_valid`), and hence, with `C` defined as the
infimum of the valid constants, `sqrt(pi/2) <= C` (`Poincare11b.sqrt_le_C11a`) and `C = sqrt(pi/2)`
(`Poincare11b.C11a_eq`); it also proves `J(lambda) <= sqrt(pi/2) |lambda|` (`Poincare11b.J_le`). The upper bound follows the
elementary route of Section 6 and does not use Theorem 3.6; the lower bound uses the central limit theorem on the cube,
derived from Lévy's continuity theorem in Mathlib. The proofs are checked by the Lean kernel and use only the standard
axioms `propext`, `Classical.choice` and `Quot.sound` (no `native_decide`). The definitions (`Poincare11a/Defs.lean`)
and the reduction (`Poincare11a/Reduction.lean`) are byte-identical copies of the files in `lean/`.
`lean/sharp/README.md` gives the statements, the structure of the proof, the places where the formal proof differs
from the paper, and the build commands. To build:

    cd lean/sharp
    lake exe cache get
    lake build
    lake env lean Axioms.lean

**The bound 71/50** (`lean/`; first version of the paper). This Lean 4 / Mathlib project proves the bound `C <= 71/50`, the first
inequality of Theorem 2.2 (with `J(grad f(y))` written as `|grad f(y)| J(grad f(y)/|grad f(y)|)`) and Theorem 4.2 of the first version. As
in `lean/sharp/`, the proofs are checked by the Lean kernel and use only the standard axioms. The certificate
computations are evaluated by the kernel. The same statements are also proved with the certificate computations closed
by `native_decide`. `lean/README.md` gives the exact statements, the build commands, the expected output of
`#print axioms` and the places where the formal proof is arranged differently from the paper. The kernel-only build is

    cd lean
    lake exe cache get
    lake build Poincare11a.MainK Poincare11a.MainPaper

Both projects use Lean `v4.35.0-rc3` and Mathlib commit `c55e6e786f`.

## Certificate format

`mom_c142.json` is a JSON object with the keys

- `claimed`: the claimed bound, a string (`"71/50"`);
- `N`: the number of intervals of `theta`;
- `library`: a list of polynomials, each a list `[a, b, c, d]` of rational numbers written as strings;
- `leaves`: a list of pairs `[[l, i1, i2], idx]`, where `[l, i1, i2]` is the dyadic square
  `[i1 2^-l, (i1+1) 2^-l] x [i2 2^-l, (i2+1) 2^-l]` in the coordinates `(P4, P6)`, and `idx` is a list of `N` integers:
  `idx[i]` is the index in `library` of the polynomial used on the `i`th interval of `theta`, or `-1` for the trivial
  bound `E|S| <= 1`;
- `outside`: a list of dyadic squares `[l, i1, i2]` that miss `R`.

## Search

    python3 search/mom_bb.py 1.42 mom_c142.json 1024

The search needs NumPy and SciPy (tested with 2.5 and 1.18). It builds the list of polynomials from linear programs
on a grid of moments, rounds the coefficients to multiples of `2^-40`, raises the constant term until the exact
Sturm test passes, and then subdivides `[0,1]^2` until every leaf has a floating-point bound below the target minus
`2e-4`. Its output may differ from the certificate on other platforms. Any output is checked in the same way.

## Numerical remarks

The programs in `numerics/` are not part of any proof. `is_route_limit.py` and `moment_ceiling.py` need NumPy, SciPy
and python-flint, `j_values.py` needs NumPy, and `fixed_theta.py` and `dim2_check.py` use only the standard library.
Their outputs are in the `.out` files next to them.

| File | Content |
|---|---|
| `fixed_theta.py` | exact values `5888/3125` and `1024/625` for the fixed-`theta` example of Remark 4.8 |
| `j_values.py` | the constants `c_n = J((1, ..., 1)/sqrt(n))` for `n = 1, 2, 3, 10, 100, 1000`, by quadrature and by formula (A4) of Theorem 3.6 (Section 5) |
| `dim2_check.py` | the vector fields of Remark 5.2 (best constant `1` in dimension 2), checked in rational arithmetic for all 16 sign functions |
| `is_route_limit.py` | certified lower bound 1.42177 for the integral over `theta` of the supremum over unit vectors of `E|sum_j lambda_j xi_j|` (Remark 2.5): 400,000 equal intervals of `[0, pi/2 - 10^-6]`; on each, `n` is chosen at the left end, where `w = 1 - p` is largest, so that `n w <= 1` on the whole interval, and the equal-weight bound, which is unimodal in `w`, is bounded below by the smaller of its two endpoint values, in ball arithmetic |
| `moment_ceiling.py` | the best bound the sextic moment method can give at a point `(P4, P6)`; largest value 1.4160 over the region (Remark 5.1 of the first version; not in the current version) |
| `search_1418.log` | the search run with target 1.418. It stops at its depth limit, level 22, at the square with triple `(22, 187218, 39554)` near `(P4, P6) = (0.0446, 0.0094)`, where the bound of `moment_ceiling.py` is only 1.4137, so the failure comes from the finite list of polynomials, the 1024 intervals and the search margin `2e-4` |

## License

Apache License 2.0, see `LICENSE`.

## Citation

See `CITATION.cff`.
