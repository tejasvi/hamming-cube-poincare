/-
Computable checker for the moment certificate of `K ≤ 71/50` (integer arithmetic only).

Scales (all quantities are integers):
* library polynomial `h(z) = a + b z² + c z⁴ + d z⁶` is stored as `(A, B, C, D) = DLIB · (a, b, c, d)`;
* `v = 1/q = 4/cos²θ` is stored as `VV = VSC · v`;
* box coordinates `P4, P6, P3²` are integers over `2^60`;
* interval weights `ℓ` are integers over `2^64`;
* the bound `E` is computed as `E · ONE` with `ONE = DLIB · VSC² · 2^60`.
-/

namespace Poincare11a.Cert

/-- Common denominator of the library coefficients: `2^40 · 5^8`. -/
def DLIB : Int := 429496729600000000
/-- Scale of `v`: `2^40`. -/
def VSC : Int := 1099511627776
/-- `2^60`, the scale of box coordinates. -/
def P60 : Int := 1152921504606846976
/-- `2^64`, the scale of interval weights. -/
def P64 : Int := 18446744073709551616
/-- `2^32`, the scale of the partition parameters `t_i`. -/
def P32 : Int := 4294967296
/-- `ONE = DLIB · VSC² · 2^60` (literal; see `ONE_eq`). -/
def ONE : Int := 598631070650737835296229307480589524851069969602969600000000
/-- `VSC² · 2^60` (literal; see `K0SC_eq`). -/
def K0SC : Int := 1393796574908163946345982392040522594123776
/-- `1507965 · 2^64 · ONE`, the threshold of `gainOK` (literal; see `THR_eq`). -/
def THR : Int := 16652147087740852034750482598173719498248698465950267138649049345826408628224000000000

theorem ONE_eq : ONE = DLIB * VSC * VSC * P60 := by decide
theorem K0SC_eq : K0SC = VSC * VSC * P60 := by decide

/-! ### Kernel-friendly integer primitives (a single `match` on the constructor of a difference) -/

/-- `a ≤ b` as a Bool. -/
def ile (a b : Int) : Bool := match b - a with
  | .ofNat _ => true
  | .negSucc _ => false

/-- `a < b` as a Bool. -/
def ilt (a b : Int) : Bool := match a - b with
  | .ofNat _ => false
  | .negSucc _ => true

/-- `0 < a` as a Bool. -/
def ipos (a : Int) : Bool := match a with
  | .ofNat 0 => false
  | .ofNat (_ + 1) => true
  | .negSucc _ => false

/-- `max a b`. -/
def imax (a b : Int) : Int := match ile a b with
  | true => b
  | false => a

/-- `min a b`. -/
def imin (a b : Int) : Int := match ile a b with
  | true => a
  | false => b

/-! ### Library polynomials and their positivity (Bernstein subdivision) -/

/-- A library polynomial, scaled by `DLIB`. -/
structure Poly where
  A : Int
  B : Int
  C : Int
  D : Int
  deriving Repr, DecidableEq

/-- Seven Bernstein coefficients (degree 6). -/
structure B7 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  c4 : Int
  c5 : Int
  c6 : Int
  deriving Repr, DecidableEq

/-- All seven coefficients are positive. -/
def B7.allPos (b : B7) : Bool :=
  ipos b.c0 && ipos b.c1 && ipos b.c2 && ipos b.c3 && ipos b.c4 && ipos b.c5 && ipos b.c6

/-- De Casteljau halves, both scaled by `2^6` (sums instead of averages, no division). -/
def B7.left (b : B7) : B7 :=
  let d0 := b.c0 + b.c1; let d1 := b.c1 + b.c2; let d2 := b.c2 + b.c3
  let d3 := b.c3 + b.c4; let d4 := b.c4 + b.c5; let d5 := b.c5 + b.c6
  let e0 := d0 + d1; let e1 := d1 + d2; let e2 := d2 + d3; let e3 := d3 + d4; let e4 := d4 + d5
  let f0 := e0 + e1; let f1 := e1 + e2; let f2 := e2 + e3; let f3 := e3 + e4
  let g0 := f0 + f1; let g1 := f1 + f2; let g2 := f2 + f3
  let h0 := g0 + g1; let h1 := g1 + g2
  ⟨64 * b.c0, 32 * d0, 16 * e0, 8 * f0, 4 * g0, 2 * h0, h0 + h1⟩

/-- Right de Casteljau half, scaled by `2^6`. -/
def B7.right (b : B7) : B7 :=
  let d0 := b.c0 + b.c1; let d1 := b.c1 + b.c2; let d2 := b.c2 + b.c3
  let d3 := b.c3 + b.c4; let d4 := b.c4 + b.c5; let d5 := b.c5 + b.c6
  let e0 := d0 + d1; let e1 := d1 + d2; let e2 := d2 + d3; let e3 := d3 + d4; let e4 := d4 + d5
  let f0 := e0 + e1; let f1 := e1 + e2; let f2 := e2 + e3; let f3 := e3 + e4
  let g0 := f0 + f1; let g1 := f1 + f2; let g2 := f2 + f3
  let h0 := g0 + g1; let h1 := g1 + g2
  ⟨h0 + h1, 2 * h1, 4 * g2, 8 * f3, 16 * e4, 32 * d5, 64 * b.c6⟩

/-- Bisection until all Bernstein coefficients are positive (with fuel). -/
def posB : Nat → B7 → Bool
  | 0, b => b.allPos
  | fuel + 1, b =>
    match b.allPos with
    | true => true
    | false => ipos b.c0 && ipos b.c6 && posB fuel b.left && posB fuel b.right

/-- Bernstein coefficients of `G(s) = (1-s)^6 H(s/(1-s))` on `[0,1]`, scaled by `90 · DLIB`, where
`H(u) = a - u + b u² + c u⁴ + d u⁶`: `(a, -1/6, b/15, 0, c/15, 0, d)`. -/
def Poly.bern (p : Poly) : B7 := ⟨90 * p.A, -15 * DLIB, 6 * p.B, 0, 6 * p.C, 0, 90 * p.D⟩

/-- Positivity certificate of `H` on `[0, ∞)`. -/
def Poly.posOK (p : Poly) : Bool := posB 40 p.bern

/-- Library as a binary tree indexed by the binary digits of the index (least significant digit first). -/
inductive LibT where
  | nil : LibT
  | leaf : Poly → LibT
  | node : LibT → LibT → LibT

/-- Lookup by index. -/
def LibT.get : LibT → Nat → Option Poly
  | .nil, _ => none
  | .leaf p, j => if j = 0 then some p else none
  | .node l r, j => if j % 2 = 0 then l.get (j / 2) else r.get (j / 2)

/-- Every polynomial in the tree passes the positivity check. -/
def LibT.allPos : LibT → Bool
  | .nil => true
  | .leaf p => p.posOK
  | .node l r => l.allPos && r.allPos

/-! ### θ-partition -/

/-- One θ-interval `[θ_i, θ_{i+1}]` with `θ_i = 2 arctan (TL/2^32)`, `θ_{i+1} = 2 arctan (TR/2^32)`:
`VL ≤ VSC · 4/cos²θ_i`, `VH ≥ VSC · 4/cos²θ_{i+1}` (when `TR < 2^32`), `LL ≤ 2^64 · sin(θ_{i+1} - θ_i)`, and the
values of `(v - 6)·VSC, (v - 4)·VSC, v² - 30 v + 120` (times `VSC²`) at `v = VL/VSC` and `v = VH/VSC`. -/
structure Ivl where
  TL : Int
  TR : Int
  VL : Int
  VH : Int
  LL : Int
  w6l : Int
  w4l : Int
  w30l : Int
  w6h : Int
  w4h : Int
  w30h : Int
  deriving Repr, DecidableEq

/-- The relations between the fields of one interval. -/
def Ivl.ok (iv : Ivl) : Bool :=
  let cl := P64 - iv.TL * iv.TL
  let pl := P64 + iv.TL * iv.TL
  let cr := P64 - iv.TR * iv.TR
  let pr := P64 + iv.TR * iv.TR
  decide (0 ≤ iv.TL) && decide (iv.TL < iv.TR) && decide (iv.TR ≤ P32) &&
  decide (iv.VL * (cl * cl) ≤ 4 * VSC * (pl * pl)) &&
  (decide (iv.TR = P32) || decide (4 * VSC * (pr * pr) ≤ iv.VH * (cr * cr))) &&
  decide (0 ≤ iv.LL) &&
  decide (iv.LL * (pl * pr) ≤ P64 * (2 * P32) * ((iv.TR - iv.TL) * (P64 + iv.TL * iv.TR))) &&
  decide (iv.w6l = (iv.VL - 6 * VSC) * VSC) && decide (iv.w4l = (iv.VL - 4 * VSC) * VSC) &&
  decide (iv.w30l = iv.VL * iv.VL - 30 * VSC * iv.VL + 120 * VSC * VSC) &&
  decide (iv.w6h = (iv.VH - 6 * VSC) * VSC) && decide (iv.w4h = (iv.VH - 4 * VSC) * VSC) &&
  decide (iv.w30h = iv.VH * iv.VH - 30 * VSC * iv.VH + 120 * VSC * VSC)

/-- Consecutive intervals share endpoints; the first starts at `t = 0`, the last ends at `t = 1`. -/
def chainOK : Int → List Ivl → Bool
  | t, [] => decide (t = P32)
  | t, iv :: ivs => decide (iv.TL = t) && iv.ok && chainOK iv.TR ivs

/-- The partition table is valid and has `N = 1024` intervals. -/
def partOK (ivs : List Ivl) : Bool := decide (ivs.length = 1024) && chainOK 0 ivs

/-! ### Bound per (leaf, interval) -/

/-- Exact maximum of `w · x` over `x ∈ [lo, hi]`, assuming `lo ≤ hi`. -/
def sel (w lo hi : Int) : Int := match w with
  | .ofNat _ => w * hi
  | .negSucc _ => w * lo

/-- Per-run constants: `k0 = (A+B+3C+15D)·VSC²·2^60` and the ranges of `(C+15D)·P4`, `10D·P3²`, `D·P6`
(scaled by `DLIB · 2^60`). -/
structure RunC where
  k0 : Int
  c4lo : Int
  c4hi : Int
  c3lo : Int
  c3hi : Int
  c6lo : Int
  c6hi : Int

/-- Run constants for polynomial `p` and the box `P4 ∈ [S0, S1]`, `P3² ∈ [0, S1]`, `P6 ∈ [T0, T1]` (over `2^60`). -/
def mkRunC (p : Poly) (S0 S1 T0 T1 : Int) : RunC :=
  let e := p.C + 15 * p.D
  let c3 := 10 * p.D * S1
  { k0 := (p.A + p.B + 3 * p.C + 15 * p.D) * K0SC
    c4lo := imin (e * S0) (e * S1), c4hi := imax (e * S0) (e * S1)
    c3lo := imin 0 c3, c3hi := imax 0 c3
    c6lo := imin (p.D * T0) (p.D * T1), c6hi := imax (p.D * T0) (p.D * T1) }

/-- Upper bound for `E · ONE` at one value of `v` (given by `w6, w4, w30`). -/
def evalE (rc : RunC) (w6 w4 w30 : Int) : Int :=
  rc.k0 + sel w6 rc.c4lo rc.c4hi + sel w4 rc.c3lo rc.c3hi + sel w30 rc.c6lo rc.c6hi

/-- Contribution `LL · (ONE - min(ONE, ub))` of one interval, `ub` = max over the two ends of the v-range. -/
def ivGain (rc : RunC) (iv : Ivl) : Int :=
  iv.LL * (ONE - imin ONE (imax (evalE rc iv.w6l iv.w4l iv.w30l) (evalE rc iv.w6h iv.w4h iv.w30h)))

/-- Process `len` intervals of one run; `none` = trivial bound. Returns the remaining intervals and the gain.
A polynomial bound is accepted only on intervals with `θ_{i+1} < π/2` (where `q > 0`). -/
def runGain (orc : Option RunC) : Nat → List Ivl → Int → Option (List Ivl × Int)
  | 0, ivs, g => some (ivs, g)
  | _ + 1, [], _ => none
  | len + 1, iv :: ivs, g =>
    match orc with
    | none => runGain orc len ivs g
    | some rc => match ilt iv.TR P32 with
      | true => runGain orc len ivs (g + ivGain rc iv)
      | false => none

/-- Process all runs of a leaf. -/
def runsGain (lib : LibT) (S0 S1 T0 T1 : Int) : List (Int × Nat) → List Ivl → Int → Option (List Ivl × Int)
  | [], ivs, g => some (ivs, g)
  | (j, len) :: rs, ivs, g =>
    let orc : Option (Option RunC) := match j with
      | .negSucc _ => some none
      | .ofNat jn => (lib.get jn).map (fun p => some (mkRunC p S0 S1 T0 T1))
    match orc with
    | none => none
    | some o =>
      match runGain o len ivs g with
      | none => none
      | some (ivs', g') => runsGain lib S0 S1 T0 T1 rs ivs' g'

/-- Threshold: `gain ≥ (π_hi/2 - 71/50) · 2^64 · ONE` with `π_hi = 3.141593`, i.e.
`gain · 10^7 ≥ 1507965 · 2^64 · ONE`. -/
def gainOK (g : Int) : Bool := ile THR (g * 10000000)

theorem THR_eq : THR = 1507965 * P64 * ONE := by decide

/-- Check of one leaf square `[i/2^l, (i+1)/2^l] × [k/2^l, (k+1)/2^l]` in the `(P4, P6)` plane, with the
dyadic bound `R/2^60 ≥ s1^{3/2}` and the run list of polynomial indices. -/
def checkLeaf (lib : LibT) (ivs : List Ivl) (l i k R : Nat) (runs : List (Int × Nat)) : Bool :=
  let sh : Nat := 2 ^ (60 - l)
  let S0 : Int := (i * sh : Nat)
  let S1 : Int := ((i + 1) * sh : Nat)
  let T0 : Int := imax ((k * sh : Nat) : Int) ((i * i * 2 ^ (60 - 2 * l) : Nat) : Int)
  let T1 : Int := imin (((k + 1) * sh : Nat) : Int) (R : Int)
  decide (l ≤ 30) && decide (S1 * S1 * S1 ≤ (R : Int) * R * P60) &&
    match runsGain lib S0 S1 T0 T1 runs ivs 0 with
    | none => false
    | some (rest, g) => rest.isEmpty && gainOK g

/-- Outside square test: the square misses `R = {s² ≤ t ≤ s^{3/2}}`, i.e. `t1 < s0²` or `t0² > s1³`. -/
def outsideOK (l i k : Nat) : Bool :=
  decide ((k + 1) * 2 ^ l < i * i) || decide ((i + 1) * (i + 1) * (i + 1) < k * k * 2 ^ l)

/-- Quadtree over `[0,1]²`: outside squares, leaf squares (with `R` and runs), and subdivided squares. -/
inductive QT where
  | out : QT
  | leaf : Nat → List (Int × Nat) → QT
  | node : QT → QT → QT → QT → QT

/-- Bool check of a whole quadtree (used by the native track). Children of `(l, i, k)`: `(l+1, 2i+a, 2k+b)`
in the order `(a,b) = (0,0), (0,1), (1,0), (1,1)`. -/
def QT.check (lib : LibT) (ivs : List Ivl) : QT → Nat → Nat → Nat → Bool
  | .out, l, i, k => outsideOK l i k
  | .leaf R runs, l, i, k => checkLeaf lib ivs l i k R runs
  | .node a b c d, l, i, k =>
    a.check lib ivs (l + 1) (2 * i) (2 * k) && b.check lib ivs (l + 1) (2 * i) (2 * k + 1) &&
      c.check lib ivs (l + 1) (2 * i + 1) (2 * k) && d.check lib ivs (l + 1) (2 * i + 1) (2 * k + 1)

/-- Prop version for sharded proofs (each leaf proved by its own theorem). -/
def QT.OK (lib : LibT) (ivs : List Ivl) : QT → Nat → Nat → Nat → Prop
  | .out, l, i, k => outsideOK l i k = true
  | .leaf R runs, l, i, k => checkLeaf lib ivs l i k R runs = true
  | .node a b c d, l, i, k =>
    a.OK lib ivs (l + 1) (2 * i) (2 * k) ∧ b.OK lib ivs (l + 1) (2 * i) (2 * k + 1) ∧
      c.OK lib ivs (l + 1) (2 * i + 1) (2 * k) ∧ d.OK lib ivs (l + 1) (2 * i + 1) (2 * k + 1)

theorem QT.OK_of_check (lib : LibT) (ivs : List Ivl) :
    ∀ (t : QT) (l i k : Nat), t.check lib ivs l i k = true → t.OK lib ivs l i k
  | .out, l, i, k, h => h
  | .leaf R runs, l, i, k, h => h
  | .node a b c d, l, i, k, h => by
    simp only [QT.check, Bool.and_eq_true] at h
    exact ⟨QT.OK_of_check lib ivs a _ _ _ h.1.1.1, QT.OK_of_check lib ivs b _ _ _ h.1.1.2,
      QT.OK_of_check lib ivs c _ _ _ h.1.2, QT.OK_of_check lib ivs d _ _ _ h.2⟩

end Poincare11a.Cert
