#!/usr/bin/env python3
"""Certified bound K = sup_lambda J(lambda) <= c via 6-moment dual polynomials and a B&B over power sums (search side).

Usage: mom_bb.py C_TARGET OUT.json [N_THETA]
For a unit vector lambda put P4 = sum lambda^4, P6 = sum lambda^6, P3 = sum lambda^3; then (P4, P6) lies in
R = {0 <= P4 <= 1, P4^2 <= P6 <= P4^(3/2)} and P3^2 <= P4. With q = cos^2(theta)/4:
  m4 = E S^4 = 3 + k4 P4,  m6 = E S^6 = 15 + 15 k4 P4 + 10 k3sq P3^2 + k6 P6,
  k3sq = (1-4q)/q, k4 = (1-6q)/q, k6 = (1-30q+120q^2)/q^2,
and E|S| <= min(1, a + b + c m4 + d m6) for every polynomial h(z) = a + b z^2 + c z^4 + d z^6 >= |z|.
J(lambda) <= sum_i |I_i| sup_{theta in I_i} min(1, ...). The B&B covers R by dyadic boxes; for each leaf and theta
interval it records the index of the library polynomial used (-1 = trivial bound 1).
"""
import sys, json, math, time
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog


# ---------------- polynomial library ----------------
def dual_lp(m4, m6, U, A):
    res = linprog([1, 1, m4, m6], A_ub=A, b_ub=-U, bounds=[(None, None), (None, None), (None, None), (1e-9, None)],
                  method='highs')
    return None if res.x is None else res.x


def H_eval(co, u):
    a, b, c, d = co
    return a - u + b * u ** 2 + c * u ** 4 + d * u ** 6


def sturm_no_pos_root(co):
    """Exact: H(u) = a - u + b u^2 + c u^4 + d u^6 has no root in [0, inf) and d > 0 (so H > 0 there)."""
    a, b, c, d = co
    if not (d > 0 and a > 0):
        return False
    P = [a, Fraction(-1), b, Fraction(0), c, Fraction(0), d]   # coefficients by degree

    def trim(p):
        while len(p) > 1 and p[-1] == 0:
            p = p[:-1]
        return p

    def deriv(p):
        return trim([i * p[i] for i in range(1, len(p))]) or [Fraction(0)]

    def rem(f, g):
        f = list(f)
        while len(f) >= len(g) and any(f):
            k = f[-1] / g[-1]
            s = len(f) - len(g)
            for i in range(len(g)):
                f[s + i] -= k * g[i]
            f = trim(f[:-1]) if len(f) > 1 else f
            if len(f) < len(g):
                break
        return trim(f)

    seq = [trim(P), deriv(P)]
    while len(seq[-1]) > 1 or seq[-1][0] != 0:
        r = rem(seq[-2], seq[-1])
        if len(r) == 1 and r[0] == 0:
            break
        seq.append([-x for x in r])
        if len(seq[-1]) == 1:
            break

    def signs_at_zero():
        out = []
        for p in seq:
            v = p[0]
            if v == 0:
                # use next nonzero coefficient sign (value just above 0)
                for x in p[1:]:
                    if x != 0:
                        v = x
                        break
            out.append(1 if v > 0 else -1 if v < 0 else 0)
        return out

    def signs_at_inf():
        return [1 if p[-1] > 0 else -1 for p in seq]

    def changes(s):
        s = [x for x in s if x != 0]
        return sum(1 for i in range(1, len(s)) if s[i] != s[i - 1])

    return changes(signs_at_zero()) - changes(signs_at_inf()) == 0


def make_library(grid4, grid6):
    U = np.concatenate([np.linspace(0, 4, 1601), np.linspace(4.01, 80, 2000)])
    A = -np.column_stack([np.ones_like(U), U ** 2, U ** 4, U ** 6])
    uu = np.linspace(0, 200, 400001)
    lib = []
    for m4 in grid4:
        for m6 in grid6(m4):
            x = dual_lp(m4, m6, U, A)
            if x is None:
                continue
            D = 2 ** 40
            b, c, d = (Fraction(round(v * D), D) for v in x[1:])
            if d <= 0:
                continue
            Hb = -uu + float(b) * uu ** 2 + float(c) * uu ** 4 + float(d) * uu ** 6
            a_need = -Hb.min()
            a = Fraction(math.ceil((a_need + 1e-10) * D), D)
            ok = sturm_no_pos_root((a, b, c, d))
            tries = 0
            while not ok and tries < 5:
                a += Fraction(1, 10 ** 8)
                ok = sturm_no_pos_root((a, b, c, d))
                tries += 1
            if ok:
                lib.append((a, b, c, d))
    return lib


# ---------------- bounds ----------------
def kappa_ranges(qlo, qhi):
    """Ranges of k3sq, k4, k6 for q in [qlo, qhi] (0 < qlo): monotone in x = 1/q; k6 = (x-15)^2 - 105."""
    xlo, xhi = 1 / qhi, 1 / qlo
    k3 = (xlo - 4, xhi - 4)
    k4 = (xlo - 6, xhi - 6)
    lo = 0.0 if xlo <= 15 <= xhi else min((xlo - 15) ** 2, (xhi - 15) ** 2)
    k6 = (lo - 105, max((xlo - 15) ** 2, (xhi - 15) ** 2) - 105)
    return k3, k4, k6


def mul_rng(r, s):
    v = [r[0] * s[0], r[0] * s[1], r[1] * s[0], r[1] * s[1]]
    return min(v), max(v)


def box_bound(box, Qs, LIB, need_idx=False):
    """box = (P4lo, P4hi, P6lo, P6hi). Returns (sum over theta intervals of len*bound, indices)."""
    P4 = (box[0], box[1])
    P6 = (box[2], box[3])
    P3 = (0.0, box[1])
    tot = 0.0
    idx = []
    for (qlo, qhi, ln) in Qs:
        if qlo <= 0:
            tot += ln
            idx.append(-1)
            continue
        k3, k4, k6 = kappa_ranges(qlo, qhi)
        t4 = mul_rng(k4, P4)
        m4 = (3 + t4[0], 3 + t4[1])
        t6a = (15 * t4[0], 15 * t4[1])
        t6b = mul_rng(k3, P3)
        t6c = mul_rng(k6, P6)
        m6 = (15 + t6a[0] + 10 * t6b[0] + t6c[0], 15 + t6a[1] + 10 * t6b[1] + t6c[1])
        a, b, c, d = LIB
        val = a + b + np.where(c < 0, c * m4[0], c * m4[1]) + np.where(d > 0, d * m6[1], d * m6[0])
        j = int(np.argmin(val))
        v = val[j]
        if v >= 1:
            tot += ln
            idx.append(-1)
        else:
            tot += ln * v
            idx.append(j)
    return tot, idx


def main():
    c_target = float(sys.argv[1])
    out = sys.argv[2]
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 512
    t0 = time.time()
    grid4 = list(np.linspace(1.0, 3.0, 41)) + list(np.linspace(3.1, 8.0, 15))
    grid6 = lambda m4: [math.exp(v) for v in np.linspace(math.log(max(m4 * m4, 1.0) + 1e-3), math.log(600), 45)]
    lib = make_library(grid4, grid6)
    print(f'library: {len(lib)} verified polynomials; {time.time()-t0:.0f}s', flush=True)
    LIBf = tuple(np.array([float(co[i]) for co in lib]) for i in range(4))
    # theta intervals and q ranges (float, slightly widened)
    Qs = []
    for i in range(N):
        ta, tb = (math.pi / 2) * i / N, (math.pi / 2) * (i + 1) / N
        qlo, qhi = math.cos(tb) ** 2 / 4, math.cos(ta) ** 2 / 4
        if i == N - 1:
            qlo = 0.0
        Qs.append((qlo * (1 - 1e-12), qhi * (1 + 1e-12), tb - ta))
    # quadtree B&B over [0,1]^2 in (P4, P6)
    margin = 2e-4
    stack = [(0, 0, 0)]  # (level, i, j) dyadic box [i/2^l, (i+1)/2^l] x [j/2^l, (j+1)/2^l]
    leaves, outside, worst = [], [], 0.0
    while stack:
        l, i, j = stack.pop()
        s = 2.0 ** -l
        a, b, cc, d = i * s, (i + 1) * s, j * s, (j + 1) * s
        if d < a * a or cc > b ** 1.5:
            outside.append((l, i, j))
            continue
        bb = (a, b, max(cc, a * a), min(d, b ** 1.5, b))
        v, idx = box_bound(bb, Qs, LIBf)
        if v <= c_target - margin:
            leaves.append(((l, i, j), idx, v))
            worst = max(worst, v)
            continue
        if l >= 22:
            raise SystemExit(f'cannot certify box {(l, i, j)}: bound {v}')
        for di in (0, 1):
            for dj in (0, 1):
                stack.append((l + 1, 2 * i + di, 2 * j + dj))
    print(f'leaves {len(leaves)}, outside {len(outside)}, worst leaf bound {worst:.6f}; {time.time()-t0:.0f}s', flush=True)
    cert = {'claimed': str(Fraction(c_target).limit_denominator(10 ** 6)), 'N': N,
            'library': [[str(x) for x in co] for co in lib],
            'leaves': [[list(code), idx] for code, idx, v in leaves],
            'outside': [list(code) for code in outside]}
    json.dump(cert, open(out, 'w'))


if __name__ == '__main__':
    main()
