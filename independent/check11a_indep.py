#!/usr/bin/env python3
"""Second checker for the moment certificate K = sup_lambda J(lambda) <= claimed (L^1 Poincare constant on the Hamming
cube; constant 11a of the optimization-constants repository). It uses methods different from the first checker's for
the polynomial test, the tiling test and the bound; the outside-box test and the moment self-test follow the same
approach as the first checker's.

usage: check11a_indep.py CERT.json [QSPLIT]          (exit status 0 iff every check passes)

Methods:
 * library (method different from the first checker): h(z) >= |z| <=> H(u) = a - u + b u^2 + c u^4 + d u^6 > 0 on
   [0, inf); checked by certified complex root isolation of the integer-scaled H (python-flint fmpz_poly.complex_roots;
   real roots come out with zero imaginary part): no real root with nonnegative real part, H(0) = a > 0, d > 0;
 * tiling (method different from the first checker): dyadic codes pairwise non-nested (no code is an ancestor of
   another) and total area exactly 1;
 * outside boxes: exact rational tests of max P6 < min P4^2 or min P6 > max P4^{3/2};
 * bound (method different from the first checker): for fixed q, ub = A + B + C m4 + D m6 is affine in (P4, P3^2, P6):
       ub = [A + B + 3C + 15D] + [(C + 15D) k4] P4 + [10 D mu3^2] P3^2 + [D k6] P6,
   so its maximum over the box is taken exactly at the right corner (sign of each coefficient); only the q-dependence is
   enclosed by interval arithmetic, on QSPLIT sub-intervals of each theta interval (default 4). Where an interval reaches
   q = 0 the trivial bound E|S| <= 1 is used instead (always valid).
 * moment formulas from cumulants: k4 = 1/q - 6, k6 = 1/q^2 - 30/q + 120, mu3^2 = 1/q - 4 (q = p(1-p)), and an exact-
   enumeration test of E S^4, E S^6 for random small lambda (p rational, values scaled by sqrt(q)).
 * input validation: claimed is a rational string, N is an integer >= 1, every leaf has a valid dyadic code and an index
   list of length N with entries in [-1, len(library)) (-1 = trivial bound), every outside code is a valid dyadic code.
No assert statements are used: every check sets the exit status, so python -O does not change the result.
Prints per-leaf totals and the worst; exit 0 iff every leaf total <= claimed and all structural checks pass.
"""
import json
import random
import sys
import itertools
from fractions import Fraction as F
from math import lcm

from flint import arb, fmpq, fmpz_poly, ctx

ctx.prec = 200


def A(x):
    x = F(x)
    return arb(fmpq(x.numerator, x.denominator))


def H_positive(a, b, c, d):
    if not (a > 0 and d > 0):
        return False
    co = [a, F(-1), b, F(0), c, F(0), d]
    L = 1
    for x in co:
        L = lcm(L, x.denominator)
    P = fmpz_poly([int(x * L) for x in co])
    for r, m in P.complex_roots():
        if r.imag.is_zero():                  # certified real root
            if not (r.real < 0):              # positive, or not certainly negative -> reject
                return False
    return True


def moment_test():
    rnd = random.Random(7)
    for _ in range(40):
        n = rnd.randint(1, 5)
        lam = [F(rnd.randint(-7, 7), rnd.randint(1, 4)) for _ in range(n)]
        if not any(lam):
            continue
        p = F(rnd.randint(51, 98), 100); q = p * (1 - p)
        # xi * sqrt(q) takes 1-p (prob p) and -p (prob 1-p)
        M = {2: F(0), 4: F(0), 6: F(0)}
        for ch in itertools.product((0, 1), repeat=n):
            v = sum(l * ((1 - p) if c == 0 else -p) for l, c in zip(lam, ch))
            w = F(1)
            for c in ch:
                w *= p if c == 0 else (1 - p)
            for r in M:
                M[r] += w * v ** r
        P2 = sum(l ** 2 for l in lam); P3 = sum(l ** 3 for l in lam); P4 = sum(l ** 4 for l in lam); P6 = sum(l ** 6 for l in lam)
        k4 = 1 / q - 6; k6 = 1 / q ** 2 - 30 / q + 120; m3s = 1 / q - 4
        if not (M[2] / q == P2 and M[4] / q ** 2 == 3 * P2 ** 2 + k4 * P4 and
                M[6] / q ** 3 == 15 * P2 ** 3 + 15 * k4 * P4 * P2 + 10 * m3s * P3 ** 2 + k6 * P6):
            return False
    return True


def tiling_ok(codes):
    S = set(map(tuple, codes))
    if len(S) != len(codes):
        return False, 'duplicate codes'
    area = F(0)
    for (l, i, j) in S:
        if not (0 <= i < 2 ** l and 0 <= j < 2 ** l):
            return False, 'code out of range'
        area += F(1, 4 ** l)
        # no ancestor of (l, i, j) is in S
        ll, ii, jj = l, i, j
        while ll > 0:
            ll, ii, jj = ll - 1, ii // 2, jj // 2
            if (ll, ii, jj) in S:
                return False, 'nested codes'
    return area == 1, 'area %s' % area


def valid_code(c):
    return (isinstance(c, list) and len(c) == 3 and all(isinstance(x, int) and not isinstance(x, bool) for x in c)
            and 0 <= c[0] <= 60 and 0 <= c[1] < 2 ** c[0] and 0 <= c[2] < 2 ** c[0])


def validate(cert):
    """'' if the certificate has the expected shape, else a reason."""
    if not isinstance(cert.get('claimed'), str):
        return 'claimed must be a rational string'
    try:
        F(cert['claimed'])
    except (ValueError, ZeroDivisionError):
        return 'claimed is not a rational'
    N = cert.get('N')
    if not (isinstance(N, int) and not isinstance(N, bool) and N >= 1):
        return 'N must be an integer >= 1'
    lib = cert.get('library')
    if not (isinstance(lib, list) and all(isinstance(co, list) and len(co) == 4 for co in lib)):
        return 'library must be a list of 4-coefficient lists'
    L = len(lib)
    lv = cert.get('leaves')
    if not (isinstance(lv, list) and lv):
        return 'leaves must be a nonempty list'
    for e in lv:
        if not (isinstance(e, list) and len(e) == 2 and valid_code(e[0]) and isinstance(e[1], list) and len(e[1]) == N):
            return 'leaf entry must be [code, index list of length N]'
        if not all(isinstance(j, int) and not isinstance(j, bool) and -1 <= j < L for j in e[1]):
            return 'leaf index out of range'
    if not (isinstance(cert.get('outside'), list) and all(valid_code(c) for c in cert['outside'])):
        return 'outside must be a list of dyadic codes'
    return ''


def box(code):
    l, i, j = code
    s = F(1, 2 ** l)
    return i * s, (i + 1) * s, j * s, (j + 1) * s


def main():
    cert = json.load(open(sys.argv[1]))
    QS = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    msg = validate(cert)
    if msg:
        print('FAIL: malformed certificate:', msg)
        print('RESULT: FAIL')
        return False
    claimed = F(cert['claimed']); N = cert['N']
    ok = True
    if not moment_test():
        print('FAIL: moment formulas'); ok = False
    lib = [tuple(F(x) for x in co) for co in cert['library']]
    bad = [k for k, co in enumerate(lib) if not H_positive(*co)]
    print('library: %d polynomials, %d rejected by root isolation' % (len(lib), len(bad)), flush=True)
    if bad:
        ok = False
    codes = [lf[0] for lf in cert['leaves']] + cert['outside']
    t_ok, msg = tiling_ok(codes)
    print('tiling (non-nested + area 1):', t_ok, msg, flush=True)
    ok &= t_ok
    for code in cert['outside']:
        a, b, c, d = box(tuple(code))
        if not (d < a * a or c * c > b ** 3):
            print('FAIL: outside box meets R', code); ok = False
    # q sub-intervals: theta in [i pi/2N, (i+1) pi/2N], split into QS pieces; q = cos(theta)^2/4 decreasing
    pi = arb.pi()
    qpieces = []
    for i in range(N):
        pcs = []
        for k in range(QS):
            ta = pi * (QS * i + k) / (2 * N * QS); tb = pi * (QS * i + k + 1) / (2 * N * QS)
            pcs.append((tb.cos() ** 2 / 4).union(ta.cos() ** 2 / 4))
        qpieces.append(pcs)
    width = pi / (2 * N)
    worst = None; totals = []
    for code, idx in cert['leaves']:
        a, b, c, d = box(tuple(code))
        c6 = max(c, a * a)
        b32 = A(b).sqrt() * A(b)
        d6 = A(d) if A(d) < b32 else arb(b32.upper())
        tot = arb(0)
        for i in range(N):
            j = idx[i]
            if j < 0:
                tot += width
                continue
            Ac, Bc, Cc, Dc = (A(x) for x in lib[j])
            ubmax = None
            for q in qpieces[i]:
                if not (q > 0):
                    ubmax = arb('inf'); break
                k4 = 1 / q - 6; k6 = 1 / (q * q) - 30 / q + 120; m3s = 1 / q - 4
                const = Ac + Bc + 3 * Cc + 15 * Dc
                al = (Cc + 15 * Dc) * k4; be = 10 * Dc * m3s; ga = Dc * k6
                # exact maximisation of the affine part over the box corners (coefficients are balls: take both ends)
                def mx(coef, lo, hi):
                    return (coef * A(lo)).union(coef * A(hi)).upper() if isinstance(lo, F) else (coef * A(lo)).union(coef * hi).upper()
                v = const.upper() + mx(al, a, b) + mx(be, F(0), b) + (ga * A(c6)).union(ga * d6).upper()
                v = arb(v)
                if not v.is_finite():
                    ubmax = arb('inf'); break
                ubmax = v if ubmax is None else arb(max(v.upper(), ubmax.upper()))   # max of exact upper ends
            u = ubmax.upper() if ubmax.is_finite() else arb(1)
            tot += width * (u if u < 1 else arb(1))
        tu = tot.upper()
        totals.append((float(tu), code))
        if not (tu <= A(claimed)):
            print('FAIL: leaf', code, float(tu)); ok = False
        worst = tu if worst is None or tu > worst else worst
    totals.sort(reverse=True)
    print('leaves: %d; worst total %s; top 5: %s' % (len(totals), worst.str(15), totals[:5]), flush=True)
    print('RESULT:', 'PASS' if ok else 'FAIL', '(claimed %s)' % claimed)
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
