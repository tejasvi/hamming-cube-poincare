#!/usr/bin/env python3
"""Checker for the moment certificate of K = sup_lambda J(lambda) <= claimed (L^1 Poincare constant on the Hamming
cube; constant 11a of the optimization-constants repository).

Usage: python3 check11a_mom.py CERT.json
Needs python-flint (arb interval arithmetic) and the standard library; shares no code with the search.
Every check is an assert statement, so the program refuses to run under python -O.

Mathematics checked ((L1)-(L4) are Lemmas 3.1-3.4 of the paper, (L5) is Proposition 4.1):
 (L1) xi = xi^(p): sqrt((1-p)/p) w.p. p, -sqrt(p/(1-p)) w.p. 1-p; q = p(1-p). Closed forms
      mu4 = (1-3q)/q, mu3^2 = (1-4q)/q, mu6 = (1-5q+5q^2)/q^2 are verified here as exact identities.
 (L2) For S = sum lambda_j xi_j, |lambda| = 1, P_r = sum lambda_j^r: E S^4 = 3 + k4 P4,
      E S^6 = 15 + 15 k4 P4 + 10 mu3^2 P3^2 + k6 P6, k4 = mu4 - 3, k6 = mu6 - 15 mu4 - 10 mu3^2 + 30
      (cumulant additivity; spot-checked here by exact enumeration).
 (L3) If h(z) = a + b z^2 + c z^4 + d z^6 >= |z| on R then E|S| <= a + b + c E S^4 + d E S^6; with E|S| <= 1 always.
      Each library polynomial is verified: H(u) = a - u + b u^2 + c u^4 + d u^6 > 0 on [0, inf) (exact Sturm count).
 (L4) (P4, P6) in R = {0 <= P4 <= 1, P4^2 <= P6 <= P4^(3/2)} and P3^2 <= P4 for unit lambda.
 (L5) J(lambda) = int_0^(pi/2) E|S_theta| dtheta, p = (1 + sin theta)/2, q = cos(theta)^2/4. The certificate's dyadic
      boxes tile [0,1]^2; boxes listed as outside miss R; for each leaf box and each theta interval
      I_i = [i pi/(2N), (i+1) pi/(2N)] the listed polynomial bounds E|S| on I_i x box; sum_i |I_i| min(1, bound) <= claimed.
"""
import sys, json, itertools, random
from fractions import Fraction as F
import flint
from flint import arb, ctx

if not __debug__:
    sys.exit('check11a_mom.py: run without -O (the checks are assert statements)')

ctx.prec = 200


# ---------- (L1) closed forms as exact identities ----------
def check_closed_forms():
    for k in range(1, 40):
        p = F(1, 2) + F(k, 81)  # p in (1/2, 1)
        if p >= 1:
            continue
        q = p * (1 - p)
        a2, b2 = (1 - p) / p, p / (1 - p)          # a^2, b^2; a*b = -1
        mu4 = p * a2 ** 2 + (1 - p) * b2 ** 2
        mu6 = p * a2 ** 3 + (1 - p) * b2 ** 3
        mu3sq = p * p * a2 ** 3 + 2 * p * (1 - p) * (-1) + (1 - p) ** 2 * b2 ** 3   # (p a^3 + (1-p) b^3)^2, (ab)^3 = -1
        assert mu4 == (1 - 3 * q) / q
        assert mu6 == (1 - 5 * q + 5 * q * q) / (q * q)
        assert mu3sq == (1 - 4 * q) / q
    # each identity is between rational functions of p of degree <= 12 after clearing denominators; 39 points suffice


# ---------- (L2) spot check of the moment formulas by exact enumeration ----------
def check_moment_formula():
    rnd = random.Random(1)
    for trial in range(30):
        n = rnd.randint(1, 4)
        lam = [F(rnd.randint(-9, 9), rnd.randint(1, 5)) for _ in range(n)]
        if all(l == 0 for l in lam):
            continue
        p = F(rnd.randint(51, 99), 100)
        q = p * (1 - p)
        # exact: use sqrt-free scaling: xi in {s*(1-p), -s*p} with s = 1/sqrt(q): E S^r = s^r E (sum lam_j u_j)^r
        vals = [(1 - p, p), (-p, 1 - p)]   # (unscaled value, prob)
        mom = {4: F(0), 6: F(0), 2: F(0)}
        for choice in itertools.product(range(2), repeat=n):
            v = sum(l * vals[c][0] for l, c in zip(lam, choice))
            w = F(1)
            for c in choice:
                w *= vals[c][1]
            for r in mom:
                mom[r] += w * v ** r
        P2 = sum(l * l for l in lam)
        P3 = sum(l ** 3 for l in lam)
        P4 = sum(l ** 4 for l in lam)
        P6 = sum(l ** 6 for l in lam)
        mu4 = (1 - 3 * q) / q
        mu6 = (1 - 5 * q + 5 * q * q) / (q * q)
        mu3sq = (1 - 4 * q) / q
        k4 = mu4 - 3
        k6 = mu6 - 15 * mu4 - 10 * mu3sq + 30
        # scaled moments: E S^r = mom[r] / q^(r/2)
        assert mom[2] / q == P2
        assert mom[4] / q ** 2 == 3 * P2 ** 2 + k4 * P4
        assert mom[6] / q ** 3 == 15 * P2 ** 3 + 15 * k4 * P4 * P2 + 10 * mu3sq * P3 ** 2 + k6 * P6


# ---------- (L3) exact Sturm check ----------
def poly_rem(f, g):
    f = f[:]
    while len(f) >= len(g):
        if f[-1] == 0:
            f.pop()
            continue
        k = f[-1] / g[-1]
        s = len(f) - len(g)
        for i, gi in enumerate(g):
            f[s + i] -= k * gi
        f.pop()
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return f


def positive_on_halfline(a, b, c, d):
    """True iff H(u) = a - u + b u^2 + c u^4 + d u^6 > 0 for all u >= 0 (exact)."""
    if not (d > 0 and a > 0):
        return False
    H = [a, F(-1), b, F(0), c, F(0), d]
    dH = [i * H[i] for i in range(1, 7)]
    seq = [H, dH]
    while True:
        r = poly_rem(seq[-2], seq[-1])
        if all(x == 0 for x in r):
            break
        seq.append([-x for x in r])
        if len(seq[-1]) == 1:
            break

    def sgn_at_0plus(p):
        for x in p:
            if x != 0:
                return 1 if x > 0 else -1
        return 0

    def sgn_at_inf(p):
        for x in reversed(p):
            if x != 0:
                return 1 if x > 0 else -1
        return 0

    def var(s):
        s = [x for x in s if x != 0]
        return sum(1 for i in range(1, len(s)) if s[i] != s[i - 1])

    roots = var([sgn_at_0plus(p) for p in seq]) - var([sgn_at_inf(p) for p in seq])
    # roots = number of distinct real roots in (0, inf) (H(0) = a != 0)
    return roots == 0


# ---------- (L5) tiling ----------
def check_tiling(leaves, outside):
    members = {}
    for code in leaves:
        members[tuple(code)] = 'leaf'
    for code in outside:
        assert tuple(code) not in members
        members[tuple(code)] = 'out'
    visited = 0
    stack = [(0, 0, 0)]
    while stack:
        l, i, j = stack.pop()
        if (l, i, j) in members:
            visited += 1
            continue
        assert l < 40, 'tiling does not close'
        for di in (0, 1):
            for dj in (0, 1):
                stack.append((l + 1, 2 * i + di, 2 * j + dj))
    assert visited == len(members), 'overlapping boxes'


def box_of(code):
    l, i, j = code
    s = F(1, 2 ** l)
    return i * s, (i + 1) * s, j * s, (j + 1) * s


def outside_region(code):
    a, b, c, d = box_of(code)
    # all points miss R iff d < a^2 (P6 < P4^2) or c > b^(3/2) (P6 > P4^(3/2)), i.e. c^2 > b^3
    return d < a * a or c * c > b ** 3


def A_(x):
    """exact rational -> arb point"""
    x = F(x)
    return arb(flint.fmpq(x.numerator, x.denominator))


def main():
    cert = json.load(open(sys.argv[1]))
    claimed = F(cert['claimed'])
    assert isinstance(cert['claimed'], str)
    N = cert['N']
    assert isinstance(N, int) and N >= 1, 'N must be a positive integer'
    check_closed_forms()
    check_moment_formula()
    lib = [tuple(F(x) for x in co) for co in cert['library']]
    for co in lib:
        assert positive_on_halfline(*co), 'invalid library polynomial'
    print(f'library: {len(lib)} polynomials verified (exact Sturm)', flush=True)
    check_tiling([lf[0] for lf in cert['leaves']], cert['outside'])
    for code in cert['outside']:
        assert outside_region(tuple(code)), f'box {code} not outside R'
    print(f'tiling: {len(cert["leaves"])} leaves + {len(cert["outside"])} outside boxes tile [0,1]^2; outside boxes miss R',
          flush=True)
    pi = arb.pi()
    width = pi / (2 * N)
    # q enclosure per theta interval (q decreasing in theta)
    qint = []
    for i in range(N):
        ta, tb = pi * i / (2 * N), pi * (i + 1) / (2 * N)
        qhi = (ta.cos() ** 2) / 4
        qlo = (tb.cos() ** 2) / 4
        qint.append(qlo.union(qhi))
    worst = None
    for code, idx in cert['leaves']:
        assert len(idx) == N
        a, b, c, d = box_of(tuple(code))
        P4 = A_(a).union(A_(b))
        # clip P6 to R: P6 in [max(c, a^2), min(d, b^(3/2))]
        c6 = max(c, a * a)
        d6u = A_(b).sqrt() * A_(b)
        P6lo = A_(c6)
        P6hi = A_(d) if A_(d) < d6u else d6u
        P6 = P6lo.union(P6hi)
        P3sq = A_(0).union(A_(b))
        total = arb(0)
        for i in range(N):
            j = idx[i]
            if j < 0:
                total += width
                continue
            q = qint[i]
            assert q > 0, 'polynomial bound used on an interval reaching q = 0'
            mu4 = (1 - 3 * q) / q
            mu3sq = (1 - 4 * q) / q
            mu6 = (1 - 5 * q + 5 * q * q) / (q * q)
            k4 = mu4 - 3
            k6 = mu6 - 15 * mu4 - 10 * mu3sq + 30
            m4 = 3 + k4 * P4
            m6 = 15 + 15 * k4 * P4 + 10 * mu3sq * P3sq + k6 * P6
            A, B, C, D = (A_(x) for x in lib[j])
            ub = A + B + C * m4 + D * m6
            assert ub.is_finite()
            u = ub.upper()
            total += width * (u if u < 1 else arb(1))
        assert total.is_finite()
        tu = total.upper()
        if worst is None or tu > worst:
            worst = tu
        assert tu <= A_(claimed), f'leaf {code}: bound {total} exceeds claimed {claimed}'
    print(f'all {len(cert["leaves"])} leaves: sum_i |I_i| min(1, bound) <= claimed; worst {worst}', flush=True)
    print(f'RESULT: PASS  K = sup_lambda J(lambda) <= {claimed}  hence C_11a <= {claimed}')


if __name__ == '__main__':
    main()
