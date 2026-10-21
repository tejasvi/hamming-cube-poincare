#!/usr/bin/env python3
"""Lower bound for int_0^{pi/2} R(p(theta)) dtheta, R(p) = sup over unit vectors of E|sum_j lambda_j xi_j^(p)|.

Not part of any proof in the paper; it supports the remark that bounding E|sum_j lambda_j xi_j| by R(p) separately for
each p cannot give a constant below 1.4217.

For p in (1/2, 1) put x = 1 - p = (1 - sin theta)/2. Equal weights lambda = (1, ..., 1)/sqrt(n) give
E|n^{-1/2} sum_{j<=n} xi_j| = E|K - n p| / sqrt(n p (1-p)) with K ~ Bin(n, p). If n x <= 1, the only value of n - K below
its mean n x is 0, so E|K - n p| = 2 n x (1-x)^n and
    f_n(x) := E|n^{-1/2} sum_{j<=n} xi_j| = 2 sqrt(n x) (1-x)^(n - 1/2)        (n x <= 1).
R(p) >= f_n(x) for every n. On an interval [theta_a, theta_b] we take n = N(x_a) := floor(1 / (2 x_a - x_a^2)), where
x_a = x(theta_a) is the largest value of x on the interval, so that n x <= 1 throughout. log f_n is concave in x, so
f_n is unimodal and its minimum over [x_b, x_a] is min(f_n(x_a), f_n(x_b)). Summing width * min over the intervals,
with arb ball arithmetic, gives a certified lower bound. (N(x) is the maximizer found by Stone; for the lower bound any
n with n x <= 1 is admissible.)

Part 2 compares, at the interval midpoints, f_N with a brute-force maximum over n of the exact binomial expression
(double precision), as a check that N(x) is the maximizing n.
"""
import math
import sys
import time

from flint import arb, ctx

ctx.prec = 128


def N_of(x):
    return int(math.floor(1.0 / (2.0 * x - x * x)))


def f_arb(n, x):
    # 2 sqrt(n x) (1-x)^(n - 1/2) = 2 sqrt(n x) exp((n - 1/2) log(1 - x))
    return 2 * (n * x).sqrt() * ((n - arb(1) / 2) * (1 - x).log()).exp()


def certified_lower(M, theta_max_gap):
    """Uniform split of [0, pi/2 - gap] into M intervals; returns a certified lower bound (arb upper/lower handled)."""
    pi = arb.pi()
    top = pi / 2 - arb(theta_max_gap)
    total = arb(0)
    for i in range(M):
        ta = top * i / M
        tb = top * (i + 1) / M
        xa = (1 - ta.sin()) / 2           # larger x (x decreases in theta)
        xb = (1 - tb.sin()) / 2
        xa_f = float(xa.mid())
        n = N_of(xa_f)
        # safety: make sure n * xa <= 1 rigorously (floor in floats could be off by one at the boundary)
        while not (n * xa <= 1):
            n -= 1
        assert n >= 1
        fa = f_arb(n, xa)
        fb = f_arb(n, xb)
        lo = fa.lower() if fa.lower() < fb.lower() else fb.lower()
        total += (tb - ta) * arb(lo)
    return total.lower()


def g_exact(n, p):
    """E|n^{-1/2} sum xi_j| for xi = xi^(p), exact binomial sum in double precision (log-space pmf)."""
    q = p * (1 - p)
    lp, lq = math.log(p), math.log(1 - p)
    s = 0.0
    for k in range(n + 1):
        lpmf = math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * lp + (n - k) * lq
        s += math.exp(lpmf) * abs(k - n * p)
    return s / math.sqrt(n * q)


def float_check(M, nmax):
    """Midpoint values: closed form f_N vs brute-force max over n <= nmax (only where N <= nmax / 3)."""
    worst = 0.0
    checked = 0
    integral = 0.0
    h = (math.pi / 2) / M
    for i in range(M):
        th = (i + 0.5) * h
        x = (1 - math.sin(th)) / 2
        p = 1 - x
        N = N_of(x)
        fN = 2 * math.sqrt(N * x) * (1 - x) ** (N - 0.5)
        integral += h * fN
        if N <= nmax // 3:
            best = max(g_exact(n, p) for n in range(1, nmax + 1))
            worst = max(worst, best - fN)
            checked += 1
    return integral, checked, worst


if __name__ == '__main__':
    t0 = time.time()
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
    gap = 1e-6
    lo = certified_lower(M, gap)
    print(f'certified lower bound for int_0^(pi/2) R(p(theta)) dtheta: {lo.str(10)} '
          f'(M = {M} intervals on [0, pi/2 - {gap}]; {time.time() - t0:.1f} s)', flush=True)
    integral, checked, worst = float_check(4000, 240)
    print(f'midpoint rule (4000 points) for int f_N(x(theta)) dtheta: {integral:.7f}')
    print(f'brute-force max over n <= 240 at {checked} midpoints: largest excess over f_N = {worst:.2e}')
    print(f'pi/2 - (midpoint value) = {math.pi / 2 - integral:.6f}; total time {time.time() - t0:.1f} s')
