#!/usr/bin/env python3
"""Values of J(lambda) = int_0^{pi/2} E|sum_j lambda_j xi_j^(p(theta))| dtheta at equal weights (numerical; not part of any
proof in the paper).

Equal weights lambda = (1, ..., 1)/sqrt(n): E|n^{-1/2} sum_{j<=n} xi_j| = E|K - n p| / sqrt(n p (1-p)), K ~ Bin(n, p),
p = (1 + sin theta)/2. The integrand is smooth between the points where n p(theta) is an integer, so the integral is
computed by Gauss-Legendre quadrature on each such piece. The result is compared with formula (A4) of Theorem 6.5 of
the paper, which for equal weights reads J = sqrt(n) (1 - sum_{k=2}^n [n (n-1) ... (n-k+1) / n^k] / (k (k-1))).
"""
import math

import numpy as np

XG, WG = np.polynomial.legendre.leggauss(24)


def integrand(n, th):
    p = (1 + np.sin(th)) / 2
    q = p * (1 - p)
    k = np.arange(n + 1)[:, None]
    lc = np.array([math.lgamma(n + 1) - math.lgamma(i + 1) - math.lgamma(n - i + 1) for i in range(n + 1)])[:, None]
    lpmf = lc + k * np.log(p)[None, :] + (n - k) * np.log1p(-p)[None, :]
    return np.sum(np.exp(lpmf) * np.abs(k - n * p[None, :]), axis=0) / np.sqrt(n * q)


def J_quad(n):
    # break points: theta with n p(theta) integer, i.e. sin(theta) = 2k/n - 1 for n/2 <= k <= n
    br = sorted({0.0, math.pi / 2} | {math.asin(2 * k / n - 1) for k in range(n + 1) if 0 <= 2 * k / n - 1 <= 1})
    tot = 0.0
    for a, b in zip(br[:-1], br[1:]):
        if b - a < 1e-15:
            continue
        th = (a + b) / 2 + (b - a) / 2 * XG
        tot += (b - a) / 2 * float(np.sum(WG * integrand(n, th)))
    return tot


def J_closed(n):
    s, prod = 0.0, 1.0
    for k in range(1, n + 1):
        prod *= (n - k + 1) / n
        if k >= 2:
            s += prod / (k * (k - 1))
    return math.sqrt(n) * (1 - s)


if __name__ == '__main__':
    r = math.sqrt(math.pi / 2)
    print(f'sqrt(pi/2) = {r:.10f}')
    for n in [1, 2, 3, 10, 100, 1000]:
        jq, jc = J_quad(n), J_closed(n)
        print(f'n = {n:5d}: J by quadrature {jq:.10f}, by (A4) {jc:.10f}, difference {jq - jc:.1e}, '
              f'sqrt(n) (sqrt(pi/2) - J) = {math.sqrt(n) * (r - jc):.6f}', flush=True)
    print(f'3/(2 sqrt 2) = {3 / (2 * math.sqrt(2)):.10f}; 17/(9 sqrt 3) = {17 / (9 * math.sqrt(3)):.10f}')
