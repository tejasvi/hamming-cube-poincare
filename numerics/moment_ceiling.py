#!/usr/bin/env python3
"""Best bound that the sextic moment method can give at a point (P4, P6) of the power-sum region (numerical; not part of
any proof in the paper).

For theta in (0, pi/2) let q = cos(theta)^2/4, mu3sq = (1-4q)/q, k4 = (1-6q)/q, k6 = (1-30q+120q^2)/q^2 and, for a unit
vector with power sums P3, P4, P6,
    m4 = 3 + k4 P4,   m6 = 15 + 15 k4 P4 + 10 mu3sq P3^2 + k6 P6.
The certificate uses P3^2 <= P4, and the bound is largest at P3^2 = P4. The smallest value of a + b + c m4 + d m6 over
h(z) = a + b z^2 + c z^4 + d z^6 >= |z| equals, by duality, the largest E|X| over symmetric X with E X^2 = 1, E X^4 = m4,
E X^6 = m6, i.e. the largest E sqrt(Y) for Y >= 0 with moments 1, 1, m4, m6. Since sqrt has a negative fourth derivative,
the maximum is attained by the two-point law of Y whose atoms are the roots of y^2 + alpha y + beta with
m4 + alpha + beta = 0 and m6 + alpha m4 + beta = 0 (Gauss quadrature for the moment sequence 1, 1, m4, m6).
The LP check in check_lp() compares this closed form with a direct LP over the polynomial coefficients.

M(P4, P6) := int_0^{pi/2} min(1, V(theta)) dtheta, V = that maximum (called B in this script). By weak duality,
E h(X) >= E|X| for the explicit two-point law, so no bound of the paper's Lemma 3.3 can be smaller than V; hence the
certificate can only prove K <= c for c >= max over the region of B. The two-point law exists when m4 > 1 and
m6 > m4^2; where it does not (only at a few points of the relaxed region, near theta = pi/2), the script uses 1, and it
reports how often that happens at the points it prints.
"""
import math
import sys
import time

import numpy as np


def V_closed(m4, m6):
    alpha = -(m6 - m4) / (m4 - 1.0)
    beta = -m4 - alpha
    disc = alpha * alpha - 4 * beta
    r = math.sqrt(disc)
    y1, y2 = (-alpha - r) / 2, (-alpha + r) / 2
    w2 = (1.0 - y1) / (y2 - y1)
    w1 = 1.0 - w2
    assert y1 > 0 and 0 < w2 < 1, (m4, m6, y1, y2, w2)
    return w1 * math.sqrt(y1) + w2 * math.sqrt(y2)


def moments(theta, P4, P6, P3sq):
    q = math.cos(theta) ** 2 / 4
    mu3sq = (1 - 4 * q) / q
    k4 = (1 - 6 * q) / q
    k6 = (1 - 30 * q + 120 * q * q) / (q * q)
    return 3 + k4 * P4, 15 + 15 * k4 * P4 + 10 * mu3sq * P3sq + k6 * P6


THETA_N = 20000
THETAS = (np.arange(THETA_N) + 0.5) * (math.pi / 2) / THETA_N


def B(P4, P6, P3sq=None):
    if P3sq is None:
        P3sq = P4
    h = (math.pi / 2) / THETA_N
    tot = 0.0
    for th in THETAS:
        m4, m6 = moments(th, P4, P6, P3sq)
        v = 1.0
        if m4 > 1 + 1e-12 and m6 > m4 * m4 * (1 + 1e-12):
            try:
                v = min(1.0, V_closed(m4, m6))
            except (AssertionError, ValueError):
                v = 1.0
        tot += h * v
    return tot


def fallbacks(P4, P6, P3sq=None):
    if P3sq is None:
        P3sq = P4
    cnt = 0
    for th in THETAS:
        m4, m6 = moments(th, P4, P6, P3sq)
        ok = m4 > 1 + 1e-12 and m6 > m4 * m4 * (1 + 1e-12)
        if ok:
            try:
                V_closed(m4, m6)
            except (AssertionError, ValueError):
                ok = False
        cnt += 0 if ok else 1
    return cnt


def check_lp():
    from scipy.optimize import linprog
    U = np.concatenate([np.linspace(0, 6, 6001), np.linspace(6.002, 60, 6000)])
    A = -np.column_stack([np.ones_like(U), U ** 2, U ** 4, U ** 6])
    worst = 0.0
    for (m4, m6) in [(3.0, 15.0), (2.0, 6.0), (4.5, 40.0), (1.5, 3.0), (8.0, 200.0)]:
        res = linprog([1, 1, m4, m6], A_ub=A, b_ub=-U, bounds=[(None, None)] * 3 + [(0, None)], method='highs')
        worst = max(worst, abs(res.fun - V_closed(m4, m6)))
        print(f'  m4 = {m4}, m6 = {m6}: LP {res.fun:.7f}, closed form {V_closed(m4, m6):.7f}')
    return worst


if __name__ == '__main__':
    t0 = time.time()
    print('closed form vs LP (the LP on a u-grid is a slight under-estimate):')
    print(f'  largest difference {check_lp():.2e}')
    print(f'Gaussian moments (m4, m6) = (3, 15): V = {V_closed(3.0, 15.0):.6f} (E|g| = {math.sqrt(2 / math.pi):.6f})')
    for (P4, P6) in [(0.0338, 0.0062), (0.02, 0.02 ** 1.5), (0.0446, 0.0094)]:
        print(f'B({P4}, {P6:.6f}) = {B(P4, P6):.6f} (fallbacks: {fallbacks(P4, P6)})', flush=True)
    # scan of the whole region: P4 in [1e-6, 1], P6 in [P4^2, P4^1.5]
    best = (0.0, None)
    for P4 in np.geomspace(1e-6, 1.0, 90):
        for s in np.linspace(0, 1, 11):
            P6 = P4 ** 2 + s * (P4 ** 1.5 - P4 ** 2)
            v = B(P4, P6)
            if v > best[0]:
                best = (v, (P4, P6, s))
    print(f'coarse scan max B = {best[0]:.6f} at P4 = {best[1][0]:.5f}, P6 = {best[1][1]:.6f} (s = {best[1][2]})',
          flush=True)
    # local refinement around the best point (s = position between P4^2 and P4^1.5)
    P4c, _, sc = best[1]
    for it in range(3):
        cand = []
        for P4 in np.linspace(P4c * 0.8, P4c * 1.2, 9):
            for s in np.linspace(max(0, sc - 0.2), min(1, sc + 0.2), 5):
                P6 = P4 ** 2 + s * (P4 ** 1.5 - P4 ** 2)
                cand.append((B(P4, P6), P4, s))
        v, P4c, sc = max(cand)
        print(f'  refine {it}: B = {v:.6f} at P4 = {P4c:.5f}, s = {sc:.3f}', flush=True)
    P6c = P4c ** 2 + sc * (P4c ** 1.5 - P4c ** 2)
    print(f'max B (numerical) = {v:.6f} at P4 = {P4c:.5f}, P6 = {P6c:.6f} (fallbacks: {fallbacks(P4c, P6c)}); '
          f'{time.time() - t0:.0f} s')
