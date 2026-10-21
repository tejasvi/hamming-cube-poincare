#!/usr/bin/env python3
"""Remark 5.2 of the paper: in dimension 2 the best constant in E|f - Ef| <= C E|grad f| is 1.

(1) For the four functions g = 1, x1, x1 x2, min(x1, x2) the program checks, in rational arithmetic, that the pairs
    V = (V1, V2) of the remark satisfy D1 V1 + D2 V2 = g - E g and |V(x)|^2 <= 1 at every point x.
(2) It applies the symmetries of the square and the change g -> -g to these four pairs and checks that every one of
    the 16 functions g from {-1,1}^2 to {-1,1} receives a pair V with the same two properties.
(3) As an independent sanity check (floating point, not part of the proof), it evaluates the ratio
    E|f - Ef| / E|grad f| for 200000 random functions f.
"""
import random
from fractions import Fraction as Fr
from itertools import product

PTS = list(product([1, -1], repeat=2))


def D(h, j):
    return {x: (h[x] - h[tuple(-x[i] if i == j else x[i] for i in range(2))]) / 2 for x in PTS}


def E(h):
    return sum(h.values()) / 4


def base_pairs():
    zero = {x: Fr(0) for x in PTS}
    return [
        ({x: Fr(1) for x in PTS}, (zero, zero)),
        ({x: Fr(x[0]) for x in PTS}, ({x: Fr(x[0]) for x in PTS}, zero)),
        ({x: Fr(x[0] * x[1]) for x in PTS}, ({x: Fr(x[0] * x[1], 2) for x in PTS}, {x: Fr(x[0] * x[1], 2) for x in PTS})),
        ({x: Fr(min(x)) for x in PTS},
         ({x: Fr(x[0], 2) + Fr(x[0] * x[1], 4) + Fr(x[1], 10) - Fr(3, 20) for x in PTS},
          {x: Fr(x[1], 2) + Fr(x[0] * x[1], 4) + Fr(x[0], 10) - Fr(3, 20) for x in PTS})),
    ]


def good(g, V):
    lhs = {x: D(V[0], 0)[x] + D(V[1], 1)[x] for x in PTS}
    Eg = E(g)
    return all(lhs[x] == g[x] - Eg for x in PTS) and all(V[0][x] ** 2 + V[1][x] ** 2 <= 1 for x in PTS)


def main():
    pairs = base_pairs()
    for g, V in pairs:
        assert good(g, V)
    print("(1) four pairs: identity exact; max |V|^2 =", [str(max(V[0][x] ** 2 + V[1][x] ** 2 for x in PTS)) for _, V in pairs])
    covered = set()
    for g, V in pairs:
        for perm in [(0, 1), (1, 0)]:
            for sg in product([1, -1], repeat=2):
                for neg in [1, -1]:
                    act = lambda x: tuple(sg[i] * x[perm[i]] for i in range(2))
                    g2 = {x: neg * g[act(x)] for x in PTS}
                    W = tuple({x: neg * V[perm[i]][act(x)] for x in PTS} for i in range(2))
                    if good(g2, W):
                        covered.add(tuple(g2[x] for x in PTS))
    print("(2) sign functions g with a pair V, max |V| <= 1:", len(covered), "of 16")
    assert len(covered) == 16
    random.seed(1)
    best = 0.0
    for _ in range(200000):
        f = {x: random.gauss(0, 1) for x in PTS}
        m = E(f)
        num = sum(abs(f[x] - m) for x in PTS) / 4
        den = sum((D(f, 0)[x] ** 2 + D(f, 1)[x] ** 2) ** 0.5 for x in PTS) / 4
        best = max(best, num / den)
    print("(3) largest ratio over 200000 random f: %.7f" % best)


if __name__ == "__main__":
    main()
