#!/usr/bin/env python3
"""Remark 4.8 of the paper: for a fixed theta the inequality E|sum_j lambda_j xi_j| <= E|sum_j |lambda_j| xi_j| can fail.

At p = 4/5, which is p(theta) = (1 + sin theta)/2 for sin theta = 3/5, the variable xi^(p) takes the value
sqrt((1-p)/p) = 1/2 with probability 4/5 and -sqrt(p/(1-p)) = -2 with probability 1/5. For lambda = (1, 1, 1, 1, -1)
the program computes both expectations exactly, by enumerating the 2^5 sign patterns in rational arithmetic.
"""
from fractions import Fraction
from itertools import product

P = Fraction(4, 5)
VALUES = [(Fraction(1, 2), P), (Fraction(-2), 1 - P)]


def mean_abs(lam):
    total = Fraction(0)
    for pattern in product(VALUES, repeat=len(lam)):
        prob = Fraction(1)
        for _, w in pattern:
            prob *= w
        total += prob * abs(sum(l * v for l, (v, _) in zip(lam, pattern)))
    return total


def main():
    assert (1 + Fraction(3, 5)) / 2 == P
    assert sum(v * w for v, w in VALUES) == 0 and sum(v * v * w for v, w in VALUES) == 1
    lam = [1, 1, 1, 1, -1]
    a = mean_abs(lam)
    b = mean_abs([abs(l) for l in lam])
    print("p = 4/5: E xi = 0, E xi^2 = 1")
    print("lambda = (1, 1, 1, 1, -1): E|sum lambda_j xi_j| =", a, "=", float(a))
    print("|lambda| = (1, 1, 1, 1, 1):  E|sum |lambda_j| xi_j| =", b, "=", float(b))
    print("first > second:", a > b)


if __name__ == "__main__":
    main()
