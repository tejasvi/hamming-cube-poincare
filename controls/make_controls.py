#!/usr/bin/env python3
"""Make perturbed copies of the certificate, to test the two checkers. Each copy must be rejected (exit status 1).

usage: python3 make_controls.py ../certificate/mom_c142.json OUTDIR

  claim_1418.json          claim lowered to 709/500 = 1.418 (below the largest computed leaf bound)
  bad_polynomial.json      first polynomial of the list changed so that H takes the value -1e-6 at one point of (0, inf)
  missing_leaf.json        first leaf removed (the squares no longer tile [0,1]^2)
  leaf_declared_outside.json   first leaf moved to the outside list, although it meets the region R
  wrong_polynomials.json   every polynomial index of one leaf replaced by 0 (trivial entries kept)
  N_zero.json              N = 0 and empty index lists
  short_index_list.json    last entry of the first leaf's index list removed
  index_out_of_range.json  one index of the first leaf set to the length of the list
"""
import copy
import json
import os
import sys
from fractions import Fraction as F


def H(co, u):
    a, b, c, d = co
    return a - u + b * u ** 2 + c * u ** 4 + d * u ** 6


def main():
    src, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    cert = json.load(open(src))

    def save(name, c):
        json.dump(c, open(os.path.join(out, name), 'w'))

    c = copy.deepcopy(cert)
    c['claimed'] = '709/500'
    save('claim_1418.json', c)

    c = copy.deepcopy(cert)
    co = [F(x) for x in c['library'][0]]
    grid = [F(k, 1000) for k in range(1, 5001)]
    u0 = min(grid, key=lambda u: H(co, u))
    co[0] = co[0] - H(co, u0) - F(1, 10 ** 6)          # now H(u0) = -1e-6 exactly
    assert H(co, u0) < 0 and co[0] > 0
    c['library'][0] = [str(x) for x in co]
    save('bad_polynomial.json', c)

    c = copy.deepcopy(cert)
    c['leaves'] = c['leaves'][1:]
    save('missing_leaf.json', c)

    c = copy.deepcopy(cert)
    code = c['leaves'][0][0]
    l, i, k = code
    s = F(1, 2 ** l)
    s0, s1, t0, t1 = i * s, (i + 1) * s, k * s, (k + 1) * s
    assert not (t1 < s0 * s0 or t0 * t0 > s1 ** 3)      # the square meets R
    c['outside'].append(code)
    c['leaves'] = c['leaves'][1:]
    save('leaf_declared_outside.json', c)

    c = copy.deepcopy(cert)
    target = [11, 49, 7]
    for leaf in c['leaves']:
        if leaf[0] == target:
            leaf[1] = [0 if j >= 0 else j for j in leaf[1]]
    save('wrong_polynomials.json', c)

    c = copy.deepcopy(cert)
    c['N'] = 0
    c['leaves'] = [[code, []] for code, idx in c['leaves']]
    save('N_zero.json', c)

    c = copy.deepcopy(cert)
    c['leaves'][0][1] = c['leaves'][0][1][:-1]
    save('short_index_list.json', c)

    c = copy.deepcopy(cert)
    idx = c['leaves'][0][1]
    pos = next(n for n, j in enumerate(idx) if j >= 0)
    idx[pos] = len(c['library'])
    save('index_out_of_range.json', c)
    print('wrote 8 controls to', out)


if __name__ == '__main__':
    main()
