"""Theorem 2 for classes with edge density a and bipartite density b, checked in exact arithmetic.

For a class C with |E(H)| <= a|V(H)| for all H in C and |E(H)| <= b|V(H)| for bipartite H in C:
  (A_t) |E| <= sum_v min(d_v, t)              (t >= a)
  (B_u) 2|E| <= sum_v min(d_v, u) + b*n'      (u >= 2a)
A pointwise certificate  g(d) >= sum al_t min(d,t) + sum be_u (min(d,u) + b[d>=1])  for all d >= 0
gives  E[gain] >= s * (sum al + 2 sum be) * w(Q),  s = 1-p,  g(d) = 1 - s^d.

For every surface of Euler genus eg (chi = 2 - eg) we bound a, b by Euler's formula, take the best
dyadic p with at most 8 coins, find the certificate by LP, round it down to rationals, and verify it
exactly for every d (beyond the largest threshold the right side is constant and g increases).
Usage: python3 surfaces.py
"""
from fractions import Fraction as F
from math import ceil, floor, log

import numpy as np
from scipy.optimize import linprog

LN3 = log(3)
kappa = lambda f: LN3 / log(1 / (1 - f))


def surface(eg):
    chi = 2 - eg
    a = max([F(3)] + [F(min(n * (n - 1) // 2, 3 * n - 3 * chi), n) for n in range(3, 500)])
    b = max([F(2)] + [F(min(n * n // 4, 2 * n - 2 * chi), n) for n in range(3, 500)])
    return a, b


def thresholds(a, extra=6):
    T = ceil(2 * a) + extra
    ts = sorted({a} | {F(t) for t in range(ceil(a), T + 1)})
    us = sorted({2 * a} | {F(u) for u in range(ceil(2 * a), T + 1)})
    return T, ts, us


def certificate(s, a, b, useB=True):
    """Exact certificate value c (a Fraction) for the dyadic s, or 0 if none found."""
    T, ts, us = thresholds(a)
    us = us if useB else []
    rows = [[float(min(d, t)) for t in ts] + [float(min(d, u) + b) for u in us] for d in range(1, T + 1)]
    sf = float(s)
    res = linprog(-np.array([1.0] * len(ts) + [2.0] * len(us)), A_ub=rows,
                  b_ub=[1 - sf ** d for d in range(1, T + 1)], bounds=[(0, None)] * (len(ts) + len(us)),
                  method="highs")
    if res.status != 0:
        return F(0)
    for shrink in (7, 6, 5, 4):  # round the LP solution down until it is exactly feasible
        x = [F(max(v, 0.0)).limit_denominator(10 ** 9) * (1 - F(1, 10 ** shrink)) for v in res.x]
        al, be = x[:len(ts)], x[len(ts):]
        # exact check; for d > T the right side is constant and g increases
        if all(1 - s ** d >= sum(c * min(d, t) for c, t in zip(al, ts))
               + sum(c * (min(d, u) + (b if d else 0)) for c, u in zip(be, us)) for d in range(T + 1)):
            return sum(al) + 2 * sum(be)
    return F(0)


def best(fun):
    """max over dyadic p = m/2^8 of s * fun(s)."""
    return max((s * fun(s), 1 - s) for s in (1 - F(m, 256) for m in range(1, 256)))


def thm1(a):  # orientation bound with k = ceil(a)
    k = ceil(a)
    return best(lambda s: (1 - s ** k) / k)


def a_only(a):  # closed form min(g(floor a)/floor a, g(ceil a)/a)
    return best(lambda s: min((1 - s ** floor(a)) / floor(a), (1 - s ** ceil(a)) / a))


if __name__ == "__main__":
    # planar check: the certificate LP reproduces phi(3/8) = 357115/2097152 from below
    c = certificate(F(5, 8), F(3), F(2))
    assert F(5, 8) * c <= F(357115, 2097152) and F(5, 8) * c > F(357115, 2097152) - F(1, 10 ** 6)
    # the A-only closed form is a valid certificate and matches the LP without facts B
    for a in (F(11, 3), F(21, 5), F(51, 11)):
        s = F(5, 7)
        cA = min((1 - s ** floor(a)) / floor(a), (1 - s ** ceil(a)) / a)
        assert abs(certificate(s, a, a, useB=False) - cA) < F(1, 10 ** 6)
    print(f"{'Euler genus':>11} {'a':>6} {'b':>6} | {'[1]':>7} {'Thm 1':>7} {'A only':>7} {'A+B':>7} | p")
    for eg in [0, 3, 4, 5, 6, 8, 10, 12, 16, 20, 40, 100, 200]:
        a, b = surface(eg)
        f, p = best(lambda s: certificate(s, a, b))
        label = "0, 1, 2" if eg == 0 else str(eg)
        print(f"{label:>11} {float(a):6.3f} {float(b):6.3f} | {kappa(1 / (8 * float(a))):7.2f} "
              f"{kappa(float(thm1(a)[0])):7.2f} {kappa(float(a_only(a)[0])):7.2f} {kappa(float(f)):7.2f} | {p}")
