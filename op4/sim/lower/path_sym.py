"""Optimal r-round ratio for fractional domination on paths.

View of v on P_L after r rounds (degrees at distance r known): the unordered pair {a, b},
a = min(v, R), b = min(L-1-v, R), R = r+1 meaning "end not seen".

lower(r):  max_L of the symmetric LP on P_L divided by gamma(P_L) = ceil(L/3). Under uniformly random
           IDs (and coins) E[x_v] depends only on the view, and E[x] is feasible, so every r-round
           algorithm (deterministic fractional, or randomized and always dominating) is at least
           this bad, even if it knows L.
upper(r):  best ratio of a single view function f(a, b) on all paths at once. A deterministic
           algorithm without IDs outputs f(view), so this ratio is achievable in r rounds.
known(L, r), unknown(L, r): the explicit algorithms after Theorem 4 of the README (Theorem 17 of the
           paper), as functions of the view: weights 2/3 at the ends and 1/3 elsewhere, and the
           average of a minimum dominating set and its mirror image on short paths. They are checked
           in exact arithmetic: ratio at most 1 + 2/(2r+3) with the length, 1 + 2/(r+2) without.
Checked for 0 <= r <= 15 (floating-point LPs): lower(r) = 1 + 2/L_r with L_r = 2r + 6 + (r mod 3)
(attained at L = L_r), and upper(r) = 1 + 1/(r + 2) for r != 2 mod 3, 1 + 1/(r + 3/2) for
r = 2 mod 3.
"""
from fractions import Fraction
from math import ceil

import numpy as np
from scipy.optimize import linprog


def views(L, R):
    return [tuple(sorted((min(v, R), min(L - 1 - v, R)))) for v in range(L)]


def lp_rows(L, R, idx):
    """Domination rows (as <= rows) and the cost row of P_L in the variables idx[view]."""
    vw = views(L, R)
    cost = np.zeros(len(idx))
    for w in vw:
        cost[idx[w]] += 1
    rows = []
    for u in range(L):
        row = np.zeros(len(idx))
        for v in (u - 1, u, u + 1):
            if 0 <= v < L:
                row[idx[vw[v]]] -= 1
        rows.append(row)
    return rows, cost


def sym_lp(L, r):
    R = r + 1
    idx = {w: i for i, w in enumerate(sorted(set(views(L, R))))}
    rows, cost = lp_rows(L, R, idx)
    return linprog(cost, A_ub=rows, b_ub=[-1] * L, bounds=(0, None), method="highs").fun


def lower(r, extra=40):
    return max((sym_lp(L, r) / ceil(L / 3), L) for L in range(1, 2 * r + extra))


def upper(r, lo=1.0, hi=2.0, iters=40):
    R = r + 1
    idx = {(a, b): i for i, (a, b) in enumerate((a, b) for a in range(R + 1) for b in range(a, R + 1))}
    # For L >= 2R+1 every view occurs, so P_{L+3} has the domination rows of P_L and three more
    # vertices with view (R, R), while ceil((L+3)/3) = ceil(L/3) + 1. With the row 3 f(R, R) <= t
    # below, the cost constraint of L+3 follows from that of L, so L <= 2R+3 suffices.
    Ls = range(1, 2 * R + 13)
    dom, costs = [], []
    for L in Ls:
        rows, cost = lp_rows(L, R, idx)
        dom += rows
        costs.append((cost, ceil(L / 3)))
    mu = np.zeros(len(idx)); mu[idx[(R, R)]] = 3  # L -> infinity: 3 f(R, R) <= t
    for _ in range(iters):
        t = (lo + hi) / 2
        A = dom + [c for c, _ in costs] + [mu]
        b = [-1] * len(dom) + [t * g for _, g in costs] + [t]
        ok = linprog(np.zeros(len(idx)), A_ub=A, b_ub=b, bounds=(0, None), method="highs").status == 0
        lo, hi = (lo, t) if ok else (t, hi)
    return hi


def mirror_avg(L):
    """Average of the minimum dominating set {1, 4, ...} of P_L (last vertex capped) and its mirror."""
    S = {min(3 * i + 1, L - 1) for i in range(ceil(L / 3))}
    return [Fraction((v in S) + (L - 1 - v in S), 2) for v in range(L)]


def from_view(L, r, f):
    R = r + 1
    return [f(*sorted((min(v, R), min(L - 1 - v, R)))) for v in range(L)]


def ends(a, b):
    """Weight 2/3 at an end of the path (a = 0), 1/3 elsewhere."""
    return Fraction(2, 3) if a == 0 else Fraction(1, 3)


def known(L, r):
    """Knows L: the mirror average if L <= 2r+2 (the nearer end is seen), else 2/3 and 1/3."""
    avg = mirror_avg(L)
    if L <= 2 * r + 2:
        return from_view(L, r, lambda a, b: avg[a])
    return from_view(L, r, ends)


def unknown(L, r):
    """Does not know L: the mirror average if both ends are seen and the path has <= r+1 vertices."""
    R = r + 1
    def f(a, b):
        if b < R and a + b + 1 <= r + 1:
            return mirror_avg(a + b + 1)[a]
        return ends(a, b)
    return from_view(L, r, f)


def dominates(x):
    return all(sum(x[max(u - 1, 0):u + 2]) >= 1 for u in range(len(x)))


if __name__ == "__main__":
    for r in range(16):
        for L in range(1, 2 * r + 40):
            for x, bound in ((known(L, r), Fraction(2, 2 * r + 3)), (unknown(L, r), Fraction(2, r + 2))):
                assert dominates(x), (r, L)
                assert sum(x) <= (1 + bound) * ceil(L / 3), (r, L, sum(x))
            if L >= 2:
                x = from_view(L, r, ends)
                assert dominates(x) and sum(x) == Fraction(L + 2, 3), (r, L)
        Lr = 2 * r + 6 + r % 3
        lb, L = lower(r)
        ub = upper(r)
        assert abs(lb - (1 + 2 / Lr)) < 1e-9 and L == Lr, (r, lb, L)
        assert abs(ub - (1 + 1 / (r + 2 - (r % 3 == 2) / 2))) < 1e-6, (r, ub)
        print(f"r={r:2d}  L_r={Lr:3d}  known length {lb:.6f} = 1+2/L_r   unknown length {ub:.6f}")
