"""Optimal r-round ratio for fractional domination on paths.

View of v on P_L after r rounds (degrees at distance r known): the unordered pair {a, b},
a = min(v, R), b = min(L-1-v, R), R = r+1 meaning "end not seen".

lower(r):  max_L of the symmetric LP on P_L divided by gamma(P_L) = ceil(L/3). Under uniformly random
           IDs (and coins) E[x_v] depends only on the view, and E[x] is feasible, so every r-round
           algorithm (deterministic fractional, or randomized with expected size) is at least this bad,
           even if it knows L.
upper(r):  best ratio of a single view function f(a, b) on all paths at once. A deterministic
           algorithm without IDs outputs f(view), so this ratio is achievable in r rounds.
explicit(L, r): the explicit weights after Theorem 4 (README), weight (L+2)/3 for L >= 2r+3.
Checked for r <= 15: lower(r) = 1 + 2/L_r with L_r = 2r + 6 + (r mod 3) (attained at L = L_r), and
upper(r) = 1 + 1/(r + 2) for r != 2 mod 3, 1 + 1/(r + 3/2) for r = 2 mod 3.
"""
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
    Ls = range(1, 2 * R + 13)  # beyond this, cost constraints only weaken (see docstring of OP4.md proof)
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


def explicit(L, r):
    p = max(q for q in range(1, r + 1) if q % 3 == 1)
    d = [min(v, L - 1 - v) for v in range(L)]
    return [1 if di <= p and di % 3 == 1 else 0 if di < p else 1 / 3 for di in d]


if __name__ == "__main__":
    for r in range(1, 16):
        for L in range(2 * r + 3, 2 * r + 30):
            x = explicit(L, r)
            assert all(sum(x[max(u - 1, 0):u + 2]) >= 1 - 1e-12 for u in range(L))
            assert abs(sum(x) - (L + 2) / 3) < 1e-9
        Lr = 2 * r + 6 + r % 3
        lb, L = lower(r)
        ub = upper(r)
        assert abs(lb - (1 + 2 / Lr)) < 1e-9 and L == Lr, (r, lb, L)
        assert abs(ub - (1 + 1 / (r + 2 - (r % 3 == 2) / 2))) < 1e-6, (r, ub)
        print(f"r={r:2d}  L_r={Lr:3d}  known length {lb:.6f} = 1+2/L_r   unknown length {ub:.6f}")
