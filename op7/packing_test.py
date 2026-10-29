"""Packing Lemma test. For S = D1 and U = V minus N[S] with G[U] of maximum degree <= 2, compare
  pack = max 3 y(U) + sum_{v not in U} (3 - |N[v] & S|) y_v  over y >= 0 with y(N[v]) <= 1 for all v
with |U|. The Packing Lemma (pack >= |U|) implies |D1| + |U| <= 3 x(V) for every fractional
dominating set x with S = {x >= 1/3}: it is the LP dual with the cap x <= 1/3 dropped.
Also reports the exact value 3 LP(S) - |S| from adv_round for comparison.
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog

from adv_battery import hub_pentagons
from adv_round import lp_given_S
from round_exp import pentagon_flower, random_planar_girth, subdivided_triangulation


def pack_value(A, S, U):
    n = len(S)
    w = np.array([3.0 if U[v] else 3.0 - sum(A[v, u] for u in range(n) if S[u]) for v in range(n)])
    w = np.maximum(w, 0)
    r = linprog(-w, A_ub=A, b_ub=np.ones(n), bounds=(0, None), method="highs")
    return -r.fun


def instance(adj, A, S):
    n = len(adj)
    U = [not (S[v] or any(S[w] for w in adj[v])) for v in range(n)]
    if any(U[v] and sum(U[w] for w in adj[v]) > 2 for v in range(n)):
        return None
    lpv = lp_given_S(A, S, 1 / 3)
    if lpv is None:
        return None
    return sum(U), pack_value(A, S, U), 3 * lpv - sum(S)


def main(seed=1, trials=300):
    rng = random.Random(seed)
    fams = [("pentagon flower k=8", pentagon_flower(8)), ("hub pentagons k=6 m=2", hub_pentagons(6, 2, rng))]
    for n in (30, 50):
        fams.append((f"random planar girth>=5 n={n}", random_planar_girth(n, 5, rng)))
    fams.append(("subdivided triangulation n=12", subdivided_triangulation(12, rng)))
    worst = None
    for name, G in fams:
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        n = len(adj)
        A = np.eye(n)
        for v in range(n):
            for w in adj[v]:
                A[v, w] = 1
        cnt, fails, gap = 0, 0, None
        for _ in range(trials):
            p = rng.choice((0.1, 0.2, 0.3, 0.5))
            S = [rng.random() < p for _ in range(n)]
            r = instance(adj, A, S)
            if r is None:
                continue
            cnt += 1
            u, pk, ex = r
            assert ex >= u - 1e-6, (name, "Claim A fails", u, ex)
            if pk < u - 1e-6:
                fails += 1
            g = pk - u
            gap = g if gap is None else min(gap, g)
        print(f"{name:32s} instances={cnt:3d}  packing < |U| in {fails}  min(pack - |U|) = {gap}", flush=True)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
