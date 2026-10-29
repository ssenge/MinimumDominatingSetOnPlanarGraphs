"""Adversarial test of a rounding rule against every fractional dominating set.

A rule with threshold theta only sees which vertices have x_v >= theta (the set S) and the
identifiers. For fixed S, the cheapest x consistent with S is an LP: min x(V) subject to
x(N[u]) >= 1, x_v >= theta on S and 0 <= x_v <= theta - eps off S. Local search over S and the
identifiers maximizes |D| / x(V). Run on small planar graphs of girth >= 5 and >= 6.
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog

from round_exp import (girth_ok, honeycomb, idrule, pentagon_flower, random_planar_girth,
                       subdivided_triangulation, thresh)

EPS = 1e-6


def lp_given_S(A, S, theta):
    n = len(S)
    bounds = [(theta, None) if S[v] else (0, theta - EPS) for v in range(n)]
    res = linprog(np.ones(n), A_ub=-A, b_ub=-np.ones(n), bounds=bounds, method="highs")
    return res.fun if res.status == 0 else None


def search(adj, rule, theta, rng, iters):
    n = len(adj)
    A = np.eye(n)
    for v in range(n):
        for w in adj[v]:
            A[v, w] = 1
    S = [False] * n
    rank = list(range(n)); rng.shuffle(rank)

    def score():
        val = lp_given_S(A, S, theta)
        if val is None:
            return -1
        x = np.array([theta if S[v] else 0.0 for v in range(n)])  # only S and ids matter
        return rule(adj, x, rank, theta) / val

    cur = score()
    for _ in range(iters):
        if rng.random() < 0.5:
            v = rng.randrange(n)
            S[v] = not S[v]
            new = score()
            if new >= cur:
                cur = new
            else:
                S[v] = not S[v]
        else:
            a, b = rng.randrange(n), rng.randrange(n)
            rank[a], rank[b] = rank[b], rank[a]
            new = score()
            if new >= cur:
                cur = new
            else:
                rank[a], rank[b] = rank[b], rank[a]
    return cur


def main(seed=1, iters=1500):
    rng = random.Random(seed)
    fams = [("dodecahedron", 5, nx.dodecahedral_graph()),
            ("honeycomb 6x6 torus", 6, honeycomb(6, 6)),
            ("pentagon flower k=5", 5, pentagon_flower(5))]
    for g in (5, 6):
        for n in (25, 40):
            fams.append((f"random planar girth>={g} n={n}", g, random_planar_girth(n, g, rng)))
    fams.append(("subdivided triangulation n=10", 6, subdivided_triangulation(10, rng)))
    res = {}
    for name, g, G in fams:
        assert girth_ok(G, g), name
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        a = g / (g - 2)
        out = []
        for rname, rule, theta in (("thresh", thresh, 1 / (2 * a + 1)), ("idrule 1/3", idrule, 1 / 3)):
            r = max(search(adj, rule, theta, rng, iters) for _ in range(3))
            res.setdefault((g, rname), []).append(r)
            out.append(f"{rname}={r:.3f}")
        print(f"{name:32s} n={len(adj):3d}  " + "  ".join(out), flush=True)
    for (g, rname), v in sorted(res.items()):
        print(f"girth>={g}  {rname:12s} max |D|/x(V) = {max(v):.3f}  (2a+1 = {(3 * g - 2) / (g - 2):.3f})")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
