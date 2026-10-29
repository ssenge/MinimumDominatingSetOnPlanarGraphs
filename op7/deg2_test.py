"""Test: if G[U] has maximum degree <= 2, is |D1| + |U| <= 3 x(V) (threshold rounding at 1/3)?

Adversarial search as in adv_round, but a choice of S whose U induces a vertex of U-degree >= 3
scores -1. Rule: D = D1 + U (all of U, the worst case of idrule on long monotone paths).
"""
import random
import sys

import networkx as nx
import numpy as np

from adv_round import lp_given_S
from round_exp import girth_ok, honeycomb, pentagon_flower, random_planar_girth, subdivided_triangulation
from adv_battery import hub_pentagons


def score(adj, A, S):
    n = len(adj)
    U = [not (S[v] or any(S[w] for w in adj[v])) for v in range(n)]
    if any(U[v] and sum(U[w] for w in adj[v]) > 2 for v in range(n)):
        return -1
    val = lp_given_S(A, S, 1 / 3)
    if val is None:
        return -1
    return (sum(S) + sum(U)) / val


def search(adj, rng, iters):
    n = len(adj)
    A = np.eye(n)
    for v in range(n):
        for w in adj[v]:
            A[v, w] = 1
    S = [rng.random() < 0.3 for _ in range(n)]
    cur = score(adj, A, S)
    for _ in range(iters):
        v = rng.randrange(n)
        S[v] = not S[v]
        new = score(adj, A, S)
        if new >= cur:
            cur = new
        else:
            S[v] = not S[v]
    return cur


def main(seed=1, iters=3000):
    rng = random.Random(seed)
    fams = [("dodecahedron", nx.dodecahedral_graph()), ("pentagon flower k=8", pentagon_flower(8)),
            ("hub pentagons k=6 m=2", hub_pentagons(6, 2, rng)), ("hub pentagons k=4 m=4", hub_pentagons(4, 4, rng))]
    for n in (30, 50, 80):
        fams.append((f"random planar girth>=5 n={n}", random_planar_girth(n, 5, rng)))
        fams.append((f"random planar girth>=6 n={n}", random_planar_girth(n, 6, rng)))
    for n in (12, 20):
        fams.append((f"subdivided triangulation n={n}", subdivided_triangulation(n, rng)))
    worst = 0
    for name, G in fams:
        assert girth_ok(G, 5) and nx.check_planarity(G)[0], name
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        r = max(search(adj, rng, iters) for _ in range(4))
        worst = max(worst, r)
        print(f"{name:32s} n={len(adj):3d}  (|D1|+|U|)/x(V) = {r:.3f}", flush=True)
    print(f"max {worst:.3f}")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
