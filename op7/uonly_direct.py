"""U-only test with U chosen directly (any set of vertices of degree >= 3).

For a vertex set U: W = N(U) minus U, LP_U = min x(N[U]) s.t. x(N[u]) >= 1 (u in U), x <= 1/3.
Hub rule from U: H = {w in W : |N(w) n U| >= 4} (variant 'all': also u in U with >= 4
U-neighbours), U' = U minus N[H], T = idrule on G[U']. Score (|H| + |T|) / LP_U, maximized over
U and identifiers. Score <= 3 everywhere would reduce the theorem to the combinatorial statement
|U| - |H| - |T| >= Phi(U), Phi(U) = |U| - 3 LP_U.
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog

from round_exp import honeycomb, random_planar_girth, subdivided_triangulation, pentagon_flower
from adv_battery import hub_pentagons

CAP = 1 / 3 - 1e-6


def lp_u(adj, U):
    us = [u for u in range(len(adj)) if U[u]]
    cols = sorted({w for u in us for w in adj[u]} | set(us))
    ci = {v: i for i, v in enumerate(cols)}
    A = np.zeros((len(us), len(cols)))
    for r, u in enumerate(us):
        A[r, ci[u]] = 1
        for w in adj[u]:
            A[r, ci[w]] = 1
    res = linprog(np.ones(len(cols)), A_ub=-A, b_ub=-np.ones(len(us)), bounds=(0, CAP), method="highs")
    return res.fun if res.status == 0 else None


def hub_size(adj, U, rank, variant):
    n = len(adj)
    cnt = [sum(U[w] for w in adj[v]) for v in range(n)]
    H = [cnt[v] >= 4 and (not U[v] or variant == "all") for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    if variant == "idrule":
        H = [False] * n
        U2 = list(U)
    J = [False] * n
    for v in range(n):
        if U2[v]:
            nb = [w for w in adj[v] if U2[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    R = [U2[v] and not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    return sum(H) + sum(J) + sum(R)


def search(adj, variant, rng, iters):
    n = len(adj)
    cand = [v for v in range(n) if len(adj[v]) >= 3]
    U = [False] * n
    for v in cand:
        U[v] = rng.random() < 0.6
    rank = list(range(n)); rng.shuffle(rank)

    def sc():
        if not any(U):
            return -1
        val = lp_u(adj, U)
        return hub_size(adj, U, rank, variant) / val if val else -1

    cur = sc()
    for _ in range(iters):
        if rng.random() < 0.5:
            v = rng.choice(cand); U[v] = not U[v]
            new = sc()
            if new >= cur:
                cur = new
            else:
                U[v] = not U[v]
        else:
            a, b = rng.randrange(n), rng.randrange(n)
            rank[a], rank[b] = rank[b], rank[a]
            new = sc()
            if new >= cur:
                cur = new
            else:
                rank[a], rank[b] = rank[b], rank[a]
    return cur


def main(seed=1, iters=2000):
    rng = random.Random(seed)
    fams = [("dodecahedron", nx.dodecahedral_graph()), ("pentagon flower k=8", pentagon_flower(8)),
            ("hub pentagons 6,2", hub_pentagons(6, 2, rng)), ("hub pentagons 4,4", hub_pentagons(4, 4, rng))]
    for n in (30, 50, 80):
        fams.append((f"random planar g>=5 n={n}", random_planar_girth(n, 5, rng)))
    for n in (12, 20):
        fams.append((f"subdivided triangulation n={n}", subdivided_triangulation(n, rng)))
    fams.append(("honeycomb 6x6 torus (nonplanar)", honeycomb(6, 6)))
    m = {}
    for name, G in fams:
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        out = []
        for variant in ("hub", "all", "idrule"):
            r = max(search(adj, variant, rng, iters) for _ in range(3))
            if "nonplanar" not in name:
                m[variant] = max(m.get(variant, 0), r)
            out.append(f"{variant}={r:.3f}")
        print(f"{name:34s} n={len(adj):3d} " + "  ".join(out), flush=True)
    print("max over planar:", {k: round(v, 3) for k, v in m.items()})


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
