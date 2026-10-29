"""Does the hub rule beat 3 against the U-only relaxation?

LP_U = min x(N[U]) s.t. x(N[u]) >= 1 for u in U, x < 1/3 on N[U] (no constraints for W or D1).
If |D minus D1| <= 3 LP_U always, the theorem reduces to a purely combinatorial statement.
Score = (|D| - |D1|) / LP_U, maximized over D1 (= S) and identifiers by local search, for the
hub rule (W-hubs), the variant with hubs inside U, and idrule.
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog

from adv_battery import hub_pentagons
from round_exp import (honeycomb, hubrule, hubrule_all, idrule, pentagon_flower,
                       random_planar_girth, subdivided_triangulation)

CAP = 1 / 3 - 1e-6


def lp_u(adj, S):
    n = len(adj)
    U = [not (S[v] or any(S[w] for w in adj[v])) for v in range(n)]
    us = [u for u in range(n) if U[u]]
    if not us:
        return 0.0, 0
    cols = sorted({w for u in us for w in adj[u]} | set(us))
    ci = {v: i for i, v in enumerate(cols)}
    A = np.zeros((len(us), len(cols)))
    for r, u in enumerate(us):
        A[r, ci[u]] = 1
        for w in adj[u]:
            A[r, ci[w]] = 1
    res = linprog(np.ones(len(cols)), A_ub=-A, b_ub=-np.ones(len(us)), bounds=(0, CAP), method="highs")
    return (res.fun if res.status == 0 else None), len(us)


def score(adj, S, rank, rule):
    val, nu = lp_u(adj, S)
    if val is None or nu == 0:
        return -1e9  # infeasible: never accepted
    x = np.array([1 / 3 if s else 0.0 for s in S])
    return (rule(adj, x, rank, 1 / 3) - sum(S)) / val


def search(adj, rule, rng, iters):
    n = len(adj)
    S = [rng.random() < 0.15 for _ in range(n)]
    for v in range(n):  # vertices of degree <= 2 cannot lie in U (the cap forces |N[u]| >= 4)
        if len(adj[v]) <= 2 and not (S[v] or any(S[w] for w in adj[v])):
            S[v] = True
    rank = list(range(n)); rng.shuffle(rank)
    cur = score(adj, S, rank, rule)
    for _ in range(iters):
        if rng.random() < 0.5:
            v = rng.randrange(n); S[v] = not S[v]
            new = score(adj, S, rank, rule)
            if new >= cur:
                cur = new
            else:
                S[v] = not S[v]
        else:
            a, b = rng.randrange(n), rng.randrange(n)
            rank[a], rank[b] = rank[b], rank[a]
            new = score(adj, S, rank, rule)
            if new >= cur:
                cur = new
            else:
                rank[a], rank[b] = rank[b], rank[a]
    return cur


def main(seed=1, iters=2000):
    rng = random.Random(seed)
    fams = [("dodecahedron", nx.dodecahedral_graph()), ("pentagon flower k=8", pentagon_flower(8)),
            ("hub pentagons 6,2", hub_pentagons(6, 2, rng)), ("hub pentagons 4,4", hub_pentagons(4, 4, rng))]
    for n in (30, 50, 70):
        fams.append((f"random planar g>=5 n={n}", random_planar_girth(n, 5, rng)))
    for n in (12, 20):
        fams.append((f"subdivided triangulation n={n}", subdivided_triangulation(n, rng)))
    rules = {"hub": lambda a, x, r, t: hubrule(a, x, r, t, 4),
             "hub_all": lambda a, x, r, t: hubrule_all(a, x, r, t, 4), "idrule": idrule}
    m = {k: 0 for k in rules}
    for name, G in fams:
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        out = []
        for k, rule in rules.items():
            r = max(search(adj, rule, rng, iters) for _ in range(3))
            m[k] = max(m[k], r)
            out.append(f"{k}={r:.3f}")
        print(f"{name:30s} n={len(adj):3d} " + "  ".join(out), flush=True)
    print("max:", {k: round(v, 3) for k, v in m.items()})


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
