"""Can hubs make a monotone path in G[U] cheap to dominate fractionally?

U is a cycle C_n with increasing identifiers, so idrule takes n - 2 of its vertices. The other
vertices are hubs (in W, so not in U). The adversary wants min x(N[U]) small, subject to
x(N[u]) >= 1 for u in U and x < 1/3. Local search over planar girth >= 5 hub structures.
Prints (n - 2) / LP, the ratio of the U-part.
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog

from round_exp import girth_ok

CAP = 1 / 3 - 1e-4


def lp_value(G, n):
    nodes = list(G)
    idx = {v: i for i, v in enumerate(nodes)}
    A = np.zeros((n, len(nodes)))
    for u in range(n):
        A[u, idx[u]] = 1
        for w in G[u]:
            A[u, idx[w]] = 1
    res = linprog(np.ones(len(nodes)), A_ub=-A, b_ub=-np.ones(n), bounds=(0, CAP), method="highs")
    return res.fun if res.status == 0 else None


def valid(G, n):
    return all(G.degree(u) >= 3 for u in range(n)) and girth_ok(G, 5) and nx.check_planarity(G)[0]


def search(n, rng, iters):
    G = nx.cycle_graph(n)
    for u in range(n):
        G.add_edge(u, ("h", u))
    best = lp_value(G, n)
    for it in range(iters):
        H = G.copy()
        hubs = [v for v in H if not isinstance(v, int)]
        r = rng.random()
        if r < 0.6:
            u, h = rng.randrange(n), rng.choice(hubs)
            if H.has_edge(u, h):
                continue
            H.add_edge(u, h)
            if rng.random() < 0.7:  # drop one of u's other hubs
                other = [w for w in H[u] if not isinstance(w, int) and w != h]
                if other:
                    H.remove_edge(u, rng.choice(other))
        elif r < 0.85:
            u = rng.randrange(n)
            other = [w for w in H[u] if not isinstance(w, int)]
            if not other:
                continue
            H.remove_edge(u, rng.choice(other))
        else:
            H.add_edge(rng.randrange(n), ("h", n + it))
        H.remove_nodes_from([v for v in list(H) if not isinstance(v, int) and H.degree(v) == 0])
        if not valid(H, n):
            continue
        val = lp_value(H, n)
        if val is not None and val <= best + 1e-9:
            G, best = H, val
    return G, best


def main(seed=1, iters=3000):
    rng = random.Random(seed)
    for n in (15, 20, 30, 40):
        G, val = search(n, rng, iters)
        hubdeg = sorted((G.degree(v) for v in G if not isinstance(v, int)), reverse=True)
        print(f"n={n:3d}  LP={val:.4f}  ratio={(n - 2) / val:.3f}  hubs={len(hubdeg)} degs={hubdeg[:8]}",
              flush=True)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
