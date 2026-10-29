"""Search for planar girth >= 5 graphs on which idrule(1/3) is worse than 3 x(V).

The graph is a cycle C_n with increasing identifiers (so idrule takes almost all of it when it lies
in U) plus extra vertices, each either in S = {x >= 1/3} or not. The cheapest x for S is an LP
(adv_round.lp_given_S). Simulated annealing over the extra vertices and their edges.
"""
import math
import random
import sys

import networkx as nx
import numpy as np

from adv_round import lp_given_S
from round_exp import girth_ok, idrule


def score(G, n):
    nodes = list(range(n)) + sorted((v for v in G if v >= n))
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [sorted(idx[w] for w in G[v]) for v in nodes]
    N = len(nodes)
    A = np.eye(N)
    for v in range(N):
        for w in adj[v]:
            A[v, w] = 1
    S = [G.nodes[v].get("S", False) for v in nodes]
    val = lp_given_S(A, S, 1 / 3)
    if val is None:
        return -1
    x = np.array([1 / 3 if s else 0.0 for s in S])
    return idrule(adj, x, list(range(N)), 1 / 3) / val


def ok(G):
    return girth_ok(G, 5) and nx.check_planarity(G)[0]


def search(n, rng, iters, T0=0.02):
    G = nx.cycle_graph(n)
    nxt = n
    for u in range(n):
        G.add_edge(u, nxt); G.add_edge(nxt, nxt + 1); G.nodes[nxt + 1]["S"] = True
        nxt += 2
    cur = score(G, n)
    best, bestG = cur, G.copy()
    for it in range(iters):
        H = G.copy()
        extra = [v for v in H if v >= n]
        r = rng.random()
        if r < 0.45:
            a = rng.choice(list(H)); b = rng.choice(extra)
            if a == b or H.has_edge(a, b):
                continue
            H.add_edge(a, b)
        elif r < 0.75:
            e = [(a, b) for a, b in H.edges() if max(a, b) >= n]
            H.remove_edge(*rng.choice(e))
        elif r < 0.9:
            H.add_edge(rng.choice(list(H)), nxt)
            H.nodes[nxt]["S"] = rng.random() < 0.3
            nxt += 1
        else:
            v = rng.choice(extra)
            H.nodes[v]["S"] = not H.nodes[v].get("S", False)
        H.remove_nodes_from([v for v in list(H) if v >= n and H.degree(v) == 0])
        if not ok(H):
            continue
        new = score(H, n)
        T = T0 * (1 - it / iters) + 1e-6
        if new >= cur or rng.random() < math.exp((new - cur) / T):
            G, cur = H, new
            if cur > best:
                best, bestG = cur, G.copy()
    return best, bestG


def main(seed=1, n=20, iters=4000):
    rng = random.Random(seed)
    best, G = search(n, rng, iters)
    extra = [v for v in G if v >= n]
    print(f"seed={seed} n={n} best={best:.4f} extra={len(extra)} S={sum(G.nodes[v].get('S', False) for v in extra)}",
          flush=True)
    if best > 3 + 1e-6:
        print("EDGES", sorted(G.edges()), "S", [v for v in extra if G.nodes[v].get("S", False)])


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
