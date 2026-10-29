"""Piece (a) of OP7.md observation 7, hub-free subcubic case.

F = G[U] subcubic, every W vertex with <= 3 U-neighbours. Then 3 LP_U >= |U| - Phi_F with
  Phi_F = min over eps in [0,1]^U of  sum eps + (1/3) sum_{v of degree 3} (1 - eps(N[v]))^+
(dual y = (1 - eps)/3). So idrule satisfies |T| <= 3 LP_U if |P| >= Phi_F, P = U minus T.
Test: adversarial identifiers (local search minimizing |P|) on random subcubic graphs, and a
graph-level search maximizing Phi_F - min |P|.
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog


def phi(adj):
    n = len(adj)
    V3 = [v for v in range(n) if len(adj[v]) == 3]
    if not V3:
        return 0.0
    # variables: eps_0..eps_{n-1}, s_v for v in V3
    m = len(V3)
    c = np.concatenate([np.ones(n), np.full(m, 1 / 3)])
    A = np.zeros((m, n + m))
    for i, v in enumerate(V3):
        for u in [v] + adj[v]:
            A[i, u] = -1
        A[i, n + i] = -1
    r = linprog(c, A_ub=A, b_ub=-np.ones(m), bounds=[(0, 1)] * n + [(0, None)] * m, method="highs")
    return r.fun


def leftover(adj, rank):
    n = len(adj)
    J = [False] * n
    for v in range(n):
        sm = sum(rank[w] < rank[v] for w in adj[v])
        J[v] = sm < len(adj[v]) - sm
    R = [not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    return sum(1 for v in range(n) if not J[v] and not R[v])


def min_P(adj, rng, iters):
    n = len(adj)
    best = None
    for _ in range(3):
        rank = list(range(n)); rng.shuffle(rank)
        cur = leftover(adj, rank)
        for _ in range(iters):
            a, b = rng.randrange(n), rng.randrange(n)
            rank[a], rank[b] = rank[b], rank[a]
            new = leftover(adj, rank)
            if new <= cur:
                cur = new
            else:
                rank[a], rank[b] = rank[b], rank[a]
        best = cur if best is None else min(best, cur)
    return best


def random_subcubic(n, p3, rng):
    G = nx.Graph(); G.add_nodes_from(range(n))
    target = [3 if rng.random() < p3 else rng.choice((1, 2)) for _ in range(n)]
    stubs = [v for v in range(n) for _ in range(target[v])]
    rng.shuffle(stubs)
    for i in range(0, len(stubs) - 1, 2):
        a, b = stubs[i], stubs[i + 1]
        if a != b and not G.has_edge(a, b) and G.degree(a) < 3 and G.degree(b) < 3:
            G.add_edge(a, b)
    return G


def main(seed=1, trials=300, iters=800):
    rng = random.Random(seed)
    worst = None
    for t in range(trials):
        n = rng.choice((8, 12, 16, 24, 32))
        G = random_subcubic(n, rng.choice((0.2, 0.4, 0.6, 0.8, 1.0)), rng)
        adj = [sorted(G[v]) for v in range(n)]
        f = phi(adj)
        p = min_P(adj, rng, iters)
        gap = p - f
        if worst is None or gap < worst[0]:
            worst = (gap, n, f, p, sorted(G.edges()))
            print(f"trial {t}: n={n} Phi={f:.3f} min|P|={p} gap={gap:.3f}", flush=True)
    print("worst gap", worst[:4])


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
