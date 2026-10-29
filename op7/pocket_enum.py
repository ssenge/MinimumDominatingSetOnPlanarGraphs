"""Exhaustive search over periodic hub structures around a monotone cycle.

Cycle C_n, n = P * K, identifiers increasing along the cycle (so idrule takes all but O(1) of it).
Each side (top, bottom) has a mega hub adjacent to the positions = offset (mod P); this cuts the
side into pockets of length P. Inside every pocket the same family of nested hubs is placed: hubs
with pairwise disjoint position intervals, neighbours spaced >= 3 apart. One D1 vertex per pocket
is adjacent to the mega hub and to all nested hubs of the pocket (the cheapest way to dominate them).
For every configuration: check planarity and girth >= 5, then report the per-period limit of
idrule / LP (adv_round) as the number K of periods grows.
"""
import itertools
import sys

import networkx as nx
import numpy as np

from adv_round import lp_given_S
from round_exp import girth_ok, idrule


def hub_families(P, kmax=3):
    """All families of at most kmax hubs inside a pocket with interior positions 1..P-1."""
    sets = []
    for size in range(1, P):
        for c in itertools.combinations(range(1, P), size):
            if all(b - a >= 3 for a, b in zip(c, c[1:])):
                sets.append(c)
    fams = [()]
    for k in range(1, kmax + 1):
        for fam in itertools.combinations(sets, k):
            iv = sorted((h[0], h[-1]) for h in fam)
            if all(a[1] < b[0] for a, b in zip(iv, iv[1:])):
                fams.append(fam)
    return fams


def build(P, K, top, bot, off):
    n = P * K
    G = nx.cycle_graph(n)
    S = set()
    for side, fam, o in (("t", top, 0), ("b", bot, off)):
        M = (side, "M")
        G.add_edge(M, (side, "qM")); S.add((side, "qM"))
        for k in range(K):
            base = o + P * k
            G.add_edge(base % n, M)
            q = (side, "q", k)
            if fam:  # a pocket without nested hubs needs no D1 vertex
                G.add_edge(q, M); S.add(q)
            for j, h in enumerate(fam):
                H = (side, "h", k, j)
                for p in h:
                    G.add_edge((base + p) % n, H)
                G.add_edge(H, q)
    return G, S, n


def ratio(G, S, n):
    if any(G.degree(u) < 3 for u in range(n)):
        return None
    if not (girth_ok(G, 5) and nx.check_planarity(G)[0]):
        return None
    nodes = list(range(n)) + [v for v in G if not isinstance(v, int)]
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [sorted(idx[w] for w in G[v]) for v in nodes]
    N = len(nodes)
    A = np.eye(N)
    for v in range(N):
        for w in adj[v]:
            A[v, w] = 1
    Sl = [v in S for v in nodes]
    val = lp_given_S(A, Sl, 1 / 3)
    if val is None:
        return None
    D = idrule(adj, np.array([1 / 3 if s else 0.0 for s in Sl]), list(range(N)), 1 / 3)
    return D, val


def limit_ratio(P, top, bot, off, K1=6, K2=12):
    """Per-period ratio as K -> infinity: slope of |D| over slope of the LP value."""
    r1 = ratio(*build(P, K1, top, bot, off))
    if r1 is None:
        return None
    r2 = ratio(*build(P, K2, top, bot, off))
    return (r2[0] - r1[0]) / (r2[1] - r1[1])


def main(Pmax=8):
    best = []
    for P in range(3, Pmax + 1):
        fams = hub_families(P)
        cnt = 0
        top_best = (0, None)
        for top, bot in itertools.product(fams, repeat=2):
            for off in range(P):
                r = limit_ratio(P, top, bot, off)
                if r is None:
                    continue
                cnt += 1
                if r > top_best[0]:
                    top_best = (r, (top, bot, off))
        print(f"P={P} families={len(fams)} valid={cnt} best={top_best[0]:.4f} at {top_best[1]}", flush=True)
        best.append((top_best[0], P, top_best[1]))
    print("overall", max(best))


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
