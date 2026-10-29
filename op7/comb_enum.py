"""Hub pockets attached through pendant vertices (a comb), U-only and full LP.

Monotone cycle p_0..p_{n-1}, n = P*K. Top side: a mega hub at positions = 0 (mod P) and in each
pocket a family of nested hubs (pocket_enum.hub_families). A position used by a top hub is in mode
'z' or 'p' (bitmask): in mode z the cycle vertex gets a pendant U-vertex z_i and the hubs attach to
z_i, in mode p they attach to p_i directly. Every U-vertex of degree < 3 gets private W leaves,
each dominated by its own D1 vertex. Hubs are dominated by one D1 vertex per pocket.
Reports, as K grows, the slopes of (rule - |D1|) / LP_U and rule / LP_full for hubrule, hubrule_all
and idrule.
"""
import itertools
import sys

import networkx as nx
import numpy as np

from adv_round import lp_given_S
from pocket_enum import hub_families
from round_exp import girth_ok, hubrule, hubrule_all, idrule
from uonly_hub import lp_u


def build(P, K, fam, mask):
    n = P * K
    G = nx.cycle_graph(n)
    S = set()
    M = ("M",)
    G.add_edge(M, ("qM",)); S.add(("qM",))
    U = set(range(n))

    def anchor(i):
        pos = i % P
        if pos in mask:
            z = ("z", i)
            if z not in G:
                G.add_edge(i, z)
                U.add(z)
            return z
        return i

    for k in range(K):
        base = P * k
        G.add_edge(anchor(base), M)
        q = ("q", k)
        if fam:
            G.add_edge(q, M); S.add(q)
        for j, h in enumerate(fam):
            H = ("h", k, j)
            for p in h:
                G.add_edge(anchor(base + p), H)
            G.add_edge(H, q)
    for u in list(U):
        t = 0
        while G.degree(u) < 3:
            w, d = ("w", u, t), ("d", u, t)
            G.add_edge(u, w); G.add_edge(w, d); S.add(d)
            t += 1
    return G, S


def evaluate(G, S):
    if not (girth_ok(G, 5) and nx.check_planarity(G)[0]):
        return None
    nodes = sorted(G, key=lambda v: (not isinstance(v, int), str(v)))
    # identifiers: cycle increasing, everything else above it
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [sorted(idx[w] for w in G[v]) for v in nodes]
    N = len(nodes)
    Sl = [v in S for v in nodes]
    A = np.eye(N)
    for v in range(N):
        for w in adj[v]:
            A[v, w] = 1
    full = lp_given_S(A, Sl, 1 / 3)
    uval, _ = lp_u(adj, Sl)
    if full is None or uval is None:
        return None
    x = np.array([1 / 3 if s else 0.0 for s in Sl]); rank = list(range(N))
    rules = {k: r(adj, x, rank, 1 / 3) for k, r in (("hub", hubrule), ("all", hubrule_all), ("id", idrule))}
    return sum(Sl), uval, full, rules


def main(Pmax=7):
    best = {}
    for P in range(3, Pmax + 1):
        for fam in hub_families(P):
            used = sorted({0} | {p for h in fam for p in h})
            for r in range(1, len(used) + 1):
                for mask in itertools.combinations(used, r):
                    res = [evaluate(*build(P, K, fam, set(mask))) for K in (6, 12)]
                    if None in res:
                        continue
                    (s1, u1, f1, r1), (s2, u2, f2, r2) = res
                    for k in r1:
                        ru = ((r2[k] - s2) - (r1[k] - s1)) / (u2 - u1)
                        rf = (r2[k] - r1[k]) / (f2 - f1)
                        for key, val in ((k + "/U", ru), (k + "/full", rf)):
                            if val > best.get(key, (0,))[0]:
                                best[key] = (round(val, 4), P, fam, mask)
        print(P, {k: v for k, v in sorted(best.items())}, flush=True)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
