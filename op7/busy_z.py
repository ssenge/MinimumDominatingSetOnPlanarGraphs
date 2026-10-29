"""Busy-Z construction: monotone rail cycle, tripods z on both sides, hub chains on the tripods.

Rail c_0..c_{n-1}, n = 14 K. Top tripods at (14k, 14k+3, 14k+6) and (14k+7, 14k+10, 14k+13);
bottom tripods at (14k+2, 14k+5, 14k+8) and (14k+9, 14k+12, 14k+15). The tripods of each side are
in cyclic order; hub j of a side is adjacent to tripods 3j .. 3j+3 of that side (chains share end
tripods). Rail vertices without a tripod get one W leaf. Full instance: every W vertex (hubs, leaves)
gets a D1 neighbour: even hubs of a side share one D1 vertex, odd hubs and leaves get private ones.
Reports hub rule / LP_U (U-only), and hub rule / LP_full.
"""
import sys

import networkx as nx
import numpy as np

from adv_round import lp_given_S
from round_exp import girth_ok, hubrule, hubrule_all, idrule
from uonly_hub import lp_u


def build(K, chain=3, dmode="shared"):
    n = 14 * K
    G = nx.cycle_graph(n)
    tri = {"t": [], "b": []}
    for k in range(K):
        b = 14 * k
        tri["t"] += [(b, b + 3, b + 6), (b + 7, b + 10, b + 13)]
        tri["b"] += [(b + 2, b + 5, b + 8), (b + 9, b + 12, b + 15)]
    zs = {}
    for side in "tb":
        zs[side] = []
        for i, feet in enumerate(tri[side]):
            z = ("z", side, i)
            for f in feet:
                G.add_edge(z, f % n)
            zs[side].append(z)
    hubs = {"t": [], "b": []}
    for side in "tb":
        m = len(zs[side])
        j = 0
        while chain * j + chain < m + (1 if m % chain == 0 else 0):
            h = ("h", side, j)
            for i in range(chain * j, chain * j + chain + 1):
                G.add_edge(h, zs[side][i % m])
            hubs[side].append(h)
            j += 1
    S = set()
    for v in range(n):
        if G.degree(v) < 3:
            w = ("w", v); G.add_edge(v, w)
            d = ("d", v); G.add_edge(w, d); S.add(d)
    for side in "tb":
        for j, h in enumerate(hubs[side]):
            if dmode == "shared" and j % 2 == 0:
                d = ("D", side)
            else:
                d = ("D", side, j)
            G.add_edge(h, d); S.add(d)
    return G, S, n


def evaluate(G, S, n):
    nodes = list(range(n)) + [v for v in G if not isinstance(v, int)]
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
    x = np.array([1 / 3 if s else 0.0 for s in Sl]); rank = list(range(N))
    res = {k: r(adj, x, rank, 1 / 3) for k, r in (("hub", hubrule), ("hub_all", hubrule_all), ("idrule", idrule))}
    return sum(Sl), uval, full, res


def main():
    for chain in (3, 4):
        for dmode in ("shared", "private"):
            out = []
            for K in (6, 12):
                G, S, n = build(K, chain, dmode)
                ok = girth_ok(G, 5) and nx.check_planarity(G)[0]
                out.append((ok,) + evaluate(G, S, n))
            (ok1, s1, u1, f1, r1), (ok2, s2, u2, f2, r2) = out
            line = f"chain={chain} D1={dmode:7s} planar+girth5={ok1 and ok2} "
            for k in ("hub", "hub_all", "idrule"):
                ru = ((r2[k] - s2) - (r1[k] - s1)) / (u2 - u1)
                rf = (r2[k] - r1[k]) / (f2 - f1)
                line += f"| {k}: U-only {ru:.4f} full {rf:.4f} "
            print(line, flush=True)


if __name__ == "__main__":
    main()
