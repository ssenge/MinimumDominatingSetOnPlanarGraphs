"""Planar girth >= 5 version of the merge-forest structure (merge_example.py).

J-path a_0 < ... < a_{4K-1}. Top P-vertices T_k ~ (a_{4k}, a_{4k+3}); bottom P-vertices
B_k ~ (a_{4k+2}, a_{4k+5}). All P-vertices send a stream (Ls transits) into the outer face; the
streams are merged by a comb (stem segments of Lm transits between consecutive merges), first the
top streams left to right, then the bottom streams right to left. In each face between consecutive
streams a W-tripod is attached to the lower stream transit of both streams and to a stem transit;
every other U-vertex of degree < 3 gets W vertices with one U-neighbour. Every face has one D1
vertex adjacent to all W of that face (W of the outer face share one D1 vertex).
Identifiers: a-path, then P-vertices, then streams/stem in topological order.
"""
import sys

import networkx as nx
import numpy as np

from adv_round import lp_given_S
from round_exp import girth_ok, hubrule_all, idrule


def build(K, Ls=1, Lm=3, wmode="tripod"):
    G = nx.Graph()
    order = []
    N = 4 * K
    a = [("a", i) for i in range(N)]
    nx.add_path(G, a); order += a
    Ps = []
    for k in range(K):
        Ps.append((("T", k), 4 * k, 4 * k + 3))
    bot = []
    for k in range(K - 1):
        bot.append((("B", k), 4 * k + 2, 4 * k + 5))
    Ps += bot[::-1]  # cyclic order around the path: top left->right, bottom right->left
    for p, i, j in Ps:
        G.add_edge(p, a[i]); G.add_edge(p, a[j]); order.append(p)
    streams = []
    for idx, (p, i, j) in enumerate(Ps):
        prev, vs = p, []
        for t in range(Ls):
            v = ("s", idx, t); G.add_edge(prev, v); vs.append(v); prev = v
        streams.append(vs)
    # comb: M_1 merges stream 0 and 1; M_k merges stem and stream k
    M = {}
    stem = {}
    M[1] = ("M", 1)
    G.add_edge(streams[0][-1], M[1]); G.add_edge(streams[1][-1], M[1])
    for k in range(1, len(Ps) - 1):
        prev, vs = M[k], []
        for t in range(Lm):
            v = ("m", k, t); G.add_edge(prev, v); vs.append(v); prev = v
        stem[k] = vs
        M[k + 1] = ("M", k + 1)
        G.add_edge(prev, M[k + 1]); G.add_edge(streams[k + 1][-1], M[k + 1])
    # final stem to a sink path
    prev = M[len(Ps) - 1]
    tail = []
    for t in range(Lm):
        v = ("m", len(Ps) - 1, t); G.add_edge(prev, v); tail.append(v); prev = v
    # topological order of the stream part
    for idx in range(len(Ps)):
        order += streams[idx]
    order.append(M[1])
    for k in range(1, len(Ps) - 1):
        order += stem[k]; order.append(M[k + 1])
    order += tail
    U = list(G.nodes())
    S = []
    # faces between stream k and k+1 (k >= 1): tripod on streams[k][0], stem[k][Lm//2], streams[k+1][0]
    if wmode == "tripod":
        for k in range(1, len(Ps) - 1):
            w = ("W", k); d = ("d", k)
            feet = [streams[k][0], stem[k][Lm // 2], streams[k + 1][0]]
            for f in feet:
                G.add_edge(w, f)
            G.add_edge(w, d); S.append(d)
    outer = ("d", "outer")
    S.append(outer)
    for u in U:
        c = 0
        while G.degree(u) < 3:
            w = ("w", u, c); c += 1
            G.add_edge(u, w); G.add_edge(w, outer)
    return G, set(S), order, set(U)


def evaluate(G, S, order):
    nodes = list(G)
    rank_of = {v: i for i, v in enumerate(order)}
    base = len(order)
    extra = [v for v in nodes if v not in rank_of]
    for i, v in enumerate(extra):
        rank_of[v] = base + i
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [sorted(idx[w] for w in G[v]) for v in nodes]
    n = len(nodes)
    A = np.eye(n)
    for v in range(n):
        for w in adj[v]:
            A[v, w] = 1
    Sl = [v in S for v in nodes]
    val = lp_given_S(A, Sl, 1 / 3)
    x = np.array([1 / 3 if s else 0.0 for s in Sl])
    rank = [rank_of[v] for v in nodes]
    return val, idrule(adj, x, rank, 1 / 3), hubrule_all(adj, x, rank, 1 / 3)


def main():
    for wmode in ("tripod", "none"):
        for Ls, Lm in ((1, 3), (2, 3), (1, 4), (2, 5)):
            res = []
            for K in (8, 16):
                G, S, order, U = build(K, Ls, Lm, wmode)
                ok = girth_ok(G, 5) and nx.check_planarity(G)[0]
                val, di, dh = evaluate(G, S, order)
                res.append((val, di, dh, ok))
            (v1, i1, h1, ok1), (v2, i2, h2, ok2) = res
            print(f"{wmode:6s} Ls={Ls} Lm={Lm} planar+girth5={ok1 and ok2} K=16 ratio idrule={i2 / v2:.4f} "
                  f"hub_all={h2 / v2:.4f}  slope idrule={(i2 - i1) / (v2 - v1):.4f}", flush=True)


if __name__ == "__main__":
    main()
