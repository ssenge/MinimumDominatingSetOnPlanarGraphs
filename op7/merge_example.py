"""Candidate counterexample to piece (a) suggested by the infeasible discharging LP.

Two monotone J-paths a_1..a_n, b_1..b_n; p_i adjacent to a_i and b_i (P-vertices, two smaller J
neighbours); from every p_i a monotone stream r_i of length Lt goes up into a binary merge tree whose
internal vertices (R, two smaller neighbours, one larger) are joined by transit paths of length Lt.
Identifiers: a, b < p < streams, increasing along streams. Every U-vertex of degree < 3 gets private
W leaves. Reports |T| (idrule on F = G[U]) against 3 LP_U.
"""
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog

CAP = 1 / 3 - 1e-9


def build(n, Lt, wmode="private"):
    G = nx.Graph()
    order = []
    a = [("a", i) for i in range(n)]
    b = [("b", i) for i in range(n)]
    nx.add_path(G, a); nx.add_path(G, b)
    order += a + b
    p = [("p", i) for i in range(n)]
    for i in range(n):
        G.add_edge(a[i], p[i]); G.add_edge(b[i], p[i])
    order += p
    # streams: each stream is a list whose last vertex feeds the next merge
    streams = []
    cnt = [0]

    def path_from(start, L, tag):
        prev = start
        verts = []
        for k in range(L):
            v = ("t", tag, k)
            G.add_edge(prev, v); verts.append(v); prev = v
        return prev, verts

    level = []
    for i in range(n):
        end, vs = path_from(p[i], Lt, ("s", i))
        order += vs
        level.append(end)
    lev = 0
    while len(level) > 1:
        nxt = []
        for j in range(0, len(level) - 1, 2):
            m = ("m", lev, j)
            G.add_edge(level[j], m); G.add_edge(level[j + 1], m)
            order.append(m)
            end, vs = path_from(m, Lt, ("u", lev, j))
            order += vs
            nxt.append(end)
        if len(level) % 2:
            nxt.append(level[-1])
        level = nxt
        lev += 1
    F = G.copy()
    U = list(G.nodes())
    for u in U:
        k = 0
        while G.degree(u) < 3:
            w = ("w", u, k); G.add_edge(u, w); k += 1
    rank = {v: i for i, v in enumerate(order)}
    return G, F, U, rank


def idrule_T(F, rank):
    J = {v for v in F if sum(rank[w] < rank[v] for w in F[v]) < sum(rank[w] > rank[v] for w in F[v])}
    R = {v for v in F if v not in J and not any(w in J for w in F[v])}
    return J | R


def lp_u(G, U):
    Us = set(U)
    cols = sorted({w for u in U for w in G[u]} | Us, key=str)
    ci = {v: i for i, v in enumerate(cols)}
    A = np.zeros((len(U), len(cols)))
    for r, u in enumerate(U):
        A[r, ci[u]] = 1
        for w in G[u]:
            A[r, ci[w]] = 1
    res = linprog(np.ones(len(cols)), A_ub=-A, b_ub=-np.ones(len(U)), bounds=(0, CAP), method="highs")
    return res.fun


def main(n=16, Lt=3):
    n, Lt = int(n), int(Lt)
    G, F, U, rank = build(n, Lt)
    T = idrule_T(F, rank)
    lp = lp_u(G, U)
    print(f"n={n} Lt={Lt} |U|={len(U)} |T|={len(T)} |P|={len(U) - len(T)} 3LP_U={3 * lp:.3f} ratio |T|/LP_U={len(T) / lp:.4f}")


if __name__ == "__main__":
    for n in (8, 16, 32, 64):
        for Lt in (0, 1, 2, 3, 4, 6):
            main(n, Lt)


def build_shared(n, Lt):
    """As build, but U-vertices of degree < 3 share W vertices in triples (far apart in order)."""
    G, F, U, rank = build(n, Lt)
    G = F.copy()
    need = []
    for u in U:
        need += [u] * (3 - G.degree(u))
    k = 0
    # pair needs that are far apart in the list to avoid short cycles
    m = len(need)
    step = max(1, m // 3)
    used = [False] * m
    for i in range(m):
        if used[i]:
            continue
        grp = [i]
        j = i + step
        while len(grp) < 3 and j < m:
            if not used[j] and need[j] not in [need[g] for g in grp] and not any(G.has_edge(need[j], need[g]) for g in grp):
                grp.append(j)
            j += 1
        w = ("w", k); k += 1
        for g in grp:
            used[g] = True
            G.add_edge(need[g], w)
    return G, F, U, rank


def main_shared(n, Lt):
    G, F, U, rank = build_shared(n, Lt)
    T = idrule_T(F, rank)
    lp = lp_u(G, U)
    print(f"shared W: n={n} Lt={Lt} |U|={len(U)} |T|={len(T)} 3LP_U={3 * lp:.3f} ratio={len(T) / lp:.4f}", flush=True)


def full_ratio(n, Lt, nd=1):
    """Shared-W instance plus nd D1 vertices; each W joins one D1 vertex (round robin)."""
    from adv_round import lp_given_S
    G, F, U, rank = build_shared(n, Lt)
    Ws = [v for v in G if v not in F]
    for i, w in enumerate(Ws):
        G.add_edge(w, ("d", i % nd))
    nodes = list(G)
    idx = {v: i for i, v in enumerate(nodes)}
    N = len(nodes)
    A = np.eye(N)
    for v in G:
        for w in G[v]:
            A[idx[v], idx[w]] = 1
    S = [isinstance(v, tuple) and v[0] == "d" for v in nodes]
    val = lp_given_S(A, S, 1 / 3)
    T = idrule_T(F, rank)
    D = sum(S) + len(T)
    print(f"full: n={n} Lt={Lt} nd={nd} |D|={D} LP_full={val:.3f} ratio={D / val:.4f}", flush=True)


def full_ratio_private(n, Lt, nd=1):
    from adv_round import lp_given_S
    G, F, U, rank = build(n, Lt)
    Ws = [v for v in G if v not in F]
    for i, w in enumerate(Ws):
        G.add_edge(w, ("d", i % nd))
    nodes = list(G)
    idx = {v: i for i, v in enumerate(nodes)}
    N = len(nodes)
    A = np.eye(N)
    for v in G:
        for w in G[v]:
            A[idx[v], idx[w]] = 1
    S = [isinstance(v, tuple) and v[0] == "d" for v in nodes]
    val = lp_given_S(A, S, 1 / 3)
    T = idrule_T(F, rank)
    D = sum(S) + len(T)
    print(f"full private: n={n} Lt={Lt} nd={nd} |D|={D} LP_full={val:.3f} ratio={D / val:.4f}", flush=True)
