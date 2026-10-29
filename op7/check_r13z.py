"""Instance check of the R13 certificate with U-hubs (discharge_r13z): soundness test of the type model.

For a graph, a set U and identifiers, compute every U-vertex's type in discharge_r13z (U'-, Q_l-,
Q_h-, heavy U-hub vertex part and Z1-types, light U-hubs as "U"-variants), set y = (1 - eps)/3
from the LP solution and check rho * dual(y) >= |D'|, where dual(y) = sum_U y - (1/3) sum_{N[U]}
(Y(v) - 1)^+ is the U-only LP dual. A feasible certificate implies this on every instance; a
violation, or a type missing from the LP, means a modelling bug. Adversarial mode: local search
over U and identifiers maximizing |D'| / dual(y).
Usage: GIRTH=5 python3 check_r13z.py rho seed rounds iters
"""
import os
import pickle
import random
import sys

import networkx as nx

import discharge_r13z as r13z
from check_r13 import idJ, slots
from dense_hub_battery import greedy_girth5, grid_faces
from pent_growth import grow2
from round_exp import _idrule_on, random_planar_girth, subdivided_triangulation
from uhub_cluster import host

HORD = r13z.HORD


def eps_solution(rho, cache_dir):
    path = os.path.join(cache_dir, f"r13z_g{r13z.GIRTH}_eps_{rho}.pkl")
    if os.path.exists(path):
        return pickle.load(open(path, "rb"))
    res, lp, info = r13z.solve(rho)
    assert res.status == 0
    out = {t: float(res.x[v]) for t, v in info["eps"].items()}, -res.fun
    pickle.dump(out, open(path, "wb"))
    return out


def bucket(a):
    return min(a, 6)


def classify(adj, U, rank):
    """Types of the U-vertices under R13 and |D minus D1|."""
    n = len(adj)
    H = [sum(U[w] for w in adj[v]) >= 4 for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    J = idJ(adj, U2, rank)
    T = _idrule_on(adj, U2, rank)
    Z = [U[v] and not U2[v] for v in range(n)]
    Q = [Z[v] and not any(T[w] for w in adj[v]) for v in range(n)]
    Z1 = [Z[v] and not Q[v] for v in range(n)]
    a = [sum(Q[w] for w in adj[v]) if H[v] else -1 for v in range(n)]
    heavy = [H[v] and a[v] >= 4 for v in range(n)]
    HU = [heavy[v] and U[v] for v in range(n)]
    lightU = [H[v] and U[v] and not heavy[v] for v in range(n)]
    choice = {}
    for q in range(n):
        if Q[q]:
            c = [w for w in list(adj[q]) + [q] if heavy[w]]
            if c:
                choice[q] = max(c, key=lambda w: (a[w], -rank[w]))
    Qh = [q in choice for q in range(n)]
    Ql = [Q[v] and not Qh[v] for v in range(n)]
    J2 = idJ(adj, Ql, rank)
    T2 = _idrule_on(adj, Ql, rank)
    nsel = [0] * n
    for q, w in choice.items():
        if not any(T2[u] for u in adj[q]):
            nsel[w] += 1
    size = sum(T) + sum(1 for v in range(n) if nsel[v]) + sum(T2)
    typ = {}
    for v in range(n):
        if not U[v]:
            continue
        nb = [u for u in adj[v] if U[u]]
        if U2[v]:
            typ[v] = ("U", slots(adj, U2, J, rank, v), sum(Qh[u] for u in nb), sum(Ql[u] for u in nb),
                      sum(Z1[u] for u in nb))
        elif Ql[v]:
            fs = slots(adj, Ql, J2, rank, v)
            npp = sum(U2[u] for u in nb)
            nh = sum(Qh[u] for u in nb)
            nz = sum(Z1[u] for u in nb)
            if lightU[v]:
                typ[v] = ("L", fs, 0, nh, 0, 1, "U")
            elif any(lightU[u] for u in nb):
                typ[v] = ("L", fs, npp, nh, nz, 1, "u")
            else:
                iso = not (fs or npp or nh or nz)
                nW = sum(H[w] and not U[w] for w in adj[v])
                typ[v] = ("L", fs, npp, nh, nz, min(2, nW) if iso else 1, "n")
        elif HU[v]:
            w = choice[v]
            ab = bucket(a[w])
            KW = min(3, sum(heavy[u] and not U[u] for u in adj[v]))
            KU = 1 + sum(HU[u] for u in adj[v])
            if ab == 6:
                KU = min(6, KU)
            typ[v] = ("HH", KW, KU, int(w == v), ab, min(2, nsel[w]))
        elif Qh[v]:
            lab = []
            for u in nb:
                if U2[u]:
                    lab.append("P")
                elif HU[u]:
                    lab.append("Hh")
                elif Qh[u]:
                    lab.append("Qh")
                elif Ql[u]:
                    lab.append("QlT" if T2[u] else "QlP")
                else:
                    lab.append("Z1")
            hk = "n"
            if lightU[v]:
                hk = "U"
                lab = [x for x in lab if x != "Z1"]
            us = tuple(sorted(lab, key=HORD.index))
            K = sum(heavy[u] for u in adj[v])
            w = choice[v]
            dom = any(T2[u] for u in adj[v])
            typ[v] = ("H", us, min(3, K - 1), hk, bucket(a[w]), 0 if dom else min(2, nsel[w]))
        else:
            lab = []
            for u in nb:
                if U2[u]:
                    lab.append("T" if T[u] else "P")
                elif HU[u]:
                    lab.append("Hh")
                elif lightU[u]:
                    lab.append("Hl")
                elif Qh[u]:
                    lab.append("Qh")
                elif Ql[u]:
                    lab.append("Ql")
                else:
                    lab.append("Z1")
            typ[v] = ("Z", tuple(sorted(lab)), min(3, sum(H[w] for w in adj[v])))
    return typ, size


def slack(adj, U, rank, eps, rho, ratio=False):
    typ, size = classify(adj, U, rank)
    y = [0.0] * len(adj)
    for v, t in typ.items():
        if t not in eps:
            raise KeyError(f"type not in LP: {t}")
        y[v] = (1 - eps[t]) / 3
    dual = sum(y)
    for v in range(len(adj)):
        if U[v] or any(U[w] for w in adj[v]):
            Y = y[v] + sum(y[w] for w in adj[v])
            dual -= max(0.0, Y - 1) / 3
    if ratio:  # minimized by the search: minus |D'| / dual(y), which must stay >= -rho
        return -size / dual if dual > 0.5 else 0.0
    return rho * dual - size


def graphs(rng):
    out = []
    for n in (30, 60, 90):
        out.append(("planar", random_planar_girth(n, 5, rng)))
    for n in (12, 20, 30):
        out.append(("subdiv", subdivided_triangulation(n, rng)))
    out.append(("greedy", greedy_girth5(60, rng)))
    for m in (4, 5):
        out.append(("grid", grid_faces(m)))
    for k in (10, 25):
        G = host(k, rng)
        out.append(("host", G[0] if isinstance(G, tuple) else G))
    for N in (60, 120):
        out.append(("pent", grow2(N, rng)))
    return out


def main(rho=4.0, seed=1, rounds=30, iters=400, ratio=1):
    rho = float(rho); rng = random.Random(int(seed)); ratio = bool(int(ratio))
    eps, marg = eps_solution(rho, os.path.dirname(os.path.abspath(__file__)) + "/certs")
    print(f"g={r13z.GIRTH} rho={rho} LP margin={marg:.5f} types={len(eps)}", flush=True)
    worst = (1e9, None)
    for name, G in graphs(rng):
        G = nx.convert_node_labels_to_integers(G)
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        n = len(adj)
        best = 1e9
        nhu = 0
        for _ in range(int(rounds)):
            p = rng.choice((0.4, 0.6, 0.8, 1.0))
            U = [rng.random() < p for _ in range(n)]
            rank = list(range(n)); rng.shuffle(rank)
            cur = slack(adj, U, rank, eps, rho, ratio)
            for _ in range(int(iters)):
                if rng.random() < 0.5:
                    v = rng.randrange(n); U[v] = not U[v]
                    new = slack(adj, U, rank, eps, rho, ratio)
                    if new <= cur:
                        cur = new
                    else:
                        U[v] = not U[v]
                else:
                    i, j = rng.randrange(n), rng.randrange(n)
                    rank[i], rank[j] = rank[j], rank[i]
                    new = slack(adj, U, rank, eps, rho, ratio)
                    if new <= cur:
                        cur = new
                    else:
                        rank[i], rank[j] = rank[j], rank[i]
            nhu = max(nhu, sum(1 for v in range(n) if U[v] and sum(U[w] for w in adj[v]) >= 4))
            best = min(best, cur)
        worst = min(worst, (best, name))
        print(f"{name:8s} n={n:3d} U-hubs<={nhu:2d} " + (f"max |D'|/dual(y) = {-best:.4f}" if ratio else
                                                          f"min slack rho*dual-|D'| = {best:.4f}"), flush=True)
    print("overall", worst)


if __name__ == "__main__":
    main(*sys.argv[1:])
