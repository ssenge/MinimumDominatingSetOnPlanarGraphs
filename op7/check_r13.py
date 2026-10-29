"""Instance check of the R13 certificate (discharge_r13): soundness test of the type model.

For a graph, a set U without U-hubs and identifiers, compute every vertex's R13 type, set
y = (1 - eps(type))/3 from the LP solution and check rho * dual(y) >= |D minus D1|, where
dual(y) = sum_U y - (1/3) sum_{N[U]} (Y(v) - 1)^+ is the U-only LP dual. A feasible certificate
implies this for every instance; a violation (or a type missing from the LP) means a modelling bug.
Adversarial mode: local search over U and identifiers minimizing rho * dual - |D'|.
"""
import os
import pickle
import random
import sys

import networkx as nx

import discharge_a2 as d2
import discharge_r13 as r13
from dense_hub_battery import greedy_girth5, grid_faces
from round_exp import _idrule_on, random_planar_girth, subdivided_triangulation
from uhub_cluster import host

HORD = ("P", "Qh", "QlT", "QlP", "Z1")


def eps_solution(rho, cache_dir):
    path = os.path.join(cache_dir, f"r13_eps_{rho}.pkl")
    if os.path.exists(path):
        return pickle.load(open(path, "rb"))
    res, lp, info = r13.solve(rho)
    assert res.status == 0
    out = {t: float(res.x[v]) for t, v in info["eps"].items()}, -res.fun
    pickle.dump(out, open(path, "wb"))
    return out


def slots(adj, S, J, rank, v):
    return tuple(sorted(("i" if rank[u] < rank[v] else "o", int(J[u]), sum(S[w] for w in adj[u]))
                        for u in adj[v] if S[u]))


def idJ(adj, S, rank):
    J = [False] * len(adj)
    for v in range(len(adj)):
        if S[v]:
            nb = [w for w in adj[v] if S[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    return J


def classify(adj, U, rank):
    """Types of the U-vertices under R13 (None if U has a hub) and |D minus D1|."""
    n = len(adj)
    if any(U[v] and sum(U[w] for w in adj[v]) >= 4 for v in range(n)):
        return None, None
    H = [not U[v] and sum(U[w] for w in adj[v]) >= 4 for v in range(n)]
    U2 = [U[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    J = idJ(adj, U2, rank)
    T = _idrule_on(adj, U2, rank)
    Z = [U[v] and not U2[v] for v in range(n)]
    Q = [Z[v] and not any(T[w] for w in adj[v]) for v in range(n)]
    Z1 = [Z[v] and not Q[v] for v in range(n)]
    a = [sum(Q[w] for w in adj[v]) if H[v] else -1 for v in range(n)]
    heavy = [H[v] and a[v] >= 4 for v in range(n)]
    Qh = [Q[v] and any(heavy[w] for w in adj[v]) for v in range(n)]
    Ql = [Q[v] and not Qh[v] for v in range(n)]
    J2 = idJ(adj, Ql, rank)
    T2 = _idrule_on(adj, Ql, rank)
    sel = [False] * n
    for q in range(n):
        if Qh[q] and not any(T2[u] for u in adj[q]):
            c = [w for w in adj[q] if heavy[w]]
            sel[max(c, key=lambda w: (a[w], -rank[w]))] = True
    size = sum(T) + sum(sel) + sum(T2)
    typ = {}
    for v in range(n):
        if not U[v]:
            continue
        nb = [u for u in adj[v] if U[u]]
        if U2[v]:
            fs = slots(adj, U2, J, rank, v)
            typ[v] = ("U", fs, sum(Qh[u] for u in nb), sum(Ql[u] for u in nb), sum(Z1[u] for u in nb))
        elif Ql[v]:
            fs = slots(adj, Ql, J2, rank, v)
            npp = sum(U2[u] for u in nb)
            nh = sum(Qh[u] for u in nb)
            nz = sum(Z1[u] for u in nb)
            nlh = min(2, sum(H[w] for w in adj[v])) if not nb else 1
            typ[v] = ("L", fs, npp, nh, nz, nlh)
        elif Qh[v]:
            lab = []
            for u in nb:
                lab.append("P" if U2[u] else "Qh" if Qh[u] else ("QlT" if T2[u] else "QlP") if Ql[u] else "Z1")
            us = tuple(sorted(lab, key=HORD.index))
            typ[v] = ("H", us, min(3, sum(heavy[w] for w in adj[v]) - 1))
        else:
            lab = ["T" if (U2[u] and T[u]) else "P" if U2[u] else "Qh" if Qh[u] else "Ql" if Ql[u] else "Z1"
                   for u in nb]
            typ[v] = ("Z", tuple(sorted(lab)), min(3, sum(H[w] for w in adj[v])))
    return typ, size


def slack(adj, U, rank, eps, rho, ratio=False):
    typ, size = classify(adj, U, rank)
    if typ is None:
        return None
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
    return out


def no_uhub(adj, U, rng):
    order = list(range(len(adj))); rng.shuffle(order)
    for v in order:
        if U[v] and sum(U[w] for w in adj[v]) >= 4:
            U[v] = False
    changed = True
    while changed:
        changed = False
        for v in order:
            if U[v] and sum(U[w] for w in adj[v]) >= 4:
                U[v] = False; changed = True
    return U


def main(rho=3.25, seed=1, rounds=40, iters=400, ratio=1):
    rho = float(rho); rng = random.Random(int(seed)); ratio = bool(int(ratio))
    eps, marg = eps_solution(rho, os.path.dirname(os.path.abspath(__file__)) + "/certs")
    print(f"rho={rho} LP margin={marg:.5f} types={len(eps)}", flush=True)
    worst = (1e9, None)
    for name, G in graphs(rng):
        G = nx.convert_node_labels_to_integers(G)
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        n = len(adj)
        best = 1e9
        for _ in range(int(rounds)):
            U = no_uhub(adj, [rng.random() < rng.choice((0.4, 0.6, 0.8)) for _ in range(n)], rng)
            rank = list(range(n)); rng.shuffle(rank)
            cur = slack(adj, U, rank, eps, rho, ratio)
            for _ in range(int(iters)):
                if rng.random() < 0.5:
                    v = rng.randrange(n); U[v] = not U[v]
                    new = slack(adj, U, rank, eps, rho, ratio)
                    if new is not None and new <= cur:
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
            best = min(best, cur)
        worst = min(worst, (best, name))
        print(f"{name:8s} n={n:3d} " + (f"max |D'|/dual(y) = {-best:.4f}" if ratio else
                                          f"min slack rho*dual-|D'| = {best:.4f}"), flush=True)
    print("overall min slack", worst)


if __name__ == "__main__":
    main(*sys.argv[1:])
