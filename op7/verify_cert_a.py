"""Check the discharging certificate of discharge_a2.py on concrete subcubic graphs.

Solve the LP at a feasible rho, read eps(type) and kappa(arc type pair), then on random subcubic
graphs with random and adversarial orders recompute every vertex charge directly and assert >= 0.
Also check the summed inequality |T| <= (rho/3)(sum (1 - eps) - (1/3) sum_{deg 3} (1 - eps(N[v]))^+).
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

import discharge_a2 as D
from subcubic_phi import random_subcubic


def solve(rho, with_s=False):
    T = D.all_types(with_s)
    eps = {t: i for i, t in enumerate(T)}
    nv = len(T)
    kap = {}
    for tu in T:
        for tv in T:
            if D.slot_of(tv, tu, "i", with_s) in set(tv) and D.slot_of(tu, tv, "o", with_s) in set(tu):
                kap[(tu, tv)] = nv; nv += 1
    mvar = {}
    for t in T:
        for sl in set(t):
            for ver in ("A", "B"):
                mvar[(t, sl, ver)] = nv; nv += 1
    rows, rhs = [], []
    for (tu, tv), k in kap.items():
        slv = D.slot_of(tv, tu, "i", with_s); slu = D.slot_of(tu, tv, "o", with_s)
        rows += [[(mvar[(tv, slv, "A")], 1), (k, 1)], [(mvar[(tv, slv, "B")], 1), (k, 1), (eps[tu], -rho / 9)],
                 [(mvar[(tu, slu, "A")], 1), (k, -1)], [(mvar[(tu, slu, "B")], 1), (k, -1), (eps[tv], -rho / 9)]]
        rhs += [0, 0, 0, 0]
    for t in T:
        inT = 0.0 if D.cls(t) == "P" else 1.0
        cnt = {}
        for sl in t:
            cnt[sl] = cnt.get(sl, 0) + 1
        rows.append([(eps[t], rho / 3)] + [(mvar[(t, sl, "A")], -c) for sl, c in cnt.items()]); rhs.append(rho / 3 - inT)
        if len(t) == 3:
            rows.append([(eps[t], rho / 3 - rho / 9)] + [(mvar[(t, sl, "B")], -c) for sl, c in cnt.items()])
            rhs.append(rho / 3 - rho / 9 - inT)
    A = lil_matrix((len(rows), nv))
    for i, row in enumerate(rows):
        for k, v in row:
            A[i, k] += v
    bounds = [(0, 1)] * len(T) + [(-50, 50)] * (nv - len(T))
    r = linprog(np.zeros(nv), A_ub=A.tocsr(), b_ub=np.array(rhs), bounds=bounds, method="highs")
    assert r.status == 0
    return {t: r.x[eps[t]] for t in T}, {p: r.x[k] for p, k in kap.items()}


def vtype(adj, rank, v, J):
    sl = []
    for w in adj[v]:
        sl.append(("i" if rank[w] < rank[v] else "o", int(J[w]), len(adj[w])))
    return tuple(sorted(sl))


def check(adj, rank, epsT, kapT, rho):
    n = len(adj)
    J = [sum(rank[w] < rank[v] for w in adj[v]) < sum(rank[w] > rank[v] for w in adj[v]) for v in range(n)]
    R = [not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    inT = [J[v] or R[v] for v in range(n)]
    ty = [vtype(adj, rank, v, J) for v in range(n)]
    e = [epsT[ty[v]] for v in range(n)]
    worst = 1e9
    total = 0.0
    for v in range(n):
        assert D.cls(ty[v]) == ("J" if J[v] else ("R" if R[v] else "P")), (ty[v], J[v], R[v])
        ch = rho / 3 * (1 - e[v]) - (1 if inT[v] else 0)
        if len(adj[v]) == 3:
            ch -= rho / 9 * max(0.0, 1 - e[v] - sum(e[w] for w in adj[v]))
        for w in adj[v]:
            if rank[w] > rank[v]:
                ch += kapT[(ty[v], ty[w])]
            else:
                ch -= kapT[(ty[w], ty[v])]
        worst = min(worst, ch)
        total += ch
    return worst, total


def main(rho=3.14, trials=400, seed=1):
    rho = float(rho)
    epsT, kapT = solve(rho)
    rng = random.Random(int(seed))
    worst = 1e9
    for t in range(int(trials)):
        n = rng.choice((10, 20, 40, 80))
        G = random_subcubic(n, rng.choice((0.3, 0.6, 0.9, 1.0)), rng)
        adj = [sorted(G[v]) for v in range(n)]
        rank = list(range(n)); rng.shuffle(rank)
        w, tot = check(adj, rank, epsT, kapT, rho)
        worst = min(worst, w)
    print(f"rho={rho}: min vertex charge over {trials} random instances = {worst:.6f}")


if __name__ == "__main__":
    main(*sys.argv[1:])
