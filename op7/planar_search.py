"""Joint annealing over planar girth >= 5 graphs, the set U and the identifiers (U-only setting).

Graphs are edge subsets of a fixed Delaunay triangulation (so always planar); an edge can be added
only if it keeps girth >= 5. Score: (|H| + |T|) / LP_U for a rule, where LP_U = min x(N[U]) with
x(N[u]) >= 1 for u in U and 0 <= x <= 1/3 (infeasible: score -1). Rules get (adj, U, rank).
"""
import math
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import Delaunay

CAP = 1 / 3 - 1e-7


def lp_u(adj, U):
    us = [u for u in range(len(adj)) if U[u]]
    if not us:
        return None
    cols = sorted({w for u in us for w in adj[u]} | set(us))
    ci = {v: i for i, v in enumerate(cols)}
    A = np.zeros((len(us), len(cols)))
    for r, u in enumerate(us):
        A[r, ci[u]] = 1
        for w in adj[u]:
            A[r, ci[w]] = 1
    res = linprog(np.ones(len(cols)), A_ub=-A, b_ub=-np.ones(len(us)), bounds=(0, CAP), method="highs")
    return res.fun if res.status == 0 else None


def idrule_on(adj, U2, rank):
    n = len(adj)
    J = [False] * n
    for v in range(n):
        if U2[v]:
            nb = [w for w in adj[v] if U2[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    R = [U2[v] and not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    return sum(J) + sum(R)


def hub_all(adj, U, rank):
    n = len(adj)
    cnt = [sum(U[w] for w in adj[v]) for v in range(n)]
    H = [cnt[v] >= 4 for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    return sum(H) + idrule_on(adj, U2, rank)


def idrule_u(adj, U, rank):
    return idrule_on(adj, U, rank)


RULES = {"hub_all": hub_all, "idrule": idrule_u}


def girth_add_ok(adj_sets, a, b):
    # dist(a, b) >= 4 in current graph
    frontier, seen = {a}, {a}
    for _ in range(3):
        nxt = set()
        for v in frontier:
            for w in adj_sets[v]:
                if w == b:
                    return False
                if w not in seen:
                    seen.add(w); nxt.add(w)
        frontier = nxt
    return True


def anneal(n, rule, rng, steps, T0=0.05):
    pts = np.array([[rng.random(), rng.random()] for _ in range(n)])
    E = set()
    for t in Delaunay(pts).simplices:
        for i in range(3):
            a, b = int(t[i]), int(t[(i + 1) % 3])
            E.add((min(a, b), max(a, b)))
    E = list(E)
    adj = [set() for _ in range(n)]
    order = E[:]; rng.shuffle(order)
    for a, b in order:
        if girth_add_ok(adj, a, b):
            adj[a].add(b); adj[b].add(a)
    U = [len(adj[v]) >= 3 and rng.random() < 0.7 for v in range(n)]
    rank = list(range(n)); rng.shuffle(rank)
    f = RULES[rule]

    def score():
        al = [sorted(s) for s in adj]
        val = lp_u(al, U)
        if not val:
            return -1.0
        return f(al, U, rank) / val

    cur = score(); best = (cur, None)
    for s in range(steps):
        T = T0 * (1 - s / steps) + 1e-4
        r = rng.random()
        undo = None
        if r < 0.3:
            v = rng.randrange(n); U[v] = not U[v]; undo = ("U", v)
        elif r < 0.6:
            a, b = rng.randrange(n), rng.randrange(n)
            rank[a], rank[b] = rank[b], rank[a]; undo = ("R", a, b)
        else:
            a, b = rng.choice(E)
            if b in adj[a]:
                adj[a].discard(b); adj[b].discard(a); undo = ("E-", a, b)
            elif girth_add_ok(adj, a, b):
                adj[a].add(b); adj[b].add(a); undo = ("E+", a, b)
            else:
                continue
        new = score()
        if new >= cur or rng.random() < math.exp((new - cur) / T):
            cur = new
            if cur > best[0]:
                best = (cur, ([sorted(x) for x in adj], U[:], rank[:]))
        else:
            if undo[0] == "U":
                U[undo[1]] = not U[undo[1]]
            elif undo[0] == "R":
                rank[undo[1]], rank[undo[2]] = rank[undo[2]], rank[undo[1]]
            elif undo[0] == "E-":
                adj[undo[1]].add(undo[2]); adj[undo[2]].add(undo[1])
            else:
                adj[undo[1]].discard(undo[2]); adj[undo[2]].discard(undo[1])
    return best


def describe(adj, U, rank, rule):
    n = len(adj)
    cnt = [sum(U[w] for w in adj[v]) for v in range(n)]
    H = [cnt[v] >= 4 for v in range(n)]
    nH = sum(H); nHU = sum(H[v] and U[v] for v in range(n))
    Z = [U[v] and not H[v] and any(H[w] for w in adj[v]) for v in range(n)]
    return f"|U|={sum(U)} |H|={nH} (in U {nHU}) |Z|={sum(Z)} LP_U={lp_u(adj, U):.3f} D={RULES[rule](adj, U, rank)}"


def main(rule="hub_all", n=40, steps=20000, seed=1, restarts=3):
    rng = random.Random(int(seed))
    overall = (0, None)
    for r in range(int(restarts)):
        b = anneal(int(n), rule, rng, int(steps))
        print(f"restart {r}: best {b[0]:.4f}  " + (describe(*b[1], rule) if b[1] else ""), flush=True)
        if b[0] > overall[0]:
            overall = b
    print(f"{rule} n={n}: max {overall[0]:.4f}")
    if overall[1]:
        import pickle
        pickle.dump(overall, open(f"planar_search_best_{rule}_{n}_{seed}.pkl", "wb"))


if __name__ == "__main__":
    main(*sys.argv[1:])
