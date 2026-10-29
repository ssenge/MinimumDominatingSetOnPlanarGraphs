"""Experiment: rounding a fractional dominating set x on planar graphs of girth >= 5 or >= 6.

thresh(theta): the threshold rounding of [1, Lemma 3.1]: D1 = {x >= theta}, D2 = V minus N[D1].
idrule(theta): D1 = {x >= theta}; on U = V minus N[D1], a vertex joins if fewer of its U-neighbours
have a smaller identifier than a larger one; every vertex of U that is still undominated joins.

For each graph, x is an optimal LP solution (several, by perturbing the objective), and the
identifiers are chosen adversarially by local search. Reports max |D| / x(V).
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import Delaunay


def girth_ok(G, g):
    """True if G has no cycle of length < g."""
    for s in G:
        dist, par = {s: 0}, {s: None}
        q = [s]
        for v in q:
            if 2 * dist[v] + 1 >= g:
                break
            for w in G[v]:
                if w not in dist:
                    dist[w], par[w] = dist[v] + 1, v
                    q.append(w)
                elif par[v] != w and dist[w] + dist[v] + 1 < g:
                    return False
    return True


def short_cycle_edge(G, g, rng):
    """An edge on a cycle of length < g, or None."""
    nodes = list(G); rng.shuffle(nodes)
    for s in nodes:
        dist, par = {s: 0}, {s: None}
        q = [s]
        for v in q:
            if 2 * dist[v] + 1 >= g:
                break
            for w in G[v]:
                if w not in dist:
                    dist[w], par[w] = dist[v] + 1, v
                    q.append(w)
                elif par[v] != w and dist[w] + dist[v] + 1 < g:
                    return (v, w)
    return None


def random_planar_girth(n, g, rng):
    pts = np.array([[rng.random(), rng.random()] for _ in range(n)])
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for t in Delaunay(pts).simplices:
        for i in range(3):
            G.add_edge(int(t[i]), int(t[(i + 1) % 3]))
    while True:
        e = short_cycle_edge(G, g, rng)
        if e is None:
            break
        G.remove_edge(*e)
    return nx.convert_node_labels_to_integers(G)


def subdivided_triangulation(n, rng):
    """Every edge of a random Delaunay triangulation subdivided once: girth 6, hubs of high degree."""
    pts = np.array([[rng.random(), rng.random()] for _ in range(n)])
    T = nx.Graph()
    for t in Delaunay(pts).simplices:
        for i in range(3):
            T.add_edge(int(t[i]), int(t[(i + 1) % 3]))
    G = nx.Graph()
    for k, (u, v) in enumerate(T.edges()):
        G.add_edge(u, ("s", k)); G.add_edge(("s", k), v)
    return nx.convert_node_labels_to_integers(G)


def pentagon_flower(k):
    """k pentagons sharing one vertex: girth 5, centre of degree 2k."""
    G = nx.Graph()
    for i in range(k):
        a, b, c, d = (i, 0), (i, 1), (i, 2), (i, 3)
        nx.add_path(G, ["c", a, b, c, d, "c"])
    return nx.convert_node_labels_to_integers(G)


def honeycomb(W, H):
    G = nx.Graph()
    for x in range(W):
        for y in range(H):
            G.add_edge((x, y), ((x + 1) % W, y))
            if (x + y) % 2 == 0:
                G.add_edge((x, y), (x, (y + 1) % H))
    return nx.convert_node_labels_to_integers(G)


def lp(adj, rng, perturb):
    n = len(adj)
    A = np.zeros((n, n))
    for v in range(n):
        A[v, v] = 1
        for w in adj[v]:
            A[v, w] = 1
    c = np.ones(n) + (perturb * np.array([rng.random() for _ in range(n)]) if perturb else 0)
    res = linprog(c, A_ub=-A, b_ub=-np.ones(n), bounds=(0, None), method="highs")
    x = res.x
    return x, x.sum()


def thresh(adj, x, rank, theta):
    n = len(adj)
    D1 = [x[v] >= theta - 1e-12 for v in range(n)]
    dom = [D1[v] or any(D1[w] for w in adj[v]) for v in range(n)]
    return sum(D1) + sum(not d for d in dom)


def idrule(adj, x, rank, theta):
    n = len(adj)
    D1 = [x[v] >= theta - 1e-12 for v in range(n)]
    U = [not (D1[v] or any(D1[w] for w in adj[v])) for v in range(n)]
    J = [False] * n
    for v in range(n):
        if U[v]:
            nb = [w for w in adj[v] if U[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    D = [D1[v] or J[v] for v in range(n)]
    # repair, in parallel: every vertex of U not dominated by D1 or J joins
    R = [U[v] and not (D[v] or any(D[w] for w in adj[v])) for v in range(n)]
    return sum(D) + sum(R)


def worst(adj, x, rule, theta, rng, iters):
    n = len(adj)
    rank = list(range(n)); rng.shuffle(rank)
    cur = rule(adj, x, rank, theta)
    for _ in range(iters):
        a, b = rng.randrange(n), rng.randrange(n)
        rank[a], rank[b] = rank[b], rank[a]
        new = rule(adj, x, rank, theta)
        if new >= cur:
            cur = new
        else:
            rank[a], rank[b] = rank[b], rank[a]
    return cur


def main(seed=1, iters=1500):
    rng = random.Random(seed)
    fams = []
    for g in (5, 6):
        for n in (40, 80, 150):
            for _ in range(3):
                fams.append((f"random planar girth>={g} n={n}", g, random_planar_girth(n, g, rng)))
    for n in (15, 30, 60):
        fams.append((f"subdivided triangulation n={n}", 6, subdivided_triangulation(n, rng)))
    for k in (3, 6, 12):
        fams.append((f"pentagon flower k={k}", 5, pentagon_flower(k)))
    for W in (6, 10):
        fams.append((f"honeycomb {W}x{W} torus", 6, honeycomb(W, W)))
    fams.append(("dodecahedron", 5, nx.dodecahedral_graph()))
    fams.append(("honeycomb 12x12 torus", 6, honeycomb(12, 12)))
    res = {}
    for name, g, G in fams:
        assert girth_ok(G, g), name
        if g == 5:
            assert nx.check_planarity(G)[0] or "torus" in name
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        a = g / (g - 2)
        out = []
        xs = []
        x0, val = lp(adj, rng, 0)
        xs.append((x0, val))
        avg = sum(lp(adj, rng, 1e-7)[0] for _ in range(20)) / 20
        xs.append((avg, avg.sum()))
        degs = {len(a) for a in adj}
        if len(degs) == 1:
            d = degs.pop()
            xs.append((np.full(len(adj), 1 / (d + 1)), len(adj) / (d + 1)))
        for x, val in xs:
            for rname, rule, theta in (("thresh 1/(2a+1)", thresh, 1 / (2 * a + 1)),
                                       ("idrule 1/3", idrule, 1 / 3),
                                       ("idrule 1/(2a+1)", idrule, 1 / (2 * a + 1))):
                r = worst(adj, x, rule, theta, rng, iters) / val
                res.setdefault((g, rname), []).append(r)
                out.append(f"{rname}={r:.2f}")
        print(f"{name:34s} " + "  ".join(out[-3:]), flush=True)
    for (g, rname), v in sorted(res.items()):
        print(f"girth>={g}  {rname:16s} max |D|/x(V) = {max(v):.3f}  (2a+1 = {(3 * g - 2) / (g - 2):.3f})")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))


def hubrule(adj, x, rank, theta, tmin=4):
    """D1 = {x >= theta}; hubs H = vertices outside U with >= tmin neighbours in U join D;
    idrule (parallel repair) on U' = U minus N(H)."""
    n = len(adj)
    D1 = [x[v] >= theta - 1e-12 for v in range(n)]
    U = [not (D1[v] or any(D1[w] for w in adj[v])) for v in range(n)]
    H = [not U[v] and not D1[v] and sum(U[w] for w in adj[v]) >= tmin for v in range(n)]
    U2 = [U[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    J = [False] * n
    for v in range(n):
        if U2[v]:
            nb = [w for w in adj[v] if U2[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    R = [U2[v] and not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    return sum(D1) + sum(H) + sum(J) + sum(R)


def hubrule_all(adj, x, rank, theta, tmin=4):
    """As hubrule, but every vertex outside D1 with >= tmin neighbours in U is a hub, also inside U.
    idrule then runs on a subcubic U' = U minus N[H]."""
    n = len(adj)
    D1 = [x[v] >= theta - 1e-12 for v in range(n)]
    U = [not (D1[v] or any(D1[w] for w in adj[v])) for v in range(n)]
    H = [not D1[v] and sum(U[w] for w in adj[v]) >= tmin for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    J = [False] * n
    for v in range(n):
        if U2[v]:
            nb = [w for w in adj[v] if U2[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    R = [U2[v] and not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    return sum(D1) + sum(H) + sum(J) + sum(R)


def hubrule_clean(adj, x, rank, theta, tmin=4):
    """hubrule_all followed by a cleanup: a hub outside U leaves D if every U-neighbour of it is
    dominated by T (has a T-neighbour). Hubs inside U stay. Never larger than hubrule_all."""
    n = len(adj)
    D1 = [x[v] >= theta - 1e-12 for v in range(n)]
    U = [not (D1[v] or any(D1[w] for w in adj[v])) for v in range(n)]
    H = [not D1[v] and sum(U[w] for w in adj[v]) >= tmin for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    J = [False] * n
    for v in range(n):
        if U2[v]:
            nb = [w for w in adj[v] if U2[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    R = [U2[v] and not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    Tset = [J[v] or R[v] for v in range(n)]
    domT = [Tset[v] or any(Tset[w] for w in adj[v]) for v in range(n)]
    keep = [H[v] and (U[v] or any(U[w] and not domT[w] for w in adj[v])) for v in range(n)]
    return sum(D1) + sum(keep) + sum(Tset)


def uhub_idrule(adj, x, rank, theta, tmin=4):
    """D1 = {x >= theta}; vertices of U with >= tmin neighbours in U (U-hubs) join D; idrule
    (parallel repair) on the subcubic rest U minus H_U. Hubs outside U never join."""
    n = len(adj)
    D1 = [x[v] >= theta - 1e-12 for v in range(n)]
    U = [not (D1[v] or any(D1[w] for w in adj[v])) for v in range(n)]
    HU = [U[v] and sum(U[w] for w in adj[v]) >= tmin for v in range(n)]
    U2 = [U[v] and not HU[v] for v in range(n)]
    J = [False] * n
    for v in range(n):
        if U2[v]:
            nb = [w for w in adj[v] if U2[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    R = [U2[v] and not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    return sum(D1) + sum(HU) + sum(J) + sum(R)


def _idrule_on(adj, S, rank):
    """idrule (parallel repair) on G[S]: the set J + R, which dominates S."""
    n = len(adj)
    J = [False] * n
    for v in range(n):
        if S[v]:
            nb = [w for w in adj[v] if S[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    return [S[v] and (J[v] or not any(J[w] for w in adj[v])) for v in range(n)]


def hubrule_r12(adj, x, rank, theta, tmin=4):
    """D1 = {x >= theta}, U, hubs H (>= tmin U-neighbours, also inside U), Z = U n N(H) minus H,
    U' = U minus N[H], T = idrule(G[U']). Q = (Z + H_U) minus N(T); a_w = |N(w) n Q| for hubs.
    Heavy hubs: a_w >= 4. A vertex of Q with a heavy hub in its closed neighbourhood selects one of
    maximum load (smallest identifier on ties); the rest Q_l runs idrule on the subcubic G[Q_l]."""
    n = len(adj)
    D1 = [x[v] >= theta - 1e-12 for v in range(n)]
    U = [not (D1[v] or any(D1[w] for w in adj[v])) for v in range(n)]
    H = [not D1[v] and sum(U[w] for w in adj[v]) >= tmin for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    T = _idrule_on(adj, U2, rank)
    Q = [U[v] and not U2[v] and not any(T[w] for w in adj[v]) for v in range(n)]
    a = [sum(Q[w] for w in adj[v]) if H[v] else -1 for v in range(n)]
    sel = [False] * n
    Ql = [False] * n
    for q in range(n):
        if not Q[q]:
            continue
        cands = [w for w in adj[q] + [q] if H[w] and a[w] >= 4]
        if cands:
            w = max(cands, key=lambda w: (a[w], -rank[w]))
            sel[w] = True
        else:
            Ql[q] = True
    T2 = _idrule_on(adj, Ql, rank)
    return sum(D1) + sum(T) + sum(sel) + sum(T2)


def hubrule_r13(adj, x, rank, theta, tmin=4):
    """R12, except that a vertex of Q_h with a neighbour in T2 does not select (it is dominated).
    Every selection that remains is the one R12 makes, so |D| never exceeds R12's."""
    n = len(adj)
    D1 = [x[v] >= theta - 1e-12 for v in range(n)]
    U = [not (D1[v] or any(D1[w] for w in adj[v])) for v in range(n)]
    return sum(D1) + r13_size(adj, U, rank, tmin)


def r13_size(adj, U, rank, tmin=4):
    """|D minus D1| of R13 for a given set U of undominated vertices."""
    n = len(adj)
    H = [sum(U[w] for w in adj[v]) >= tmin for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    T = _idrule_on(adj, U2, rank)
    Q = [U[v] and not U2[v] and not any(T[w] for w in adj[v]) for v in range(n)]
    a = [sum(Q[w] for w in adj[v]) if H[v] else -1 for v in range(n)]
    choice = {}
    Ql = [False] * n
    for q in range(n):
        if Q[q]:
            c = [w for w in adj[q] + [q] if H[w] and a[w] >= 4]
            if c:
                choice[q] = max(c, key=lambda w: (a[w], -rank[w]))
            else:
                Ql[q] = True
    T2 = _idrule_on(adj, Ql, rank)
    sel = [False] * n
    for q, w in choice.items():
        if not any(T2[u] for u in adj[q]):
            sel[w] = True
    return sum(T) + sum(sel) + sum(T2)

