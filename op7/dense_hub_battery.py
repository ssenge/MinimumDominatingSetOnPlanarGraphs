"""Adversarial battery on hub-dense planar girth >= 5 graphs (many adjacent vertices of degree >= 4).

Families: greedy maximal girth-5 subgraphs of Delaunay triangulations (average degree near 10/3),
the subdivided square grid with one vertex per face joined to two opposite subdivision vertices,
and the Cairo-like greedy completion of a pentagon flower ring. Rules: hubrule_all, hubrule, idrule,
against the cheapest fractional dominating set for the adversary's D1 (adv_round.search).
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.spatial import Delaunay

from adv_round import search
from round_exp import girth_ok, hubrule, hubrule_all, idrule


def greedy_girth5(n, rng):
    pts = np.array([[rng.random(), rng.random()] for _ in range(n)])
    E = set()
    for t in Delaunay(pts).simplices:
        for i in range(3):
            a, b = int(t[i]), int(t[(i + 1) % 3])
            E.add((min(a, b), max(a, b)))
    E = list(E); rng.shuffle(E)
    G = nx.Graph(); G.add_nodes_from(range(n))
    for a, b in E:
        # adding ab keeps girth >= 5 iff dist(a, b) >= 4 in the current graph
        try:
            d = nx.shortest_path_length(G, a, b)
        except nx.NetworkXNoPath:
            d = 99
        if d >= 4:
            G.add_edge(a, b)
    return G


def grid_faces(m):
    Q = nx.grid_2d_graph(m, m)
    G = nx.Graph()
    sub = {}
    for (u, v) in Q.edges():
        s = ("s", u, v)
        G.add_edge(u, s); G.add_edge(s, v); sub[frozenset((u, v))] = s
    for i in range(m - 1):
        for j in range(m - 1):
            f = ("f", i, j)
            # opposite subdivision vertices of the face: bottom and top edges, or left and right
            if (i + j) % 2 == 0:
                a = sub[frozenset(((i, j), (i + 1, j)))]; b = sub[frozenset(((i, j + 1), (i + 1, j + 1)))]
            else:
                a = sub[frozenset(((i, j), (i, j + 1)))]; b = sub[frozenset(((i + 1, j), (i + 1, j + 1)))]
            G.add_edge(f, a); G.add_edge(f, b)
    return nx.convert_node_labels_to_integers(G)


def main(seed=1, iters=2500):
    rng = random.Random(int(seed))
    fams = []
    for n in (30, 45, 60):
        for _ in range(2):
            fams.append((f"greedy maximal girth5 n={n}", greedy_girth5(n, rng)))
    for m in (4, 5):
        fams.append((f"subdivided grid + face vertices m={m}", grid_faces(m)))
    worst = {}
    for name, G in fams:
        assert girth_ok(G, 5) and nx.check_planarity(G)[0], name
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        degs = sorted((len(a) for a in adj), reverse=True)
        out = []
        for rname, rule in (("hub_all", hubrule_all), ("hub", hubrule), ("idrule", idrule)):
            r = max(search(adj, rule, 1 / 3, rng, int(iters)) for _ in range(2))
            worst[rname] = max(worst.get(rname, 0), r)
            out.append(f"{rname}={r:.3f}")
        avg = sum(degs) / len(degs)
        print(f"{name:38s} n={len(adj):3d} avgdeg={avg:.2f} #deg>=4={sum(d >= 4 for d in degs):3d}  " + "  ".join(out), flush=True)
    print("max:", {k: round(v, 3) for k, v in worst.items()})


if __name__ == "__main__":
    main(*sys.argv[1:])
