"""Larger adversarial battery for idrule(1/3) against all fractional dominating sets.
Planar girth >= 5 families, plus non-planar girth >= 5 graphs to see whether planarity matters."""
import random
import sys

import networkx as nx

from adv_round import search
from round_exp import (girth_ok, honeycomb, idrule, pentagon_flower, random_planar_girth,
                       subdivided_triangulation)


def random_girth_regular(d, n, g, rng):
    for _ in range(2000):
        G = nx.random_regular_graph(d, n, seed=rng.randrange(10**9))
        if girth_ok(G, g):
            return G
    return None


def hub_pentagons(k, m, rng):
    """m hubs on a cycle-free skeleton, each carrying k pentagons, pentagons of neighbouring hubs
    glued along an edge: planar, girth 5, several high-degree vertices."""
    G = nx.Graph()
    for h in range(m):
        for i in range(k):
            nx.add_path(G, [("h", h), (h, i, 0), (h, i, 1), (h, i, 2), (h, i, 3), ("h", h)])
        if h:
            G.add_edge((h - 1, 0, 1), (h, 0, 2))
    return nx.convert_node_labels_to_integers(G)


def main(seed=1, iters=3000):
    rng = random.Random(seed)
    fams = []
    for n in (30, 50, 70):
        for g in (5, 6):
            fams.append((f"planar girth>={g} n={n}", True, random_planar_girth(n, g, rng)))
    for n in (15, 20):
        fams.append((f"subdivided triangulation n={n}", True, subdivided_triangulation(n, rng)))
    for k, m in ((6, 2), (4, 4)):
        fams.append((f"hub pentagons k={k} m={m}", True, hub_pentagons(k, m, rng)))
    fams.append(("pentagon flower k=10", True, pentagon_flower(10)))
    fams.append(("honeycomb 8x8 torus", False, honeycomb(8, 8)))
    fams.append(("Petersen", False, nx.petersen_graph()))
    for d, n in ((3, 30), (4, 40), (5, 60)):
        G = random_girth_regular(d, n, 5, rng)
        if G is not None:
            fams.append((f"random {d}-regular girth>=5 n={n}", False, G))
    worst = {True: 0, False: 0}
    for name, planar, G in fams:
        assert girth_ok(G, 5), name
        if planar:
            assert nx.check_planarity(G)[0], name
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        r = max(search(adj, idrule, 1 / 3, rng, iters) for _ in range(3))
        worst[planar] = max(worst[planar], r)
        print(f"{name:34s} n={len(adj):3d} planar={planar!s:5s} idrule 1/3: {r:.3f}", flush=True)
    print(f"max over planar: {worst[True]:.3f}; over non-planar: {worst[False]:.3f}")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
