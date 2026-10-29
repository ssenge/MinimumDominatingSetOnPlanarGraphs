"""Does idrule(1/3) need planarity? Dense non-planar graphs of girth >= 5."""
import itertools
import random

import networkx as nx

from adv_round import search
from round_exp import girth_ok, idrule


def pg_incidence(q):
    """Point-line incidence graph of PG(2, q), q prime: (q+1)-regular, girth 6."""
    pts = []
    for v in itertools.product(range(q), repeat=3):
        if any(v):
            first = next(c for c in v if c)
            inv = pow(first, q - 2, q)
            w = tuple(c * inv % q for c in v)
            if w not in pts:
                pts.append(w)
    G = nx.Graph()
    for i, p in enumerate(pts):
        for j, l in enumerate(pts):
            if sum(a * b for a, b in zip(p, l)) % q == 0:
                G.add_edge(("p", i), ("l", j))
    return nx.convert_node_labels_to_integers(G)


rng = random.Random(3)
for name, G in (("PG(2,2) Heawood", pg_incidence(2)), ("PG(2,3)", pg_incidence(3)),
                ("PG(2,5)", pg_incidence(5)), ("Hoffman-Singleton", nx.hoffman_singleton_graph())):
    assert girth_ok(G, 5)
    adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
    r = max(search(adj, idrule, 1 / 3, rng, 1500) for _ in range(2))
    print(f"{name:20s} n={len(adj):3d} deg={len(adj[0])}  idrule 1/3: {r:.3f}", flush=True)
