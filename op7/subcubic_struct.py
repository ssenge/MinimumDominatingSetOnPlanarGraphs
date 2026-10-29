"""Structured adversarial families for piece (a): |P| >= Phi_F on subcubic F.

Families (with adversarial identifiers by local search, started from structured orders):
  spider(k, L): k <= 3 legs of length L at one centre;
  subdiv(K, m): cubic graph K, each edge subdivided m times;
  cubic graphs with some edges subdivided;
  caterpillar(n): path with a pendant at every vertex.
"""
import random
import sys

import networkx as nx

from subcubic_phi import phi, leftover


def adv(adj, rng, iters, starts):
    n = len(adj)
    best = None
    for st in starts:
        rank = list(st)
        cur = leftover(adj, rank)
        for _ in range(iters):
            a, b = rng.randrange(n), rng.randrange(n)
            rank[a], rank[b] = rank[b], rank[a]
            new = leftover(adj, rank)
            if new <= cur:
                cur = new
            else:
                rank[a], rank[b] = rank[b], rank[a]
        best = cur if best is None else min(best, cur)
    return best


def subdivide(K, m, edges=None):
    G = nx.Graph()
    G.add_nodes_from(K)
    for k, (u, v) in enumerate(K.edges()):
        if edges is not None and (u, v) not in edges:
            G.add_edge(u, v); continue
        path = [u] + [("s", k, i) for i in range(m)] + [v]
        nx.add_path(G, path)
    return nx.convert_node_labels_to_integers(G, label_attribute="orig")


def topo_starts(G, rng, cnt):
    """Orders that are linear extensions of random acyclic orientations of the base graph."""
    n = G.number_of_nodes()
    out = []
    for _ in range(cnt):
        base = {}
        for v in G:
            o = G.nodes[v].get("orig", v)
            if not isinstance(o, tuple):
                base[o] = base.get(o, rng.random())
        key = {}
        for v in G:
            o = G.nodes[v].get("orig", v)
            if isinstance(o, tuple):
                key[v] = None
            else:
                key[v] = base[o]
        # subdivision vertices: interpolate along their path
        for v in G:
            if key[v] is None:
                key[v] = rng.random()
        order = sorted(G, key=lambda v: key[v])
        rank = [0] * n
        for i, v in enumerate(order):
            rank[v] = i
        out.append(rank)
    return out


def run(name, G, rng, iters=1500):
    G = nx.convert_node_labels_to_integers(G, label_attribute="orig")
    n = G.number_of_nodes()
    adj = [sorted(G[v]) for v in range(n)]
    assert max(len(a) for a in adj) <= 3
    starts = [rng.sample(range(n), n) for _ in range(3)] + [list(range(n))]
    p = adv(adj, rng, iters, starts)
    f = phi(adj)
    print(f"{name:40s} n={n:3d} Phi={f:7.3f} min|P|={p:3d} gap={p - f:6.3f}", flush=True)
    return p - f


def main(seed=1):
    rng = random.Random(seed)
    worst = 1e9
    for L in (3, 6, 12):
        G = nx.Graph()
        for leg in range(3):
            nx.add_path(G, ["c"] + [(leg, i) for i in range(L)])
        worst = min(worst, run(f"spider 3 legs L={L}", G, rng))
    for m in (0, 1, 2, 4):
        for nm, K in (("K4", nx.complete_graph(4)), ("petersen", nx.petersen_graph()),
                      ("dodecahedron", nx.dodecahedral_graph()), ("cube", nx.hypercube_graph(3))):
            worst = min(worst, run(f"{nm} subdivided m={m}", subdivide(K, m), rng))
    for nm, K in (("dodecahedron", nx.dodecahedral_graph()), ("petersen", nx.petersen_graph())):
        E = list(K.edges())
        for frac in (0.2, 0.4, 0.6):
            sel = set(rng.sample(E, int(frac * len(E))))
            worst = min(worst, run(f"{nm} partly subdivided {frac} m=2", subdivide(K, 2, sel), rng))
    for n in (10, 20):
        G = nx.path_graph(n)
        for i in range(n):
            G.add_edge(i, ("leaf", i))
        worst = min(worst, run(f"caterpillar n={n}", G, rng))
    for n in (12, 20, 30):
        G = nx.cycle_graph(n)
        for i in range(n):
            G.add_edge(i, ("leaf", i))
        worst = min(worst, run(f"sun (cycle + pendants) n={n}", G, rng))
    G = nx.random_regular_graph(3, 30, seed=seed)
    worst = min(worst, run("random cubic n=30", G, rng))
    print("worst gap", round(worst, 4))


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
