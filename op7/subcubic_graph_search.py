"""Graph-level search for piece (a): minimize min|P| - Phi_F over subcubic graphs F."""
import random
import sys

import networkx as nx

from subcubic_phi import phi, min_P, random_subcubic


def gap(G, rng, iters):
    n = G.number_of_nodes()
    adj = [sorted(G[v]) for v in range(n)]
    return min_P(adj, rng, iters) - phi(adj)


def mutate(G, rng):
    H = G.copy()
    n = H.number_of_nodes()
    if rng.random() < 0.5 and H.number_of_edges() > 0:
        H.remove_edge(*rng.choice(list(H.edges())))
    else:
        a, b = rng.randrange(n), rng.randrange(n)
        if a != b and not H.has_edge(a, b) and H.degree(a) < 3 and H.degree(b) < 3:
            H.add_edge(a, b)
    return H


def main(seed=1, n=14, steps=400, iters=400):
    rng = random.Random(seed)
    G = random_subcubic(n, 0.7, rng)
    cur = gap(G, rng, iters)
    for s in range(steps):
        H = mutate(G, rng)
        g = gap(H, rng, iters)
        if g <= cur + (0.05 if rng.random() < 0.1 else 0):
            G, cur = H, g
        if s % 50 == 0:
            print(f"step {s} gap={cur:.3f} edges={G.number_of_edges()}", flush=True)
    print(f"n={n} final gap={cur:.3f} degs={sorted(d for _, d in G.degree())} edges={sorted(G.edges())}")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
