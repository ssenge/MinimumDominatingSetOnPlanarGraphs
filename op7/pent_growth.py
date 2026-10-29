"""Planar girth-5 graphs rich in adjacent degree-4 vertices, grown pentagon by pentagon, and an
adversarial test of R13 (and R12) on them against LP_U.

Growth: the outer boundary is a cycle; a move takes a boundary segment of L edges (L = 1..4)
whose end vertices are at distance exactly L, and closes it into a pentagon with a new outer path
of 4 - L new vertices. Moves prefer segments whose inner vertices already have degree >= 4, so
the interior looks like a patch of the hyperbolic tiling {5,4} (all interior degrees 4, girth 5).
Test: U = all vertices (every vertex of degree >= 4 is then a U-hub) or U chosen by local search,
identifiers by local search; score |D'| / LP_U.
"""
import random
import sys
from collections import deque

import networkx as nx

import uonly_direct
from clean_battery import direct_search, r12_size_U, r13_size_U
from round_exp import girth_ok


def dist_le(adj, u, w, cap):
    """BFS distance from u to w, or cap + 1 if larger than cap."""
    seen = {u: 0}
    dq = deque([u])
    while dq:
        x = dq.popleft()
        if seen[x] >= cap:
            continue
        for y in adj[x]:
            if y not in seen:
                seen[y] = seen[x] + 1
                if y == w:
                    return seen[y]
                dq.append(y)
    return seen.get(w, cap + 1)


def grow(n_target, rng, maxdeg=5, p3=0.05):
    adj = {i: {(i + 1) % 5, (i - 1) % 5} for i in range(5)}
    B = list(range(5))
    nxt = 5
    stall = 0
    while nxt < n_target and stall < 5000:
        m = len(B)
        i = rng.randrange(m)
        L = rng.choice((2, 3, 3, 4, 4, 1))
        if L >= m - 1:
            stall += 1
            continue
        seg = [B[(i + j) % m] for j in range(L + 1)]
        u, w, inner = seg[0], seg[-1], seg[1:-1]
        k = 4 - L
        if any(len(adj[v]) < 4 for v in inner) and rng.random() > p3:
            stall += 1
            continue
        if len(adj[u]) >= maxdeg or len(adj[w]) >= maxdeg:
            stall += 1
            continue
        if dist_le(adj, u, w, L) != L:
            stall += 1
            continue
        new = list(range(nxt, nxt + k))
        nxt += k
        path = [u] + new + [w]
        for v in new:
            adj[v] = set()
        for a, b in zip(path, path[1:]):
            adj[a].add(b); adj[b].add(a)
        # boundary: u, new..., w replaces u, inner..., w (the new path lies outside)
        start = i
        nb = [B[(start + j) % m] for j in range(m)]
        B = [u] + new + nb[L:]
        stall = 0
    G = nx.Graph()
    for a in adj:
        for b in adj[a]:
            G.add_edge(a, b)
    return nx.convert_node_labels_to_integers(G)


def grow2(n_target, rng, maxdeg=5):
    """Closure-driven growth: close a run of 1-3 consecutive boundary vertices of degree >= 4
    with one pentagon (3 - r new vertices); without such a run, add a pentagon on a boundary
    edge at a vertex of degree 3."""
    adj = {i: {(i + 1) % 5, (i - 1) % 5} for i in range(5)}
    B = list(range(5))
    nxt = 5
    stall = 0
    while nxt < n_target and stall < 2000:
        m = len(B)
        full = [len(adj[v]) >= 4 for v in B]
        runs = []
        for i in range(m):
            if full[i] and not full[(i - 1) % m]:
                r = 0
                while r < 3 and full[(i + r) % m] and r < m - 3:
                    r += 1
                runs.append(((i - 1) % m, r))
        if runs:
            i, r = rng.choice(runs)
            L = r + 1
        else:
            cand = [j for j in range(m) if len(adj[B[j]]) == 3] or list(range(m))
            i = rng.choice(cand)
            L = 1
            if rng.random() < 0.5:
                i = (i - 1) % m
        seg = [B[(i + j) % m] for j in range(L + 1)]
        u, w = seg[0], seg[-1]
        k = 4 - L
        if (len(adj[u]) >= maxdeg or len(adj[w]) >= maxdeg or dist_le(adj, u, w, L) != L
                or L >= m - 1):
            stall += 1
            continue
        new = list(range(nxt, nxt + k))
        nxt += k
        path = [u] + new + [w]
        for v in new:
            adj[v] = set()
        for x, y in zip(path, path[1:]):
            adj[x].add(y); adj[y].add(x)
        nb = [B[(i + j) % m] for j in range(m)]
        B = [u] + new + nb[L:]
        stall = 0
    G = nx.Graph()
    for x in adj:
        for y in adj[x]:
            G.add_edge(x, y)
    return nx.convert_node_labels_to_integers(G)


def rank_search(adj, U, size, rng, iters):
    n = len(adj)
    val = uonly_direct.lp_u(adj, U)
    rank = list(range(n)); rng.shuffle(rank)
    cur = size(adj, U, rank)
    for _ in range(iters):
        a, b = rng.randrange(n), rng.randrange(n)
        rank[a], rank[b] = rank[b], rank[a]
        new = size(adj, U, rank)
        if new >= cur:
            cur = new
        else:
            rank[a], rank[b] = rank[b], rank[a]
    return cur / val


def main(seed=1, iters=3000):
    rng = random.Random(int(seed)); iters = int(iters)
    worst = {}
    for N in (60, 100, 160):
        for rep in range(3):
            G = grow2(N, rng)
            assert girth_ok(G, 5) and nx.check_planarity(G)[0]
            adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
            n = len(adj)
            degs = [len(a) for a in adj]
            nh = sum(d >= 4 for d in degs)
            hh = sum(1 for v in range(n) if degs[v] >= 4 for w in adj[v] if degs[w] >= 4) // 2
            out = []
            for k, size in (("r12", r12_size_U), ("r13", r13_size_U)):
                a = max(rank_search(adj, [d >= 3 for d in degs], size, rng, iters) for _ in range(2))
                b = max(direct_search(adj, size, rng, iters) for _ in range(2))
                worst[k] = max(worst.get(k, 0), a, b)
                out.append(f"{k}: U=deg3+ {a:.3f} U* {b:.3f}")
            print(f"n={n:3d} hubs={nh:3d} hub-hub edges={hh:3d}  " + "  ".join(out), flush=True)
    print("max", {k: round(v, 3) for k, v in worst.items()})


if __name__ == "__main__":
    main(*sys.argv[1:])
