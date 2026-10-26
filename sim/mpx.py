"""One-shot local clustering of unweighted planar graphs: MPX with capped exponential shifts.

Each vertex v draws delta_v ~ Exp(beta), capped at R. Vertex u joins argmax_v (delta_v - dist(u,v)),
ties to the smaller id. Clusters are connected with strong radius <= R, and u only needs its
R-ball, so this is a local rule. Question: is the cut fraction O(log R / R) on all planar graphs?

usage: python3 mpx.py [seed]
"""
import heapq
import math
import random
import sys

import rules as RU

unit = lambda r: 1


def capped_mpx(Q, R, beta, rng):
    # multi-source Dijkstra on keys (R - delta_v + dist, v): lexicographic min = argmax, ties to min id
    best = {}
    heap = [(R - min(rng.expovariate(beta), R), v, v) for v in Q]
    heapq.heapify(heap)
    while heap:
        k, c, u = heapq.heappop(heap)
        if u in best:
            continue
        best[u] = (k, c)
        for x in Q[u]:
            if x not in best:
                heapq.heappush(heap, (k + 1, c, x))
    return {u: c for u, (k, c) in best.items()}


def cut_fraction(Q, cl):
    m = cut = 0
    for u, nb in Q.items():
        for x in nb:
            if u < x:
                m += 1
                cut += cl[u] != cl[x]
    return cut / m


def bintree(depth):
    Q = {i: {} for i in range(2 ** (depth + 1) - 1)}
    for i in range(1, len(Q)):
        p = (i - 1) // 2
        Q[i][p] = Q[p][i] = 1
    return Q


def hypdisk(levels):
    # concentric cycles, level i has 2^i vertices (i >= 2), each vertex has 2 children: planar, exp growth
    Q, prev = {}, None
    nxt = 0
    for i in range(2, levels + 2):
        cur = list(range(nxt, nxt + 2 ** i))
        nxt += 2 ** i
        for v in cur:
            Q[v] = {}
        for j, v in enumerate(cur):
            w = cur[(j + 1) % len(cur)]
            Q[v][w] = Q[w][v] = 1
            if prev:
                p = prev[j // 2]
                Q[v][p] = Q[p][v] = 1
        prev = cur
    return Q


def rank_mpx(Q, R, beta, rng, base=2.0):
    # degree-priority variant: u joins the highest-rank v (rank = floor log deg) with dist(u,v) <= delta_v,
    # within a rank the max delta_v - dist, then min id. Fixes hub+deg2, not the tree ladder.
    delta = {v: min(rng.expovariate(beta), R) for v in Q}
    rank = {v: int(math.log(max(len(Q[v]), 1), base)) for v in Q}
    cl = {}
    for r in sorted(set(rank.values()), reverse=True):
        heap = [(R - delta[v], v, v, 0) for v in Q if rank[v] == r]
        heapq.heapify(heap)
        seen = set()
        while heap:
            k, c, u, d = heapq.heappop(heap)
            if u in seen:
                continue
            seen.add(u)
            cl.setdefault(u, c)
            for x in Q[u]:
                if x not in seen and d + 1 <= delta[c]:
                    heapq.heappush(heap, (k + 1, c, x, d + 1))
    return cl


def ladder(h):
    # two complete binary trees of depth h, leaf i of each joined by a 2-path: planar, max degree 3.
    # Capped MPX cuts ~0.09 of the edges for every R (Voronoi cells of capped seeds disagree across the rungs).
    T = 2 ** (h + 1) - 1
    Q = {i: {} for i in range(2 * T + 2 ** h)}
    def add(u, v):
        Q[u][v] = Q[v][u] = 1
    for off in (0, T):
        for i in range(1, T):
            add(off + i, off + (i - 1) // 2)
    for j in range(2 ** h):
        add(T - 2 ** h + j, 2 * T + j)
        add(2 * T - 2 ** h + j, 2 * T + j)
    return Q


def relabel(Q, rng):
    ids = list(Q)
    perm = ids[:]
    rng.shuffle(perm)
    m = dict(zip(ids, perm))
    return {m[u]: {m[x]: 1 for x in nb} for u, nb in Q.items()}


def families(rng):
    return {
        "sqgrid300": lambda: RU.fam_sqgrid(300, rng, unit),
        "trigrid300": lambda: RU.fam_trigrid(300, rng, unit),
        "delaunay60k": lambda: RU.fam_delaunay(60000, rng, unit),
        "cubic60k": lambda: RU.fam_cubic(60000, rng, unit),
        "K2n": lambda: RU.fam_k2n(20000, rng, unit),
        "hub+deg2": lambda: RU.fam_hubdeg2(2000, rng, unit),
        "apollon": lambda: RU.fam_stacked(20000, rng, unit),
        "bintree17": lambda: relabel(bintree(17), rng),
        "hypdisk15": lambda: relabel(hypdisk(15), rng),
    }


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    fams = {name: g() for name, g in families(rng).items()}
    for c in (1.0, 2.0):
        print(f"\nbeta = {c} ln(R)/R   (cut fraction; R * cut / ln R in brackets)")
        print(f"{'R':>4}" + "".join(f"{f:>16s}" for f in fams))
        for R in (8, 16, 32, 64):
            beta = c * math.log(R) / R
            row = []
            for Q in fams.values():
                fr = cut_fraction(Q, capped_mpx(Q, R, beta, rng))
                row.append(f"{fr:8.4f} [{fr * R / math.log(R):4.2f}]")
            print(f"{R:>4}" + "".join(f"{s:>16s}" for s in row))


if __name__ == "__main__":
    main()
