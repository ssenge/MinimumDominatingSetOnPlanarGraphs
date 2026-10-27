"""Local low-diameter decomposition of forests (core / hair), checked numerically.

h(v, w): height of the branch of v through its neighbour w = max distance from v to a leaf of it.
Core T_c: vertices with >= 2 branches of height >= R. Hairs hang off T_c with depth <= R.
Cuts: (1) every T_c-edge at a vertex of T_c-degree >= 3, (2) every T_c-edge independently with
probability 1/R, (3) both T_c-edges of a vertex whose uncut T_c-segment reaches beyond distance Lr.
Claim: E[#cut] <= O(n/R) + O(n e^{-Lr/R}), and every cluster has radius <= 2 Lr + R + 1.
Every rule only looks at distance <= Lr + R + 2, so it runs in O(Lr + R) rounds.
"""
import math
import random
import sys
from collections import deque

sys.setrecursionlimit(1 << 20)


def branch_heights(adj):
    """h[v][w] for every arc v->w, by rerooting (two DFS passes per component)."""
    n = len(adj)
    down = [0] * n                   # height of v's subtree in the rooted tree
    h = [dict() for _ in range(n)]
    seen = [False] * n
    for root in range(n):
        if seen[root]:
            continue
        order, parent = [], {root: -1}
        seen[root] = True
        st = [root]
        while st:
            v = st.pop(); order.append(v)
            for w in adj[v]:
                if not seen[w]:
                    seen[w] = True; parent[w] = v; st.append(w)
        for v in reversed(order):
            down[v] = max((down[w] + 1 for w in adj[v] if w != parent[v]), default=0)
            for w in adj[v]:
                if w != parent[v]:
                    h[v][w] = down[w] + 1
        for v in order:              # up[v] = h[v][parent]
            p = parent[v]
            if p == -1:
                continue
            best = max((h[p][w] for w in adj[p] if w != v), default=0)
            h[v][p] = best + 1
    return h


def ldd(adj, R, Lr, rng):
    n = len(adj)
    h = branch_heights(adj)
    core = [sum(1 for w in adj[v] if h[v][w] >= R) >= 2 for v in range(n)]
    cdeg = [sum(1 for w in adj[v] if core[w]) for v in range(n)] if n else []
    cut = set()
    key = lambda u, v: (u, v) if u < v else (v, u)
    marked = {key(u, v) for u in range(n) if core[u] for v in adj[u] if core[v] and u < v and rng.random() < 1 / R}
    for v in range(n):
        if core[v] and cdeg[v] >= 3:
            cut |= {key(v, w) for w in adj[v] if core[w]}
    cut |= marked
    # long segments: walk along T_c-degree-2 paths until a cut edge, an end, or distance Lr
    for v in range(n):
        if not core[v] or cdeg[v] >= 3:
            continue
        long_ = False
        for w0 in (w for w in adj[v] if core[w]):
            prev, cur, d = v, w0, 0
            while True:
                if key(prev, cur) in marked or cdeg[cur] >= 3:
                    break
                d += 1
                if d > Lr:
                    long_ = True; break
                nxt = [w for w in adj[cur] if core[w] and w != prev]
                if not nxt:
                    break
                prev, cur = cur, nxt[0]
            if long_:
                break
        if long_:
            cut |= {key(v, w) for w in adj[v] if core[w]}
    return cut


def radius_ok(adj, cut, bound):
    n = len(adj); comp = [-1] * n; worst = 0
    for s in range(n):
        if comp[s] != -1:
            continue
        members, q = [s], deque([s]); comp[s] = s
        while q:
            v = q.popleft()
            for w in adj[v]:
                if comp[w] == -1 and (min(v, w), max(v, w)) not in cut:
                    comp[w] = s; members.append(w); q.append(w)
        # radius of a tree component = ceil(diameter / 2), via double BFS
        def far(x):
            dist = {x: 0}; q = deque([x])
            while q:
                v = q.popleft()
                for w in adj[v]:
                    if w not in dist and comp[w] == s and (min(v, w), max(v, w)) not in cut:
                        dist[w] = dist[v] + 1; q.append(w)
            y = max(dist, key=dist.get); return y, dist[y]
        a, _ = far(s); _, diam = far(a)
        worst = max(worst, (diam + 1) // 2)
    return worst <= bound, worst


def trees(rng, n):
    def from_parents(par):
        adj = [[] for _ in range(len(par))]
        for v, p in enumerate(par):
            if p >= 0:
                adj[v].append(p); adj[p].append(v)
        return adj
    yield "path", from_parents([i - 1 for i in range(n)])
    yield "caterpillar", from_parents([-1] + [i - 1 if i % 2 else i - 2 if i > 1 else 0 for i in range(1, n)])
    yield "binary", from_parents([(i - 1) // 2 for i in range(n)])
    yield "spider", from_parents([-1] + [0 if i % 200 == 1 else i - 1 for i in range(1, n)])
    yield "random recursive", from_parents([-1] + [rng.randrange(i) for i in range(1, n)])
    yield "random caterpillar-ish", from_parents([-1] + [max(0, i - 1 - (rng.random() < 0.6)) for i in range(1, n)])
    yield "broom", from_parents([i - 1 if i < n // 2 else n // 2 - 1 for i in range(n)])


if __name__ == "__main__":
    rng = random.Random(1)
    n = 20000
    for R in (8, 16, 32, 64):
        Lr = math.ceil(R * math.log(R))
        for name, adj in trees(rng, n):
            cut = ldd(adj, R, Lr, rng)
            ok, worst = radius_ok(adj, cut, 2 * Lr + R + 1)
            assert ok, (name, R, worst)
            print(f"R={R:3d} {name:24s} cut*R/n = {len(cut) * R / n:6.3f}  max radius {worst:5d} (bound {2 * Lr + R + 1})")
