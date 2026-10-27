"""Deterministic fractional domination on forests by window averaging (no randomness).

Core and hairs as in tree_ldd.py, computed in the forest itself. Windows, as in the proof of
Theorem 5: on every core path p_1..p_m, the hairs of {p_j : |j - i| <= R} for 1 - R <= i <= m + R,
each with weight 1/(2R+1); the hair of every branch vertex (core degree 0 or >= 3) and every
core-free component, with weight 1. x = sum_W wt(W) x^W, with x^W a minimum dominating set of the
forest induced by W (dominating W). Every vertex lies in windows of total weight 1, so x dominates.
Claim (proof in the paper, checked in Lean): sum x <= gamma + B and B <= 72 gamma / R, where
B = sum_W wt(W) |boundary of W|.
"""
import random
from collections import deque

from tree_ldd import branch_heights, trees


def mds_forest(adj, S):
    """Minimum dominating set of the forest induced by S (dominating S), by the 3-state DP."""
    S = set(S); INF = float("inf"); res = set(); seen = set()
    for root in S:
        if root in seen:
            continue
        order, par = [], {root: None}; seen.add(root); st = [root]
        while st:
            v = st.pop(); order.append(v)
            for w in adj[v]:
                if w in S and w not in seen:
                    seen.add(w); par[w] = v; st.append(w)
        # a: v in D; b: v not in D, dominated by a child; c: v not in D, not dominated (parent must)
        a, b, c, ch = {}, {}, {}, {}
        for v in reversed(order):
            kids = [w for w in adj[v] if w in S and par.get(w) == v]
            ch[v] = kids
            a[v] = 1 + sum(min(a[w], b[w], c[w]) for w in kids)
            base = sum(min(a[w], b[w]) for w in kids)
            c[v] = sum(b[w] for w in kids)
            b[v] = base + min((max(0, a[w] - min(a[w], b[w])) for w in kids), default=INF) if kids else INF
        def take(v, state):
            if state == "a":
                res.add(v)
                for w in ch[v]:
                    take(w, min(("a", a[w]), ("b", b[w]), ("c", c[w]), key=lambda t: t[1])[0])
            elif state == "c":
                for w in ch[v]:
                    take(w, "b")
            else:
                best = min(ch[v], key=lambda w: a[w] - min(a[w], b[w]))
                for w in ch[v]:
                    take(w, "a" if w == best else min(("a", a[w]), ("b", b[w]), key=lambda t: t[1])[0])
        take(root, "a" if a[root] <= b[root] else "b")
    return res


def windows(adj, R):
    n = len(adj); h = branch_heights(adj)
    core = [sum(1 for w in adj[v] if h[v][w] >= R) >= 2 for v in range(n)]
    cdeg = [sum(1 for w in adj[v] if core[w]) for v in range(n)]
    # hair of a core vertex: non-core vertices whose path to the core enters it
    att = list(range(n)); q = deque(v for v in range(n) if core[v]); seen = set(q)
    while q:
        v = q.popleft()
        for w in adj[v]:
            if w not in seen and not core[w]:
                seen.add(w); att[w] = att[v]; q.append(w)
    hair = {}
    for v in range(n):
        if v in seen:
            hair.setdefault(att[v], []).append(v)
    out = []
    for v in range(n):                       # core-free components: one window each
        if v not in seen:
            comp, q2 = {v}, deque([v])
            while q2:
                u = q2.popleft()
                for w in adj[u]:
                    if w not in comp:
                        comp.add(w); q2.append(w)
            seen |= comp; out.append((1.0, comp))
    for v in range(n):                       # branch vertices and isolated core vertices
        if core[v] and (cdeg[v] >= 3 or cdeg[v] == 0):
            out.append((1.0, set(hair[v])))
    done = set()
    for v in range(n):                       # core paths: maximal runs of T_c-degree 1 or 2
        if not core[v] or cdeg[v] >= 3 or cdeg[v] == 0 or v in done:
            continue
        path = [v]; done.add(v)
        for direction in (0, 1):
            prev, cur = None, v
            while True:
                nxt = [w for w in adj[cur] if core[w] and w != prev and cdeg[w] in (1, 2) and w not in done]
                if not nxt:
                    break
                prev, cur = cur, nxt[0]; done.add(cur)
                path.append(cur) if direction == 0 else path.insert(0, cur)
        m = len(path)
        for i in range(-R, m + R):
            W = set()
            for j in range(max(0, i - R), min(m, i + R + 1)):
                W |= set(hair[path[j]])
            out.append((1.0 / (2 * R + 1), W))
    return out, sum(core)


def boundary(adj, W):
    return sum(1 for v in W if any(w not in W for w in adj[v]))


if __name__ == "__main__":
    rng = random.Random(2)
    for n in (3000,):
        for name, adj in trees(rng, n):
            gamma = len(mds_forest(adj, range(n)))
            for R in (4, 8, 16):
                ws, ncore = windows(adj, R)
                x = [0.0] * n
                for wt, W in ws:
                    for v in mds_forest(adj, W):
                        x[v] += wt
                wsum = [0.0] * n
                for wt, W in ws:
                    for v in W:
                        wsum[v] += wt
                assert all(abs(t - 1) < 1e-9 for t in wsum), (name, R)      # windows of weight 1
                cover = [sum(x[w] for w in adj[u]) + x[u] for u in range(n)]
                assert min(cover) >= 1 - 1e-9, (name, R, min(cover))
                B = sum(wt * boundary(adj, W) for wt, W in ws)
                exc = sum(x) - gamma
                assert exc <= B + 1e-9, (name, R, exc, B)                   # repair
                assert B <= 72 * gamma / R, (name, R, B)                     # boundary count
                print(f"{name:24s} R={R:3d} gamma={gamma:5d} sum x={sum(x):9.2f} "
                      f"excess*R/gamma={exc * R / gamma:6.2f}  B*R/gamma={B * R / gamma:6.2f}  "
                      f"ratio={sum(x) / gamma:.4f}")
