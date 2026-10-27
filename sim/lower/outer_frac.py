"""Deterministic fractional domination on bounded-degree outerplanar graphs by window averaging.

Faces of length <= ell are bags, longer faces are holes. Decomposition D: short faces, thin edges (in no
short face) and vertex nodes (vertices in >= 2 pieces; a piece is an ell-block or a thin edge). A vertex
node is joined to one face of each ell-block at it (smallest index) and to its thin edges. In the proof
D is unfolded into its universal cover; here every hole has length >= 12(R + ell), so the explorations
below (radius <= R + ell) never wrap around a hole and can be done in G itself.
Core: nodes with >= 2 directions of height >= R. Windows: phi-bands of length R on core paths and core
cycles (weight 1/R per integer shift), branch nodes (core degree != 2) and core-free components (weight 1),
each with its hairs. x^W: optimal LP solution on N[W] that dominates W.
Checked: coverage exactly 1, domination, sum x - gamma_f <= B (B = sum over windows of wt * sum of the
adhesions of the D-edges they cut), and B * R / n bounded.
Randomized version: on every core path, cut the edges with mu > R and then the edges whose ends pick
different anchors (the edge of smallest Exp(mu) clock among the edges within psi-distance R). Checked:
E[#long + #anchor cuts] <= 18 n / R, the bound of the proof.
"""
import random
import sys
from collections import deque

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def generate(n, delta, ell, hole, rng, p_pend=0.1, p_hole=0.003):
    """Random outerplanar graph, max degree delta, faces of length <= ell or in [hole, 2 hole]."""
    adj = [{1}, {0}]
    faces, outer = [], [(0, 1)]
    while len(adj) < n:
        if rng.random() < p_pend:
            v = rng.randrange(len(adj))
            if len(adj[v]) < delta:
                adj.append({v}); adj[v].add(len(adj) - 1); outer.append((v, len(adj) - 1))
            continue
        i = rng.randrange(len(outer)); a, b = outer[i]
        if len(adj[a]) >= delta or len(adj[b]) >= delta:
            continue
        k = rng.randint(hole, 2 * hole) - 2 if rng.random() < p_hole else rng.randint(1, ell - 2)
        path = [a] + list(range(len(adj), len(adj) + k)) + [b]
        adj += [set() for _ in range(k)]
        for x, y in zip(path, path[1:]):
            adj[x].add(y); adj[y].add(x)
        faces.append(path)
        outer[i] = outer[-1]; outer.pop()
        outer += list(zip(path, path[1:]))
    return [sorted(s) for s in adj], faces


def bfs(adj, src, cap, allowed=None):
    dist = {s: 0 for s in src}; q = deque(src)
    while q:
        v = q.popleft()
        if dist[v] < cap:
            for w in adj[v]:
                if w not in dist and (allowed is None or w in allowed):
                    dist[w] = dist[v] + 1; q.append(w)
    return dist


def decompose(adj, faces, ell):
    n = len(adj); key = lambda u, v: (min(u, v), max(u, v))
    short = [f for f in faces if len(f) <= ell]
    ef = {}
    for i, f in enumerate(short):
        for x, y in zip(f, f[1:] + f[:1]):
            ef.setdefault(key(x, y), []).append(i)
    par = list(range(len(short)))
    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for fs in ef.values():
        if len(fs) == 2:
            par[find(fs[0])] = find(fs[1])
    thin = [key(u, w) for u in range(n) for w in adj[u] if u < w and key(u, w) not in ef]
    bags = [frozenset(f) for f in short] + [frozenset(e) for e in thin]
    nbr = [set() for _ in bags]
    def link(a, b):
        nbr[a].add(b); nbr[b].add(a)
    for fs in ef.values():
        if len(fs) == 2:
            link(*fs)
    pieces = [{} for _ in range(n)]
    for i, f in enumerate(short):
        for v in f:
            pieces[v].setdefault(("B", find(i)), i)
    for j, e in enumerate(thin):
        for v in e:
            pieces[v][("E", j)] = len(short) + j
    for v in range(n):
        if len(pieces[v]) != 1:
            bags.append(frozenset([v])); nbr.append(set())
            for node in pieces[v].values():
                link(len(bags) - 1, node)
    return bags, nbr


def windows(adj, bags, nbr, R, ell):
    m = len(bags)
    def high(a, b):
        X = bags[a] & bags[b]; d = bfs(adj, list(X), R)
        seen = {b}; q = deque([b])
        while q:
            c = q.popleft()
            if any(d.get(z, R) >= R for z in bags[c]):
                return True
            for e in nbr[c]:
                if e != a and e not in seen and min(d.get(z, R + 1) for z in bags[e]) <= R:
                    seen.add(e); q.append(e)
        return False
    core = [sum(high(a, b) for b in nbr[a]) >= 2 for a in range(m)]
    att = [a if core[a] else -1 for a in range(m)]
    q = deque(a for a in range(m) if core[a])
    while q:
        a = q.popleft()
        for b in nbr[a]:
            if att[b] == -1:
                att[b] = att[a]; q.append(b)
    owner = {}
    for a in range(m):
        for v in bags[a]:
            owner.setdefault(v, a)
    hv, hn = {}, {}
    for v, a in owner.items():
        hv.setdefault(att[a], set()).add(v)
    for a in range(m):
        hn.setdefault(att[a], set()).add(a)
    out = []                                           # (weight, vertex set, node set or None)
    seen = set()
    for a in range(m):
        if att[a] == -1 and a not in seen:
            comp = {a}; qq = deque([a])
            while qq:
                for y in nbr[qq.popleft()]:
                    if y not in comp:
                        comp.add(y); qq.append(y)
            seen |= comp
            out.append((1.0, {v for v, o in owner.items() if o in comp}, None))
    cdeg = [sum(core[b] for b in nbr[a]) if core[a] else -1 for a in range(m)]
    for a in range(m):
        if cdeg[a] not in (-1, 2):
            out.append((1.0, hv.get(a, set()), hn[a]))
    done, ncyc, paths = set(), 0, []
    for a in range(m):
        if cdeg[a] != 2 or a in done:
            continue
        path = [a]; done.add(a)
        for direction in (0, 1):
            prev, cur = None, a
            while True:
                nxt = [b for b in nbr[cur] if core[b] and b != prev and cdeg[b] == 2 and b not in done]
                if not nxt:
                    break
                prev, cur = cur, nxt[0]; done.add(cur)
                path.append(cur) if direction == 0 else path.insert(0, cur)
        L = len(path); cyc = L >= 3 and path[-1] in nbr[path[0]]
        lam = []
        for i, x in enumerate(path):
            cn = [b for b in nbr[x] if core[b]]
            if cyc:
                prv, nxt = path[i - 1], path[(i + 1) % L]
            else:
                prv = path[i - 1] if i > 0 else None
                nxt = path[i + 1] if i + 1 < L else None
                prv = prv if prv is not None else next(b for b in cn if b != nxt)
                nxt = nxt if nxt is not None else next(b for b in cn if b != prv)
            d = bfs(adj, list(bags[x] & bags[prv]), ell)
            lam.append(max(1, min(d[z] for z in bags[x] & bags[nxt])))
        mu = [lam[i] + lam[(i + 1) % L] for i in range(L)]     # edge lengths, independent of direction
        phi = np.concatenate([[0], np.cumsum(mu)])
        ncyc += cyc; paths.append((mu if cyc else mu[:-1], cyc))
        if cyc:
            P = int(phi[L]); assert P >= R, "core cycle shorter than R"
            shifts = [(t, [x for x, p in zip(path, phi) if (p - t) % P < R]) for t in range(P)]
        else:
            shifts = [(t, [x for x, p in zip(path, phi) if t <= p < t + R])
                      for t in range(-R + 1, int(phi[len(path) - 1]) + 1)]
        for t, xs in shifts:
            out.append((1.0 / R, set().union(*(hv.get(x, set()) for x in xs)), set().union(*(hn[x] for x in xs))))
    return out, sum(core), ncyc, paths


def anchor_cuts(mu, cyc, R, rng):
    """Cut edges of one core path (edge i joins nodes i and i + 1, mod len(mu) on a cycle)."""
    m = len(mu); L = m if cyc else m + 1
    clock = [rng.expovariate(x) for x in mu]
    anchor = []
    for p in range(L):
        best = None
        for step, j in ((1, p), (-1, p - 1)):
            d = 0
            while (cyc or 0 <= j < m) and mu[j % m] <= R and d + mu[j % m] <= R:
                d += mu[j % m]
                if best is None or clock[j % m] < clock[best]:
                    best = j % m
                j += step
        anchor.append(best)
    return sum(x > R or anchor[i] != anchor[(i + 1) % L] for i, x in enumerate(mu))


def lp(adj, dom, support):
    sup = sorted(support); col = {v: i for i, v in enumerate(sup)}; dom = sorted(dom)
    A = lil_matrix((len(dom), len(sup)))
    for r, u in enumerate(dom):
        for w in [u] + list(adj[u]):
            A[r, col[w]] = -1
    res = linprog(np.ones(len(sup)), A_ub=A.tocsr(), b_ub=-np.ones(len(dom)), bounds=(0, None),
                  method="highs")
    assert res.status == 0
    return dict(zip(sup, res.x)), res.fun


def check(adj, bags, nbr, ws):
    n = len(adj)
    cover = np.zeros(n)
    for wt, W, _ in ws:
        cover[list(W)] += wt
    assert np.allclose(cover, 1), cover.min()
    _, gf = lp(adj, range(n), range(n))
    x, cache, B = np.zeros(n), {}, 0.0
    for wt, W, nodes in (w for w in ws if w[1]):
        k = frozenset(W)
        if k not in cache:
            cache[k] = lp(adj, W, W | {w for v in W for w in adj[v]})[0]
        for v, val in cache[k].items():
            x[v] += wt * val
        if nodes is not None:
            B += wt * sum(len(bags[a] & bags[b]) for a in nodes for b in nbr[a] if b not in nodes)
    assert all(x[u] + sum(x[w] for w in adj[u]) >= 1 - 1e-7 for u in range(n))
    exc = x.sum() - gf
    assert exc <= B + 1e-6, (exc, B)
    rad = 0
    for _, W, _ in ws:
        left = set(W)
        while left:
            comp = bfs(adj, [left.pop()], n, W); left -= set(comp)
            far = max(comp, key=comp.get); rad = max(rad, (max(bfs(adj, [far], n, W).values()) + 1) // 2)
    return gf, x.sum(), B, rad


def ring(L, bead):
    """Cycle of length L (one hole); bead: a triangle on every second edge."""
    adj = [{(i - 1) % L, (i + 1) % L} for i in range(L)]; faces = [list(range(L))]
    for i in range(0, L if bead else 0, 2):
        a, b, c = i, (i + 1) % L, len(adj); adj.append({a, b}); adj[a].add(c); adj[b].add(c)
        faces.append([a, c, b])
    return [sorted(x) for x in adj], faces


def theta(L, k):
    """k holes of length L in a row, consecutive holes sharing an edge (a cycle with k - 1 chords)."""
    n = k * (L - 2) + 2; adj = [set() for _ in range(n)]
    top, bot = [0], [1]; faces = []; nxt = 2; prev = (0, 1)
    for _ in range(k):
        side = list(range(nxt, nxt + L - 2)); nxt += L - 2
        cyc = [prev[0]] + side + [prev[1]]
        for x, y in zip(cyc, cyc[1:] + cyc[:1]):
            adj[x].add(y); adj[y].add(x)
        faces.append(cyc); prev = (side[(L - 2) // 2 - 1], side[(L - 2) // 2])
    return [sorted(x) for x in adj], faces


def families(R, ell, rng):
    hole = 12 * (R + ell)
    yield "ring", *ring(2 * hole, False)
    yield "beaded ring", *ring(2 * hole, True)
    yield "theta x4", *theta(hole, 4)
    for delta in (3, 4, 6):
        yield f"random delta={delta}", *generate(2000, delta, ell, hole, rng)


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    for R in (4, 8, 16):
        ell = R
        for name, adj, faces in families(R, ell, rng):
            bags, nbrs = decompose(adj, faces, ell)
            ws, ncore, ncyc, paths = windows(adj, bags, nbrs, R, ell)
            gf, sx, B, rad = check(adj, bags, nbrs, ws)
            n = len(adj); holes = sum(len(f) > ell for f in faces)
            cut = np.mean([sum(anchor_cuts(mu, cyc, R, rng) for mu, cyc in paths) for _ in range(20)])
            assert cut <= 18 * n / R, (cut, n, R)
            print(f"R={R:2d} {name:16s} n={n:4d} holes={holes} core cycles={ncyc} gamma_f={gf:7.1f} "
                  f"ratio={sx / gf:.4f} excess*R/n={(sx - gf) * R / n:5.2f} B*R/n={B * R / n:5.2f} "
                  f"radius/(R+ell)={rad / (R + ell):4.2f} anchor cut*R/n={cut * R / n:5.2f}", flush=True)
