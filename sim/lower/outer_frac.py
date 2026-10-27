"""Fractional domination on outerplanar graphs (any maximum degree) by window averaging.

Faces of length <= ell are bags, longer faces are holes. Decomposition D: short faces, thin edges (in no
short face) and vertex nodes (vertices in >= 2 pieces; a piece is an ell-block or a thin edge). A vertex
node is joined to one face of each ell-block at it (smallest index) and to its thin edges. In the proof
D is unfolded into its universal cover; here every hole has length >= 12(R + ell), so the explorations
below never wrap around a hole and can be done in G itself.
Core: nodes with >= 2 directions of height >= R. Core paths are measured by runs: on a core path with
adhesions X_j, the run of v is the interval of j with v in X_j, and a run is maximal if no other run
strictly contains it. mu_j = 1 / rho_j + (lam(p_j) + lam(p_{j+1})) / 2, where rho_j is the length of the
shortest maximal run through j and lam(p) = d(X_in, X_out) if these adhesions are disjoint, else 0.
Windows: psi-bands of length R for every real shift (weight dtau / R), branch nodes (core degree != 2)
and core-free components (weight 1), each with its hairs. x^W: optimal LP solution on N[W] that
dominates W.
Checked: coverage exactly 1, domination, sum x - gamma_f <= B (B = sum over windows of wt * sum of the
adhesions of the D-edges they cut). Reported: B * R / gamma_f and psi / gamma_f (bounded independently
of the maximum degree), and the eccentricity in G of the windows.
Randomized version: on every core path, cut the edges with mu > R and then the edges whose ends pick
different anchors (the edge of smallest Exp(mu) clock among the edges within psi-distance R). Checked:
E[#long + #anchor cuts] <= 3 * psi / R, the bound of the proof.
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


def run_rho(X, cyc):
    """rho_j for every edge j of a core path (cycles are unrolled three times, middle copy used)."""
    m = len(X); seq = X * 3 if cyc else X; M = len(seq)
    st, en = {}, {}
    for i in range(M):
        for v in seq[i]:
            st[i, v] = st[i - 1, v] if i and v in seq[i - 1] else i
    for i in reversed(range(M)):
        for v in seq[i]:
            en[i, v] = en[i + 1, v] if i + 1 < M and v in seq[i + 1] else i
    def maximal(i, v):
        s, e = st[i, v], en[i, v]
        return not any(u != v and st[s, u] <= s and en[s, u] >= e and (st[s, u], en[s, u]) != (s, e)
                       for u in seq[s])
    return [min(en[i, v] - st[i, v] + 1 for v in seq[i] if maximal(i, v))
            for i in (range(m, 2 * m) if cyc else range(m))]


def bands(phi, R, P=None):
    """psi-bands [tau, tau + R) for all real tau, as (weight, node indices)."""
    key = lambda t: round(t, 9)
    if P is None:
        bp = sorted({key(p) for p in phi} | {key(p - R) for p in phi})
        pairs = list(zip(bp, bp[1:]))
        inside = lambda t, p: t <= p < t + R
    else:
        bp = sorted({key(p % P) for p in phi} | {key((p - R) % P) for p in phi})
        pairs = list(zip(bp, bp[1:] + [bp[0] + P]))
        inside = lambda t, p: (p - t) % P < R
    out = []
    for a, b in pairs:
        t = (a + b) / 2; xs = [i for i, p in enumerate(phi) if inside(t, p)]
        if xs:
            out.append(((b - a) / R, xs))
    return out


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
    done, ncyc, paths, psi = set(), 0, [], 0.0
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
        cn = lambda i: [b for b in nbr[path[i]] if core[b]]
        side = []                                  # adhesions of node i towards i - 1 and i + 1
        for i, x in enumerate(path):
            if cyc:
                prv, nx = path[i - 1], path[(i + 1) % L]
            else:
                prv = path[i - 1] if i > 0 else None
                nx = path[i + 1] if i + 1 < L else None
                prv = prv if prv is not None else next(b for b in cn(i) if b != nx)
                nx = nx if nx is not None else next(b for b in cn(i) if b != prv)
            side.append((bags[x] & bags[prv], bags[x] & bags[nx]))
        E = L if cyc else L - 1
        lam = [0 if A & B else min(bfs(adj, list(A), ell).get(z, ell) for z in B) for A, B in side]
        rho = run_rho([side[i][1] for i in range(E)], cyc)
        mu = [1 / rho[i] + (lam[i] + lam[(i + 1) % L]) / 2 for i in range(E)]
        phi = [0.0]
        for x in mu[:L - 1]:
            phi.append(phi[-1] + x)
        P = sum(mu) if cyc else None
        assert P is None or P > 2 * R, "core cycle too short"
        ncyc += cyc; psi += sum(mu); paths.append((mu, cyc))
        for wt, xs in bands(phi, R, P):
            out.append((wt, set().union(*(hv.get(path[i], set()) for i in xs)),
                        set().union(*(hn[path[i]] for i in xs))))
    return out, psi, ncyc, paths


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


def g_ecc(adj, ws):
    """Largest G-distance from the smallest vertex of a window to the rest of it."""
    best, seen = 0, set()
    for _, W, _ in ws:
        k = frozenset(W)
        if W and k not in seen:
            seen.add(k); d = bfs(adj, [min(W)], len(adj))
            best = max(best, max(d[w] for w in W))
    return best


def add(adj, u, v):
    while len(adj) <= max(u, v):
        adj.append(set())
    adj[u].add(v); adj[v].add(u)


def leg(adj, a, length):
    prev = a
    for _ in range(length):
        v = len(adj); add(adj, prev, v); prev = v


def fan_legs(k, length, mids):
    """Hub 0 over the path 1..k; legs at 1, k and at `mids` evenly spaced fan vertices."""
    adj, faces = [], []
    for i in range(1, k + 1):
        add(adj, 0, i)
    for i in range(1, k):
        add(adj, i, i + 1); faces.append([0, i, i + 1])
    for a in [1, k] + [1 + (k - 1) * (t + 1) // (mids + 1) for t in range(mids)]:
        leg(adj, a, length)
    return [sorted(s) for s in adj], faces


def staircase(phases, k, length, mid_legs):
    """Triangulated strip of alternating fans (each hub's run has length k); legs at both ends,
    and optionally at the middle vertex of every phase (many branch nodes)."""
    adj, faces = [], []
    t, b = 0, 1; add(adj, t, b); first = t
    for ph in range(phases):
        mid = None
        for s in range(k):
            c = len(adj); add(adj, t, c); add(adj, b, c); faces.append([t, b, c])
            if ph % 2 == 0:
                b = c
            else:
                t = c
            if s == k // 2:
                mid = c
        if mid_legs:
            leg(adj, mid, length)
    leg(adj, first, length); leg(adj, t, length)
    return [sorted(s) for s in adj], faces


def farey_legs(d, length):
    """Maximal outerplanar graph with weak dual a complete binary tree of depth d; legs at the
    four outer vertices of depth d farthest apart in the outer order."""
    adj, faces = [], []
    add(adj, 0, 1); todo = [(0, 1, 0)]; outer = []
    while todo:
        a, b, k = todo.pop()
        if k == d:
            outer.append(a); continue
        c = len(adj); add(adj, a, c); add(adj, b, c); faces.append([a, b, c])
        todo += [(c, b, k + 1), (a, c, k + 1)]
    for a in outer[:: max(1, len(outer) // 4)]:
        leg(adj, a, length)
    return [sorted(s) for s in adj], faces


def hub_ring(blocks, k):
    """One hole whose boundary is a cycle of `blocks` segments of k vertices; every segment is the rim of
    a fan with its own hub, so the core cycle around the hole runs through hub runs of length k."""
    L = blocks * k; adj, faces = [], [list(range(L))]
    for i in range(L):
        add(adj, i, (i + 1) % L)
    for b in range(blocks):
        h = len(adj)
        for i in range(b * k, b * k + k):
            add(adj, h, i)
        for i in range(b * k, b * k + k - 1):
            faces.append([h, i, i + 1])
    return [sorted(s) for s in adj], faces


def preferential(n, ell, hole, rng, p_pend=0.2, p_hole=0.002):
    """Random outerplanar graph; new faces go on an outer edge at a degree-biased vertex."""
    adj, faces, ends = [{1}, {0}], [], [0, 1]
    at = {0: {(0, 1)}, 1: {(0, 1)}}                      # outer edges at each vertex
    while len(adj) < n:
        v = rng.choice(ends)
        if rng.random() < p_pend:
            w = len(adj); adj.append({v}); adj[v].add(w); ends += [v, w]
            at.setdefault(v, set()).add((v, w)); at[w] = {(v, w)}
            continue
        a, b = rng.choice(sorted(at[v]))
        k = rng.randint(hole, 2 * hole) - 2 if rng.random() < p_hole else rng.randint(1, ell - 2)
        path = [a] + list(range(len(adj), len(adj) + k)) + [b]
        adj += [set() for _ in range(k)]
        at[a].discard((a, b)); at[b].discard((a, b))
        for x, y in zip(path, path[1:]):
            adj[x].add(y); adj[y].add(x); ends += [x, y]
            at.setdefault(x, set()).add((x, y)); at.setdefault(y, set()).add((x, y))
        faces.append(path)
    return [sorted(s) for s in adj], faces


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
    for k in (20, 320):
        yield f"fan k={k}", *fan_legs(k, 3 * R, 1)
    for k in (8, 128):
        yield f"stair k={k}", *staircase(max(6, 2 * R), k, 3 * R, False)
        yield f"stair+legs k={k}", *staircase(max(6, 2 * R), k, 3 * R, True)
    yield "farey d=9", *farey_legs(9, 3 * R)
    yield "hub ring k=64", *hub_ring(max(8, 2 * hole // 64), 64)
    yield "preferential", *preferential(2500, ell, hole, rng)


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    for R in (4, 8, 16):
        ell = R
        for name, adj, faces in families(R, ell, rng):
            bags, nbrs = decompose(adj, faces, ell)
            ws, psi, ncyc, paths = windows(adj, bags, nbrs, R, ell)
            gf, sx, B, _ = check(adj, bags, nbrs, ws)
            ecc = g_ecc(adj, ws)
            cut = np.mean([sum(anchor_cuts(mu, cyc, R, rng) for mu, cyc in paths) for _ in range(20)])
            assert cut <= 3 * psi / R + 1e-9, (cut, psi, R)
            n = len(adj); holes = sum(len(f) > ell for f in faces)
            print(f"R={R:2d} {name:16s} n={n:4d} maxdeg={max(map(len, adj)):3d} holes={holes} "
                  f"core cycles={ncyc} gamma_f={gf:7.1f} B*R/gf={B * R / gf:6.2f} psi/gf={psi / gf:5.2f} "
                  f"ecc/(R+ell)={ecc / (R + ell):4.2f} cut*R/psi={cut * R / psi if psi else 0:4.2f}",
                  flush=True)
