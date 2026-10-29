"""Theorem 6 in the covering graph: an independent implementation of the proof, with every step checked.

outer_frac.py works in G itself and only uses holes far longer than the windows. This script builds the
objects of the proof as they are defined there, so that windows may wrap around short holes.
- Faces: the inner faces from a planar embedding of G plus an apex. Faces with at most ell vertices are
  short, longer ones are holes. D: short faces, thin edges (on no short face) and vertex nodes (vertices
  in at least two pieces). A vertex node is joined to its thin edges and to one face of every ell-block
  at it (smallest index, or random with --random-choices). Ownership: one node of D_v for every v.
- Unfolding: T, the universal cover of D, is explored lazily as a rooted tree whose nodes are labelled
  by nodes of D. A vertex of G-hat is a pair (t, v), where t is the node of the copy of D_v closest to
  the root. Distances in G-hat are computed in this unfolding, so they are exact.
- Core, hairs, core paths, runs, rho, lambda, mu, psi and the three families of windows, as in the paper.
  A cyclic core path of D is an infinite core path of T, handled through one period.
- Deterministic version: every window solves its LP on N[W] in G-hat, and the solutions are averaged.
- Randomized version: long and branch cuts, exponential clocks shared by all lifts of an edge of D,
  anchors, clusters, and the lexicographically first minimum dominating set of every cluster.

Checked claims (a violation is reported with the claim it breaks):
- faces: Euler count, faces are induced isometric cycles, two faces share at most one edge, and (for
  small graphs) every induced cycle is a face and every cycle of length <= ell lies in one ell-block;
- D: every D_v is a tree, adhesions are a vertex or an edge, cycle rank of D = number h of holes;
- few holes: separators separate, sum |S(F)| <= 2h, the explicit packing has pairwise distance >= 3
  and at least (|F| - 4|S(F)| - 2)/3 vertices per hole, and h <= 3 gamma_f/(ell - 13) for ell >= 14;
- unfolding: (i) covering at every vertex, (ii) face bags are isometric in G-hat, (iii) two lifts of a
  vertex are more than ell apart;
- core and hairs: (b) hair radius < R + ell/2, (c) radius of core-free components < R + ell, (d)
  hairs are injective;
- runs: runs are intervals, rho from G-hat equals rho from D, (R1), both bounds of (R2), (R3) in G-hat;
- windows: total weight exactly 1 at every vertex; a path window lies within distance < 3R + ell + 4
  of every vertex of X_a (of a vertex of the bag of p_a if a = b); the other windows have radius
  < 2R + 2ell;
- output: x dominates, sum x = sum wt * opt+(W), opt+(W) <= y(W) + sum_{e in dQ} |X_e| (repair) for
  every window, excess <= B, c(e) = 0 off the core, c(e) <= 2 mu(e)/R on core paths, <= 2 at branches;
- counting: 6h + 4N1 core neighbours of branch nodes, 4h + 2N1 core paths, N1 <= 3 gamma_f/(R - 2),
  sum k_P <= 12 gamma_f + 28 #paths, sum lambda <= 3 gamma_f + 5 #{lambda > 0}, #{lambda > 0} <= k_P + 2
  per path, sum mu <= 75 gamma_f + 178 (4h + 2N1), and period + mu(e) > (ell - 4)/2 on infinite core
  paths; the packing sets behind N1, sum k_P and sum lambda are built and checked to be packings;
- randomized (ell = 6R + 5): lifts of one edge are more than 3R apart in psi, the exact cut
  probabilities under independent clocks are at most mu(B(p) ^ B(p'))/R and sum to at most
  2 sum mu / R, E[#cuts] <= 3 sum mu / R + 6h + 4N1; in samples, the clusters partition V(G), project
  injectively, the output dominates, and its size is at most gamma + 2 sum_cut |X_e|.
Reported: B R / gamma_f (B = weighted boundary, the repair bound), the number of windows that contain
two lifts of one vertex (wrapping), and E[#cuts] against the bound.

Run as python3 outer_cover.py [suite ...] [--workers N]. Suites: faces, det, wrap, degree, regime,
rand, sensitivity (default: all). The exit code is 1 if any check fails.
"""
import math
import random
import sys
import time
import traceback
from collections import Counter, defaultdict, deque
from multiprocessing import Pool

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import lil_matrix

EPS = 1e-7


# ----------------------------------------------------------------------------- graphs and LPs
def _apex(adj):
    n = len(adj)
    G = nx.Graph(); G.add_nodes_from(range(n + 1))
    G.add_edges_from((u, w) for u in range(n) for w in adj[u] if u < w)
    G.add_edges_from((u, n) for u in range(n))
    return G


def outerplanar(adj):
    return nx.check_planarity(_apex(adj))[0]


def inner_faces(adj):
    n = len(adj)
    ok, emb = nx.check_planarity(_apex(adj))
    assert ok, "not outerplanar"
    seen, faces = set(), []
    for u, w in emb.edges():
        if (u, w) not in seen:
            f = emb.traverse_face(u, w, mark_half_edges=seen)
            if n not in f:
                faces.append(list(f))
    return faces


def ncomp(adj):
    n = len(adj); seen = [False] * n; c = 0
    for s in range(n):
        if not seen[s]:
            c += 1; seen[s] = True; st = [s]
            while st:
                v = st.pop()
                for w in adj[v]:
                    if not seen[w]:
                        seen[w] = True; st.append(w)
    return c


def bfs(adj, src, cap=None):
    dist = {s: 0 for s in src}; q = deque(src)
    while q:
        v = q.popleft()
        if cap is not None and dist[v] >= cap:
            continue
        for w in adj[v]:
            if w not in dist:
                dist[w] = dist[v] + 1; q.append(w)
    return dist


def lp_cover(nbhd, dom, support):
    """min x(support), x >= 0, x(N[u]) >= 1 for u in dom; nbhd(u) lists N[u]."""
    sup = list(support); col = {v: i for i, v in enumerate(sup)}; dom = list(dom)
    if not dom:
        return {}, 0.0
    A = lil_matrix((len(dom), len(sup)))
    for r, u in enumerate(dom):
        for w in nbhd(u):
            if w in col:
                A[r, col[w]] = -1
    res = linprog(np.ones(len(sup)), A_ub=A.tocsr(), b_ub=-np.ones(len(dom)), bounds=(0, None),
                  method="highs")
    assert res.status == 0, res.message
    return dict(zip(sup, res.x)), float(res.fun)


def gamma_f(adj):
    n = len(adj)
    x, val = lp_cover(lambda u: [u] + list(adj[u]), range(n), range(n))
    return val, np.array([x[v] for v in range(n)])


def ilp_cover(nbhd, dom, support):
    sup = sorted(support); col = {v: i for i, v in enumerate(sup)}; dom = list(dom)
    if not dom:
        return set()
    A = lil_matrix((len(dom), len(sup)))
    for r, u in enumerate(dom):
        for w in nbhd(u):
            if w in col:
                A[r, col[w]] = 1
    res = milp(np.ones(len(sup)), constraints=LinearConstraint(A.tocsr(), lb=np.ones(len(dom))),
               integrality=np.ones(len(sup)), bounds=Bounds(0, 1))
    assert res.status == 0
    return {sup[i] for i in range(len(sup)) if res.x[i] > 0.5}


def gamma(adj):
    n = len(adj)
    return len(ilp_cover(lambda u: [u] + list(adj[u]), range(n), range(n)))


# ----------------------------------------------------------------------------- decomposition graph D
class Decomp:
    def __init__(self, adj, faces, ell, rng=None):
        self.adj, self.n, self.ell, self.faces = adj, len(adj), ell, faces
        n = self.n
        short = [list(f) for f in faces if len(f) <= ell]
        self.holes = [list(f) for f in faces if len(f) > ell]
        ef = defaultdict(list)
        for i, f in enumerate(short):
            for x, y in zip(f, f[1:] + f[:1]):
                ef[frozenset((x, y))].append(i)
        par = list(range(len(short)))

        def find(a):
            while par[a] != a:
                par[a] = par[par[a]]; a = par[a]
            return a
        for fs in ef.values():
            assert len(fs) <= 2
            if len(fs) == 2:
                par[find(fs[0])] = find(fs[1])
        edges = sorted({(min(u, w), max(u, w)) for u in range(n) for w in adj[u]})
        thin = [e for e in edges if frozenset(e) not in ef]
        self.kind, self.bag, self.cyc = [], [], []
        for f in short:
            self.kind.append('F'); self.bag.append(frozenset(f)); self.cyc.append(tuple(f))
        for e in thin:
            self.kind.append('E'); self.bag.append(frozenset(e)); self.cyc.append(tuple(e))
        self.nbr = [set() for _ in self.bag]

        def link(a, b):
            assert a != b
            self.nbr[a].add(b); self.nbr[b].add(a)
        for fs in ef.values():
            if len(fs) == 2:
                link(*fs)
        pieces = [dict() for _ in range(n)]
        for i, f in enumerate(short):
            for v in f:
                pieces[v].setdefault(('B', find(i)), []).append(i)
        for j, e in enumerate(thin):
            for v in e:
                pieces[v][('E', j)] = [len(short) + j]
        self.block_of = [find(i) for i in range(len(short))] + [None] * len(thin)
        for v in range(n):
            if len(pieces[v]) != 1:
                idx = len(self.bag)
                self.kind.append('V'); self.bag.append(frozenset([v])); self.cyc.append((v,))
                self.nbr.append(set())
                for key, lst in sorted(pieces[v].items()):
                    link(idx, min(lst) if rng is None else rng.choice(lst))
        self.M = len(self.bag)
        self.nbr = [sorted(s) for s in self.nbr]
        self.ebag = []                      # edges of G inside each bag
        for a in range(self.M):
            d = defaultdict(list); c = self.cyc[a]
            if self.kind[a] == 'F':
                for x, y in zip(c, c[1:] + c[:1]):
                    d[x].append(y); d[y].append(x)
            elif self.kind[a] == 'E':
                d[c[0]].append(c[1]); d[c[1]].append(c[0])
            self.ebag.append(d)
        self.Dv = [[] for _ in range(n)]
        for a in range(self.M):
            for v in self.bag[a]:
                self.Dv[v].append(a)
        self.own = [min(self.Dv[v]) if rng is None else rng.choice(self.Dv[v]) for v in range(n)]

    def adh(self, a, b):
        return self.bag[a] & self.bag[b]

    def edge_count(self):
        return sum(len(s) for s in self.nbr) // 2

    def ncomp(self):
        comp = [-1] * self.M; c = 0
        for s in range(self.M):
            if comp[s] < 0:
                comp[s] = c; st = [s]
                while st:
                    a = st.pop()
                    for b in self.nbr[a]:
                        if comp[b] < 0:
                            comp[b] = c; st.append(b)
                c += 1
        return c

    def bag_dist(self, a, X, Y):
        """distance between the vertex sets X and Y inside the bag of a."""
        if X & Y:
            return 0
        if self.kind[a] == 'E':
            return 1
        if self.kind[a] == 'V':
            return 0
        c = self.cyc[a]; L = len(c); pos = {v: i for i, v in enumerate(c)}
        return min(min(abs(pos[x] - pos[y]), L - abs(pos[x] - pos[y])) for x in X for y in Y)


# ----------------------------------------------------------------------------- lazy universal cover
class Unfold:
    """The universal cover T of D (of the side of a T-edge if forbid is given), rooted at a node with
    label root, explored lazily. The T-neighbours of a node are its parent and one child for every
    D-neighbour of its label other than the label of its parent."""

    def __init__(self, dec, root, forbid=None):
        self.dec = dec
        self.label = [root]; self.parent = [-1]; self.children = [dict()]
        self.forbid = forbid
        self._copy = {}

    def child(self, u, lab):
        c = self.children[u].get(lab)
        if c is None:
            assert lab in self.dec.nbr[self.label[u]] and lab != self.up_label(u)
            c = len(self.label)
            self.label.append(lab); self.parent.append(u); self.children.append({})
            self.children[u][lab] = c
        return c

    def up_label(self, u):
        return self.label[self.parent[u]] if self.parent[u] >= 0 else self.forbid

    def tnbr(self, s, lab):
        """the T-neighbour of s with label lab (None if it lies outside a side)."""
        if lab == self.up_label(s):
            return self.parent[s] if self.parent[s] >= 0 else None
        return self.child(s, lab)

    def bagof(self, u):
        return self.dec.bag[self.label[u]]

    def top(self, u, v):
        bag = self.dec.bag
        while self.parent[u] >= 0 and v in bag[self.label[self.parent[u]]]:
            u = self.parent[u]
        return u

    def hv(self, u, v):
        return (self.top(u, v), v)

    def copy(self, t, v):
        """the nodes of the copy of D_v whose top node is t."""
        key = (t, v)
        if key not in self._copy:
            bag = self.dec.bag; out = [t]; st = [t]
            while st:
                u = st.pop(); pl = self.up_label(u)
                for b in self.dec.nbr[self.label[u]]:
                    if b != pl and v in bag[b]:
                        c = self.child(u, b); out.append(c); st.append(c)
            self._copy[key] = out
        return self._copy[key]

    def owner(self, hv):
        t, v = hv
        for s in self.copy(t, v):
            if self.label[s] == self.dec.own[v]:
                return s
        return None

    def gnbrs(self, hv, check=False):
        t, v = hv
        res = {}
        for s in self.copy(t, v):
            for w in self.dec.ebag[self.label[s]].get(v, ()):
                tw = self.top(s, w)
                assert res.get(w, tw) == tw, ("covering violated: two neighbours over", v, w)
                res[w] = tw
        if check:
            assert set(res) == set(self.dec.adj[v]), ("neighbours missing", v)
        return [(tw, w) for w, tw in res.items()]

    def bfs(self, src, cap):
        dist = {s: 0 for s in src}; q = deque(src)
        while q:
            z = q.popleft()
            if dist[z] >= cap:
                continue
            for y in self.gnbrs(z):
                if y not in dist:
                    dist[y] = dist[z] + 1; q.append(y)
        return dist

    def subtree(self, s):
        """s and all nodes below it."""
        out = [s]; st = [s]
        while st:
            x = st.pop(); pl = self.up_label(x)
            for b in self.dec.nbr[self.label[x]]:
                if b != pl:
                    c = self.child(x, b); out.append(c); st.append(c)
        return out


# ----------------------------------------------------------------------------- core, hairs, core paths
class Structure:
    def __init__(self, dec, R):
        self.dec, self.R = dec, R
        M = dec.M
        self.height = {(a, b): self.side_height(a, b, R) for a in range(M) for b in dec.nbr[a]}
        self.high = {k: hh >= R for k, hh in self.height.items()}
        self.core = [sum(self.high[(a, b)] for b in dec.nbr[a]) >= 2 for a in range(M)]
        self.kdeg = [sum(self.core[b] for b in dec.nbr[a]) if self.core[a] else -1 for a in range(M)]
        self.branch = [self.core[a] and self.kdeg[a] != 2 for a in range(M)]
        self._hairs()
        self._paths()

    def side_height(self, a, b, cap):
        """min(h(a,b), cap): BFS in G-hat from the adhesion, inside the side at b."""
        U = Unfold(self.dec, b, forbid=a)
        dist = U.bfs([U.hv(0, x) for x in self.dec.adh(a, b)], cap)
        return max(dist.values())

    def _hairs(self):
        dec, core = self.dec, self.core
        comp = [-1] * dec.M; comps = []
        for s in range(dec.M):
            if not core[s] and comp[s] < 0:
                cid = len(comps); comps.append([s]); comp[s] = cid; st = [s]
                while st:
                    a = st.pop()
                    for b in dec.nbr[a]:
                        if not core[b] and comp[b] < 0:
                            comp[b] = cid; comps[cid].append(b); st.append(b)
        self.att = [a if core[a] else None for a in range(dec.M)]
        self.noncore_comps = []
        for nodes in comps:
            ns = set(nodes)
            e_in = sum(len([b for b in dec.nbr[a] if b in ns]) for a in nodes) // 2
            assert e_in == len(nodes) - 1, "a core-free component of D is not a tree"
            attach = [(a, b) for a in nodes for b in dec.nbr[a] if core[b]]
            assert len(attach) <= 1, "a core-free component is attached to the core by two edges"
            if attach:
                for a in nodes:
                    self.att[a] = attach[0][1]
            else:
                self.noncore_comps.append(nodes)
        self.hairD = defaultdict(list)
        for a in range(dec.M):
            if self.att[a] is not None:
                self.hairD[self.att[a]].append(a)

    def _paths(self):
        dec, core, kdeg = self.dec, self.core, self.kdeg
        done = set(); self.paths = []
        for a in range(dec.M):
            if not (core[a] and kdeg[a] == 2) or a in done:
                continue
            seq = [a]; done.add(a)
            for direction in (0, 1):
                prev, cur = (None, a) if direction == 0 else (seq[1] if len(seq) > 1 else None, a)
                while True:
                    nxt = [b for b in dec.nbr[cur] if core[b] and kdeg[b] == 2 and b != prev and b not in done]
                    if not nxt:
                        break
                    prev, cur = cur, nxt[0]; done.add(cur)
                    if direction == 0:
                        seq.append(cur)
                    else:
                        seq.insert(0, cur)
            L = len(seq)
            cyc = L >= 3 and seq[0] in dec.nbr[seq[-1]] and \
                set(b for b in dec.nbr[seq[0]] if core[b]) == {seq[1], seq[-1]}
            if cyc:
                self.paths.append(CorePath(self, seq, True, None, None))
                continue
            cn0 = [b for b in dec.nbr[seq[0]] if core[b] and (L == 1 or b != seq[1])]
            cn1 = [b for b in dec.nbr[seq[-1]] if core[b] and (L == 1 or b != seq[-2])]
            if L == 1:
                assert len(cn0) == 2
                b0, b1 = cn0
            else:
                assert len(cn0) == 1 and len(cn1) == 1
                b0, b1 = cn0[0], cn1[0]
            assert self.branch[b0] and self.branch[b1]
            self.paths.append(CorePath(self, seq, False, b0, b1))


class CorePath:
    """seq: labels of a core path of D. Finite: nodes 0..L-1 and edges i = (i, i+1). Cyclic (an
    infinite core path of T): node i has label seq[i % L], and one period has L edges."""

    def __init__(self, S, seq, cyc, b0, b1):
        dec = S.dec
        self.S, self.seq, self.cyc, self.b0, self.b1 = S, seq, cyc, b0, b1
        L = self.L = len(seq)
        self.E = L if cyc else L - 1
        X = self.X = [dec.adh(self.lab(i), self.lab(i + 1)) for i in range(self.E)]
        lam = []
        for i in range(L):
            if cyc:
                A, B = X[(i - 1) % L], X[i]
            else:
                A = X[i - 1] if i > 0 else dec.adh(b0, seq[0])
                B = X[i] if i < L - 1 else dec.adh(seq[-1], b1)
            lam.append(dec.bag_dist(seq[i], A, B))
        self.lam = lam
        seqX = [X[i % L] for i in range(5 * L)] if cyc else X      # five periods, use the middle one
        Mx = len(seqX)
        runs = set()
        for i in range(Mx):
            for v in seqX[i]:
                if i > 0 and v in seqX[i - 1]:
                    continue
                j = i
                while j + 1 < Mx and v in seqX[j + 1]:
                    j += 1
                runs.add((i, j))
        if cyc:
            assert all(e - s + 1 <= L or s == 0 or e == Mx - 1 for s, e in runs), "run longer than a period"
            runs = {(s, e) for s, e in runs if s > 0 and e < Mx - 1}
        maximal = sorted(I for I in runs if not any(J != I and J[0] <= I[0] and J[1] >= I[1] for J in runs))
        rho = [None] * Mx
        for s, e in maximal:
            for i in range(s, e + 1):
                if rho[i] is None or e - s + 1 < rho[i]:
                    rho[i] = e - s + 1
        if cyc:
            self.rho = [rho[2 * L + i] for i in range(L)]
            self.maxruns = [(s - 2 * L, e - 2 * L) for s, e in maximal if 2 * L <= s < 3 * L]
        else:
            assert all(r is not None for r in rho)
            self.rho, self.maxruns = rho, maximal
        self.k = len(self.maxruns)
        self.mu = [1 / self.rho[i] + (lam[i % L] + lam[(i + 1) % L]) / 2 for i in range(self.E)]
        self.period = sum(self.mu) if cyc else None

    def lab(self, i):
        return self.seq[i % self.L] if self.cyc else self.seq[i]

    def Xi(self, i):
        return self.X[i % self.L] if self.cyc else self.X[i]

    def mui(self, i):
        return self.mu[i % self.L] if self.cyc else self.mu[i]

    def rhoi(self, i):
        return self.rho[i % self.L] if self.cyc else self.rho[i]

    def psi(self, i):
        if not self.cyc:
            return sum(self.mu[:i])
        q, r = divmod(i, self.L)
        return q * self.period + sum(self.mu[:r])

    def windows(self, R):
        """(weight, a, b) for the windows with core nodes a..b, one per orbit."""
        key = lambda t: round(t, 9)
        out = []
        if not self.cyc:
            ps = [self.psi(i) for i in range(self.L)]
            bp = sorted({key(p) for p in ps} | {key(p - R) for p in ps})
            for t0, t1 in zip(bp, bp[1:]):
                t = (t0 + t1) / 2
                xs = [i for i, p in enumerate(ps) if t <= p <= t + R]
                if xs:
                    out.append(((t1 - t0) / R, xs[0], xs[-1]))
            return out
        P = self.period
        ps0 = [self.psi(i) for i in range(self.L)]
        bp = sorted({key(p % P) for p in ps0} | {key((p - R) % P) for p in ps0})
        nrep = int(math.ceil((R + P) / P)) + 2
        for t0, t1 in zip(bp, bp[1:] + [bp[0] + P]):
            t = (t0 + t1) / 2
            xs = [i for i in range(-nrep * self.L, nrep * self.L) if t <= self.psi(i) <= t + R]
            if xs:
                assert xs == list(range(xs[0], xs[-1] + 1))
                out.append(((t1 - t0) / R, xs[0], xs[-1]))
        return out


# ----------------------------------------------------------------------------- checks on G and D
class Report:
    def __init__(self, name):
        self.name = name; self.viol = []; self.info = {}

    def bad(self, claim, detail=None):
        self.viol.append((claim, detail))


def check_faces(adj, faces, ell, rep, all_cycles=False):
    n = len(adj); m = sum(map(len, adj)) // 2
    if len(faces) != m - n + ncomp(adj):
        rep.bad("Euler count of the inner faces", (len(faces), m - n + ncomp(adj)))
    for f in faces:
        k = len(f); S = set(f)
        if len(S) != k:
            rep.bad("face not a cycle", f)
        if any(adj[v] & S != {f[i - 1], f[(i + 1) % k]} for i, v in enumerate(f)):
            rep.bad("face not induced", f)
        pos = {v: i for i, v in enumerate(f)}
        for v in f[:6]:
            d = bfs(adj, [v])
            if any(d[w] != min(abs(pos[v] - pos[w]), k - abs(pos[v] - pos[w])) for w in f):
                rep.bad("face not isometric", f); break
    es = defaultdict(list)
    for i, f in enumerate(faces):
        for x, y in zip(f, f[1:] + f[:1]):
            es[frozenset((x, y))].append(i)
    share = Counter(tuple(sorted(fs)) for fs in es.values() if len(fs) == 2)
    if any(len(fs) > 2 for fs in es.values()):
        rep.bad("edge on three faces")
    for (i, j), c in share.items():
        if c > 1 or len(set(faces[i]) & set(faces[j])) != 2:
            rep.bad("two faces with a common edge share more", (i, j))
    if all_cycles:
        G = nx.Graph(); G.add_edges_from((u, w) for u in range(n) for w in adj[u] if u < w)
        fs = {frozenset(f) for f in faces}
        dec = Decomp(adj, faces, ell)
        blk = {}
        for a in range(dec.M):
            if dec.kind[a] == 'F':
                c = dec.cyc[a]
                for x, y in zip(c, c[1:] + c[:1]):
                    blk[frozenset((x, y))] = dec.block_of[a]
        for c in nx.simple_cycles(G, length_bound=max(ell, 3) + 2):
            S = set(c)
            if all(len(adj[v] & S) == 2 for v in c) and frozenset(c) not in fs:
                rep.bad("induced cycle that is not a face", c)
            if len(c) <= ell:
                bl = {blk.get(frozenset((x, y))) for x, y in zip(c, c[1:] + c[:1])}
                if len(bl) != 1 or None in bl:
                    rep.bad("short cycle not in one ell-block", c)


def check_D(dec, rep):
    for v in range(dec.n):
        S = set(dec.Dv[v])
        e = sum(1 for a in S for b in dec.nbr[a] if b in S) // 2
        seen = {dec.Dv[v][0]}; st = [dec.Dv[v][0]]
        while st:
            a = st.pop()
            for b in dec.nbr[a]:
                if b in S and b not in seen:
                    seen.add(b); st.append(b)
        if e != len(S) - 1 or len(seen) != len(S):
            rep.bad("D_v not a tree", v)
    for a in range(dec.M):
        for b in dec.nbr[a]:
            X = sorted(dec.adh(a, b))
            if not (len(X) == 1 or (len(X) == 2 and X[1] in dec.adj[X[0]])):
                rep.bad("adhesion not a vertex or an edge", (a, b))
    c = dec.ncomp()
    if c != ncomp(dec.adj):
        rep.bad("c(D) != c(G)")
    if dec.edge_count() - dec.M + c != len(dec.holes):
        rep.bad("cycle rank of D != h", (dec.edge_count() - dec.M + c, len(dec.holes)))
    rep.info["h"] = len(dec.holes)


def check_holes(dec, gf, rep):
    """The forest of faces, bridges and cut vertices; separators; the packing of 'Few holes'."""
    adj, n, faces = dec.adj, dec.n, dec.faces
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from((u, w) for u in range(n) for w in adj[u] if u < w)
    ef = defaultdict(list)
    for i, f in enumerate(faces):
        for x, y in zip(f, f[1:] + f[:1]):
            ef[frozenset((x, y))].append(i)
    T = nx.Graph(); T.add_nodes_from(('F', i) for i in range(len(faces)))
    T.add_edges_from((('F', fs[0]), ('F', fs[1])) for fs in ef.values() if len(fs) == 2)
    for e in G.edges():
        if frozenset(e) not in ef:
            T.add_node(('B', frozenset(e)))
    blocks = [set(b) for b in nx.biconnected_components(G)]
    for c in nx.articulation_points(G):
        for B in blocks:
            if c in B:
                if len(B) == 2:
                    T.add_edge(('C', c), ('B', frozenset(B)))
                else:
                    T.add_edge(('C', c), ('F', min(i for i, f in enumerate(faces) if c in f and set(f) <= B)))
    if not nx.is_forest(T):
        rep.bad("faces, bridges and cut vertices do not form a forest"); return
    hole_ids = [i for i, f in enumerate(faces) if len(f) > dec.ell]
    S = {i: set() for i in hole_ids}
    for i in hole_ids:
        for j in hole_ids:
            if i == j or not nx.has_path(T, ('F', i), ('F', j)):
                continue
            nb = nx.shortest_path(T, ('F', i), ('F', j))[1]
            s = frozenset(set(faces[i]) & set(faces[nb[1]])) if nb[0] == 'F' else frozenset([nb[1]])
            S[i].add(s)
            H = G.copy(); H.remove_nodes_from(s)
            if any(nx.has_path(H, a, b) for a in set(faces[i]) - s for b in set(faces[j]) - s):
                rep.bad("separator does not separate", (i, j))
    if sum(len(S[i]) for i in hole_ids) > 2 * len(hole_ids):
        rep.bad("sum |S(F)| <= 2h", (sum(len(S[i]) for i in hole_ids), len(hole_ids)))
    chosen = []
    for i in hole_ids:
        f = faces[i]; k = len(f)
        dist = {}
        for s in S[i]:
            for v, dv in bfs(adj, list(s), 2).items():
                dist[v] = min(dist.get(v, 9), dv)
        Wset = {j for j, v in enumerate(f) if dist.get(v, 9) >= 2}
        pick = []
        if not S[i]:
            pick = [f[j] for j in range(0, k - 2, 3)]
        else:
            start = next(j for j in range(k) if j not in Wset); arc = []
            for t in range(1, k + 1):
                j = (start + t) % k
                if j in Wset:
                    arc.append(j)
                else:
                    pick += [f[arc[q]] for q in range(0, len(arc), 3)]; arc = []
        if len(pick) < (k - 4 * len(S[i]) - 2) / 3 - EPS:
            rep.bad("few holes: count per hole", i)
        chosen += pick
    pack_check(adj, chosen, rep, "holes")
    h = len(hole_ids)
    if dec.ell >= 14 and h > 3 * gf / (dec.ell - 13) + EPS:
        rep.bad("h <= 3 gamma_f / (ell - 13)", (h, gf, dec.ell))


def pack_check(adj, chosen, rep, tag):
    if len(set(chosen)) != len(chosen):
        rep.bad(f"{tag} packing: repeated vertex")
    cs = set(chosen)
    for v in cs:
        if any(w != v and w in cs for w in bfs(adj, [v], 2)):
            rep.bad(f"{tag} packing: two vertices at distance <= 2", v); break
    rep.info[f"pack_{tag}"] = len(cs)


def check_cover(dec, rep):
    """(i) covering at every vertex within distance ell, (iii) lifts > ell apart, (ii) face bags isometric."""
    ell = dec.ell
    for v in range(dec.n):
        U = Unfold(dec, dec.own[v]); root = U.hv(0, v)
        dist = {root: 0}; q = deque([root])
        while q:
            z = q.popleft()
            if dist[z] >= ell:
                continue
            for y in U.gnbrs(z, check=True):
                if y not in dist:
                    dist[y] = dist[z] + 1; q.append(y)
        if any(z[1] == v and z != root for z in dist):
            rep.bad("(iii) two lifts within distance ell", v)
    for a in range(dec.M):
        if dec.kind[a] != 'F':
            continue
        U = Unfold(dec, a); c = dec.cyc[a]; k = len(c)
        for i0 in range(0, k, max(1, k // 3)):
            d = U.bfs([U.hv(0, c[i0])], k // 2 + 1)
            if any(d.get(U.hv(0, w)) != min(abs(i0 - j), k - abs(i0 - j)) for j, w in enumerate(c)):
                rep.bad("(ii) face bag not isometric in G-hat", a)


# ----------------------------------------------------------------------------- deterministic version
def build_window(S, kind, data):
    """(U, Q, core nodes of the window) in an unfolding rooted at its first node."""
    dec = S.dec
    if kind == 'path':
        P, a, b = data
        U = Unfold(dec, P.lab(a)); cores = [0]
        for i in range(a + 1, b + 1):
            cores.append(U.child(cores[-1], P.lab(i)))
    elif kind == 'branch':
        U = Unfold(dec, data); cores = [0]
    else:
        U = Unfold(dec, data[0])
        Q = set(U.subtree(0))
        assert len(Q) == len(data), "a core-free component unfolds to a different size"
        return U, Q, []
    Q = set(cores)
    for c in cores:
        for bl in dec.nbr[U.label[c]]:
            if not S.core[bl]:
                hair = U.subtree(U.child(c, bl))
                if any(S.core[U.label[x]] for x in hair):
                    raise AssertionError("core node inside a hair")
                Q.update(hair)
    return U, Q, cores


def window_orbits(S):
    out = [(wt, 'path', (P, a, b)) for P in S.paths for wt, a, b in P.windows(S.R)]
    out += [(1.0, 'branch', a) for a in range(S.dec.M) if S.branch[a]]
    out += [(1.0, 'noncore', comp) for comp in S.noncore_comps]
    return out


def far_from(U, src, targets, cap):
    """largest distance from src to targets if all are within cap, else infinity (BFS stops early)."""
    left = set(targets) - set(src); dist = {s: 0 for s in src}; q = deque(src); far = 0
    while q and left:
        z = q.popleft()
        if dist[z] >= cap:
            continue
        for y in U.gnbrs(z):
            if y not in dist:
                dist[y] = dist[z] + 1; q.append(y)
                if y in left:
                    left.discard(y); far = dist[y]
    return far if not left else math.inf


def deterministic(dec, S, gf, y, rep):
    adj, n, R, ell = dec.adj, dec.n, S.R, dec.ell
    x = np.zeros(n); cov = np.zeros(n); B = 0.0; total = 0.0
    cE = defaultdict(float); wraps = 0
    for wt, kind, data in window_orbits(S):
        U, Q, cores = build_window(S, kind, data)
        W = {U.hv(s, v) for s in Q for v in U.bagof(s) if dec.own[v] == U.label[s]}
        nb = {z: [z] + U.gnbrs(z, check=True) for z in W}
        NW = set(W).union(*nb.values()) if W else set()
        sol, val = lp_cover(lambda u: nb[u], W, NW)
        bw = 0
        for s in Q:
            for bl in dec.nbr[U.label[s]]:
                t = U.tnbr(s, bl)
                if t is not None and t not in Q:
                    bw += len(dec.adh(U.label[s], bl))
                    cE[tuple(sorted((U.label[s], bl)))] += wt
        if val > sum(y[v] for _, v in W) + bw + EPS:
            rep.bad("repair: opt+(W) <= y(W) + sum |X_e|", kind)
        for (_, v), xv in sol.items():
            x[v] += wt * xv
        for _, v in W:
            cov[v] += wt
        total += wt * val; B += wt * bw
        if len({v for _, v in W}) < len(W):
            wraps += 1
        if W and kind == 'path':
            P, a, b = data
            xs = P.Xi(a) if b > a else [next(iter(U.bagof(0)))]
            lim = 3 * R + ell + 4
            for xv in xs:
                if not far_from(U, [U.hv(0, xv)], W, math.ceil(lim)) < lim:
                    rep.bad("path window within 3R + ell + 4 of X_a", (a, b))
        elif W:
            lim = 2 * R + 2 * ell
            if not far_from(U, [min(W, key=lambda z: z[1])], W, math.ceil(lim)) < lim:
                rep.bad("window radius < 2R + 2ell", kind)
    if not np.allclose(cov, 1):
        rep.bad("windows do not have total weight 1", (cov.min(), cov.max()))
    if min(x[u] + sum(x[w] for w in adj[u]) for u in range(n)) < 1 - EPS:
        rep.bad("x does not dominate")
    if abs(total - x.sum()) > 1e-6:
        rep.bad("sum x != sum wt opt+(W)", (total, x.sum()))
    if x.sum() - gf > B + 1e-6:
        rep.bad("excess > B", (x.sum() - gf, B))
    mu_of = {tuple(sorted((P.lab(i), P.lab(i + 1)))): P.mu[i] for P in S.paths for i in range(P.E)}
    for e, c in cE.items():
        if not (S.core[e[0]] and S.core[e[1]]):
            rep.bad("c(e) > 0 off the core", e)
        elif e in mu_of and c > 2 * mu_of[e] / R + EPS:
            rep.bad("c(e) <= 2 mu(e) / R", e)
        elif e not in mu_of and c > 2 + EPS:
            rep.bad("c(e) <= 2 at a branch node", e)
    rep.info.update(n=n, maxdeg=max(map(len, adj)), gf=round(gf, 3), exc=round(x.sum() - gf, 4),
                    B=round(B, 3), BR_gf=round(B * R / gf, 2), wrap=wraps, paths=len(S.paths),
                    infinite=sum(P.cyc for P in S.paths))
    return x


def check_structure(S, gf, rep):
    dec, R, ell = S.dec, S.R, S.dec.ell
    adj, h = dec.adj, len(dec.holes)
    for c in range(dec.M):
        if not S.core[c]:
            continue
        if len(set(S.hairD[c])) != len(S.hairD[c]):
            rep.bad("(d) hair not injective", c)
        U = Unfold(dec, c)
        d = U.bfs([U.hv(0, v) for v in dec.bag[c]], int(R + ell / 2) + 2)
        for q in dec.nbr[c]:
            if S.core[q]:
                continue
            for s in U.subtree(U.child(0, q)):
                if any(not d.get(U.hv(s, v), math.inf) < R + ell / 2 for v in U.bagof(s)):
                    rep.bad("(b) hair radius < R + ell/2", c); break
    for comp in S.noncore_comps:
        Vs = set().union(*(dec.bag[a] for a in comp))
        if not min(max(bfs(adj, [v]).get(w, math.inf) for w in Vs) for v in Vs) < R + ell:
            rep.bad("(c) core-free component radius < R + ell")
    N1 = sum(1 for a in range(dec.M) if S.core[a] and S.kdeg[a] <= 1)
    nbr_branch = sum(S.kdeg[a] for a in range(dec.M) if S.branch[a])
    if nbr_branch > 6 * h + 4 * N1:
        rep.bad("branch nodes have <= 6h + 4N1 core neighbours", (nbr_branch, h, N1))
    npaths = len(S.paths)
    if npaths > 4 * h + 2 * N1:
        rep.bad("<= 4h + 2N1 core paths", (npaths, h, N1))
    if R > 2 and N1 > 3 * gf / (R - 2) + EPS:
        rep.bad("N1 <= 3 gamma_f / (R - 2)", (N1, gf))
    sk = sum(P.k for P in S.paths)
    if sk > 12 * gf + 28 * npaths + EPS:
        rep.bad("sum k_P <= 12 gamma_f + 28 #paths", (sk, gf, npaths))
    lam_sum = sum(sum(P.lam) for P in S.paths)
    lam_pos = sum(sum(1 for l in P.lam if l > 0) for P in S.paths)
    if lam_sum > 3 * gf + 5 * lam_pos + EPS:
        rep.bad("sum lambda <= 3 gamma_f + 5 #{lambda > 0}", (lam_sum, gf, lam_pos))
    for P in S.paths:
        if sum(1 for l in P.lam if l > 0) > P.k + 2:
            rep.bad("#{lambda > 0} <= k_P + 2 on a core path")
        if P.cyc and not min(P.period + m for m in P.mu) > (ell - 4) / 2 - EPS:
            rep.bad("period + mu(e) > (ell - 4)/2 on an infinite core path", (P.period, ell))
    smu = sum(sum(P.mu) for P in S.paths)
    if smu > sk + lam_sum + EPS:
        rep.bad("sum mu <= sum k_P + sum lambda", (smu, sk, lam_sum))
    if smu > 75 * gf + 178 * (4 * h + 2 * N1) + EPS:
        rep.bad("sum mu <= 75 gamma_f + 178 (4h + 2N1)", smu)
    rep.info.update(N1=N1, sum_k=sk, sum_mu=round(smu, 2))
    return N1


def unfold_path(S, P, a, b):
    U = Unfold(S.dec, P.lab(a)); pn = [0]
    for i in range(a + 1, b + 1):
        pn.append(U.child(pn[-1], P.lab(i)))
    return U, pn


def check_runs(S, rep):
    """runs, rho, (R1), (R2) and (R3), with adhesions and distances in G-hat."""
    dec = S.dec
    for P in S.paths:
        a, b = (-2 * P.L, 3 * P.L) if P.cyc else (0, P.L - 1)
        U, pn = unfold_path(S, P, a, b)
        node = lambda i: pn[i - a]
        Xh = {i: {U.hv(node(i + 1), v) for v in P.Xi(i)} for i in range(a, b)}
        occ = defaultdict(list)
        for i in range(a, b):
            for z in Xh[i]:
                occ[z].append(i)
        runs = set()
        for z, lst in occ.items():
            if lst != list(range(lst[0], lst[-1] + 1)):
                rep.bad("run not an interval")
            runs.add((lst[0], lst[-1]))
        trunc = lambda I: I[0] == a or I[1] == b - 1
        maxr = sorted(I for I in runs if not any(J != I and J[0] <= I[0] and J[1] >= I[1] for J in runs))
        for i in range(a, b):
            through = [I for I in maxr if I[0] <= i <= I[1]]
            if through and not any(trunc(I) for I in through):
                if min(I[1] - I[0] + 1 for I in through) != P.rhoi(i):
                    rep.bad("rho from G-hat != rho from D", i)
        full = [I for I in maxr if not trunc(I)]
        for c in range(len(full)):
            for c2 in range(c + 3, len(full)):
                if any(Xh[i] & Xh[j] for i in range(full[c][0], full[c][1] + 1)
                       for j in range(full[c2][0], full[c2][1] + 1)):
                    rep.bad("(R1)", (c, c2))
        for t in pn:                         # hairs, so that shortest paths may use them
            for bl in dec.nbr[U.label[t]]:
                if not S.core[bl]:
                    U.subtree(U.child(t, bl))
        for i in range(a, b):
            d = U.bfs(list(Xh[i]), int(2 * sum(P.mui(j) for j in range(i, b)) + 6))
            acc = 0.0
            for j in range(i, b):
                acc += P.mui(j)
                if min(d.get(z, math.inf) for z in Xh[j]) > 2 * acc + 3 + EPS:
                    rep.bad("(R3)", (i, j))
        for i in range(a, b):
            for j in range(i, min(b, i + 60)):
                k = sum(1 for I in maxr if I[1] >= i and I[0] <= j)
                s = sum(1 / P.rhoi(t) for t in range(i, j + 1))
                if s < (k - 4) / 2 - EPS or s > k + EPS:
                    rep.bad("(R2)", (i, j))


def hair_nodes(U, S, t):
    out = {t}
    for bl in S.dec.nbr[U.label[t]]:
        if not S.core[bl]:
            out.update(U.subtree(U.child(t, bl)))
    return out


def packing_N1(S, rep):
    dec, R = S.dec, S.R
    chosen = []
    for c in range(dec.M):
        if not (S.core[c] and S.kdeg[c] <= 1):
            continue
        qs = [q for q in dec.nbr[c] if not S.core[q] and S.high[(c, q)]]
        if not qs:
            rep.bad("N1: no high side outside the core", c); continue
        V = Unfold(dec, qs[0], forbid=c)
        src = [V.hv(0, x) for x in dec.adh(c, qs[0])]
        dist = {s: 0 for s in src}; par = {s: None for s in src}; q = deque(src); far = None
        while q:
            z = q.popleft()
            if dist[z] == R:
                far = z; break
            for yv in V.gnbrs(z):
                if yv not in dist:
                    dist[yv] = dist[z] + 1; par[yv] = z; q.append(yv)
        if far is None:
            rep.bad("high side without a vertex at distance R", c); continue
        path = []
        while far is not None:
            path.append(far); far = par[far]
        sel = path[::-1][2::3]
        if len(sel) < (R - 2) / 3 - EPS:
            rep.bad("N1 count", c)
        if any(V.owner(yv) is None for z in sel for yv in [z] + V.gnbrs(z)):
            rep.bad("N1: closed neighbourhood not owned by the hair", c)
        chosen += [z[1] for z in sel]
    pack_check(dec.adj, chosen, rep, "N1")


def packing_runs(S, rep):
    """every twelfth maximal run carries x_c with N[x_c] owned by the hairs of p_i, t_{c-6} < i <= t_{c+6}."""
    dec = S.dec
    chosen = []
    for P in S.paths:
        if P.cyc:
            k = len(P.maxruns)
            runs = sorted((s + r * P.L, e + r * P.L) for r in range(-1, 4) for s, e in P.maxruns)
            first = next(t for t, I in enumerate(runs) if I[0] >= 0)
            I = runs[first:first + k + 12]
        else:
            I = P.maxruns; k = len(I)
        cs = [c for c in range(6, k) if c % 12 == 6 and c + 6 <= k - 4]
        if len(cs) < (k - 28) / 12 - EPS:
            rep.bad("runs packing count", (k, len(cs)))
        if not cs:
            continue
        lo = min(I[c - 6][0] for c in cs) - 2; hi = max(I[c + 6][1] for c in cs) + 2
        if not P.cyc:
            lo, hi = max(lo, 0), min(hi, P.L - 1)
        U, pn = unfold_path(S, P, lo, hi)
        node = lambda i: pn[i - lo]
        hairs = {i: hair_nodes(U, S, node(i)) for i in range(lo, hi + 1)}
        for c in cs:
            allowed = set().union(*(hairs[i] for i in range(I[c - 6][1] + 1, I[c + 6][0] + 1)))
            cand = sorted({U.hv(node(i + 1), v) for i in range(I[c][0], I[c][1] + 1) for v in P.Xi(i)},
                          key=lambda z: z[1])
            pick = None
            for z in cand:
                if all(U.owner(yv) in allowed for yv in [z] + U.gnbrs(z)):
                    pick = pick or z
                else:
                    rep.bad("runs packing: N[x_c] leaves its region", c)
            if pick is not None:
                chosen.append(pick[1])
    pack_check(dec.adj, chosen, rep, "runs")


def packing_lambda(S, rep):
    dec = S.dec
    chosen = []
    for P in S.paths:
        for i in range(P.L):
            lam = P.lam[i]
            if lam < 6:
                continue
            a = P.seq[i]
            if dec.kind[a] != 'F':
                rep.bad("lambda >= 6 at a node that is not a face", a); continue
            if P.cyc:
                A, B = P.X[(i - 1) % P.L], P.X[i]
            else:
                A = P.X[i - 1] if i > 0 else dec.adh(P.b0, P.seq[0])
                B = P.X[i] if i < P.L - 1 else dec.adh(P.seq[-1], P.b1)
            c = dec.cyc[a]; k = len(c); pos = {v: j for j, v in enumerate(c)}
            steps, x0, sgn = min((((pos[w] - pos[u]) * sg) % k, u, sg) for u in A for w in B for sg in (1, -1))
            arc = [c[(pos[x0] + sgn * t) % k] for t in range(steps + 1)]
            dset = lambda Y, v: min(min(abs(pos[v] - pos[w]), k - abs(pos[v] - pos[w])) for w in Y)
            sel = [v for v in arc if dset(A, v) >= 3 and dset(B, v) >= 3][::3]
            if len(sel) < (lam - 5) / 3 - EPS:
                rep.bad("lambda count", a)
            U = Unfold(dec, a)
            hs = hair_nodes(U, S, 0)
            if any(U.owner(yv) not in hs for v in sel for yv in [U.hv(0, v)] + U.gnbrs(U.hv(0, v))):
                rep.bad("lambda packing: N[u] not owned by hair(p)", a)
            chosen += sel
    pack_check(dec.adj, chosen, rep, "lambda")


def run_det(name, adj, ell, R, rng=None, cover=True, runs=True, all_cycles=False):
    assert outerplanar(adj), name
    faces = inner_faces(adj)
    rep = Report(f"{name} ell={ell} R={R}")
    check_faces(adj, faces, ell, rep, all_cycles)
    dec = Decomp(adj, faces, ell, rng)
    check_D(dec, rep)
    gf, y = gamma_f(adj)
    check_holes(dec, gf, rep)
    if cover:
        check_cover(dec, rep)
    S = Structure(dec, R)
    deterministic(dec, S, gf, y, rep)
    check_structure(S, gf, rep)
    if runs:
        check_runs(S, rep)
    packing_N1(S, rep); packing_runs(S, rep); packing_lambda(S, rep)
    return rep


# ----------------------------------------------------------------------------- randomized version
def segments(P, R):
    """segments of P as lists of edge indices, and the long edges; None for an infinite segment."""
    long_ = [i for i in range(P.E) if P.mu[i] > R]
    if not P.cyc:
        out, cur = [], []
        for i in range(P.E):
            if P.mu[i] > R:
                if cur:
                    out.append(cur)
                cur = []
            else:
                cur.append(i)
        return out + ([cur] if cur else []), long_
    if not long_:
        return None, long_
    out = [list(range(s + 1, t)) for s, t in zip(long_, long_[1:] + [long_[0] + P.L])]
    return [s for s in out if s], long_


def ball(P, R, i, segset):
    """B(p_i): edges of the segment (segset, or all of Z) with both ends within psi-distance R of p_i."""
    pi = P.psi(i); out = []
    j = i
    while (segset is None or j in segset) and P.psi(j + 1) - pi <= R + 1e-12:
        out.append(j); j += 1
    j = i - 1
    while (segset is None or j in segset) and pi - P.psi(j) <= R + 1e-12:
        out.append(j); j -= 1
    return out


def run_rand(name, adj, ell, R, samples=30, seed=0):
    rep = Report(f"{name} ell={ell} R={R}")
    assert outerplanar(adj)
    dec = Decomp(adj, inner_faces(adj), ell)
    S = Structure(dec, R)
    h = len(dec.holes)
    N1 = sum(1 for a in range(dec.M) if S.core[a] and S.kdeg[a] <= 1)
    brE = {tuple(sorted((a, b))) for a in range(dec.M) if S.branch[a] for b in dec.nbr[a] if S.core[b]}
    smu = sum(sum(P.mu) for P in S.paths)
    e_anchor = 0.0; nlong = 0
    for P in S.paths:
        if P.cyc and not min(P.period + m for m in P.mu) > 3 * R:
            rep.bad("two lifts of an edge of D within psi-distance 3R", (P.period, R))
        segs, long_ = segments(P, R)
        nlong += len(long_)
        tot_sym = 0.0; tot_mu = 0.0
        for seg in ([None] if segs is None else segs):
            segset = None if seg is None else set(seg)
            for e in (range(P.L) if seg is None else seg):
                tot_mu += P.mui(e)
                Bp, Bq = set(ball(P, R, e, segset)), set(ball(P, R, e + 1, segset))
                if e not in Bp or e not in Bq:
                    rep.bad("a segment edge is not in B(p)", e)
                Un = Bp | Bq
                if P.cyc and len({f % P.L for f in Un}) != len(Un):
                    rep.bad("B(p) u B(p') contains two lifts of one edge of D", e)
                sym = Bp ^ Bq
                mu_sym = sum(P.mui(f) for f in sym); mu_U = sum(P.mui(f) for f in Un)
                if sym and not mu_U > R:
                    rep.bad("mu(B(p) u B(p')) > R when B(p) != B(p')", e)
                prob = mu_sym / mu_U if mu_U > 0 else 0.0
                if prob > mu_sym / R + 1e-12:
                    rep.bad("cut probability <= mu(B(p) ^ B(p'))/R", e)
                e_anchor += prob; tot_sym += mu_sym
        if tot_sym > 2 * tot_mu + EPS:
            rep.bad("sum mu(B(p) ^ B(p')) <= 2 sum mu", (tot_sym, tot_mu))
    e_cuts = e_anchor + nlong + len(brE)
    if e_anchor > 2 * smu / R + EPS:
        rep.bad("E[anchor cuts] <= 2 sum mu / R", (e_anchor, smu))
    if e_cuts > 3 * smu / R + 6 * h + 4 * N1 + EPS:
        rep.bad("E[cuts] <= 3 sum mu / R + 6h + 4N1")
    g = gamma(adj)
    rng = random.Random(seed)
    owned = defaultdict(list)
    for v in range(dec.n):
        owned[dec.own[v]].append(v)
    hair_vertices = lambda lab: [v for a in S.hairD[lab] for v in owned[a]]
    sizes = []
    for _ in range(samples):
        clock = {}
        for P in S.paths:
            for i in range(P.E):
                clock[tuple(sorted((P.lab(i), P.lab(i + 1))))] = rng.expovariate(P.mu[i])
        clusters = []; cutD = list(brE)
        for P in S.paths:
            segs, _ = segments(P, R)
            ck = lambda f: clock[tuple(sorted((P.lab(f), P.lab(f + 1))))]
            lo, hi = (-2 * P.L, 3 * P.L) if P.cyc else (0, P.L - 1)
            segof = {}
            for sid, seg in enumerate(segs or []):
                for f in seg:
                    for r in (range(-4, 5) if P.cyc else [0]):
                        segof[f + r * P.L] = (sid, r)
            anchor = {}
            for i in range(lo, hi + 1):
                if P.cyc and segs is None:
                    anchor[i] = min(ball(P, R, i, None), key=ck)
                    continue
                sg = segof.get(i, segof.get(i - 1))
                if sg is None:
                    anchor[i] = ('alone', i); continue
                anchor[i] = min(ball(P, R, i, {f for f, s in segof.items() if s == sg}), key=ck)
            cut = [i for i in range(lo, hi) if P.mui(i) > R or anchor[i] != anchor[i + 1]]
            cutD += [tuple(sorted((P.lab(i), P.lab(i + 1)))) for i in cut if not P.cyc or 0 <= i < P.L]
            if P.cyc:
                if not cut:
                    rep.bad("infinite cluster"); continue
                for c1, c2 in zip(cut, cut[1:]):
                    if 0 <= c1 + 1 < P.L:
                        labs = [P.lab(i) for i in range(c1 + 1, c2 + 1)]
                        if len(set(labs)) != len(labs):
                            rep.bad("a cluster does not project injectively")
                        clusters.append([v for l in labs for v in hair_vertices(l)])
            else:
                bnd = [-1] + cut + [P.L - 1]
                for c1, c2 in zip(bnd, bnd[1:]):
                    clusters.append([v for i in range(c1 + 1, c2 + 1) for v in hair_vertices(P.lab(i))])
        clusters += [hair_vertices(a) for a in range(dec.M) if S.branch[a]]
        clusters += [[v for a in comp for v in owned[a]] for comp in S.noncore_comps]
        cnt = Counter(v for C in clusters for v in C)
        if any(cnt[v] != 1 for v in range(dec.n)):
            rep.bad("the clusters do not partition V(G)"); break
        out = set()
        for C in clusters:
            if C:
                NC = set(C).union(*(adj[v] for v in C))
                out |= ilp_cover(lambda u: [u] + list(adj[u]), C, NC)
        if not all(u in out or adj[u] & out for u in range(dec.n)):
            rep.bad("the output does not dominate")
        if len(out) > g + sum(2 * len(dec.adh(a, b)) for a, b in cutD):
            rep.bad("size <= gamma + 2 sum over cut edges of |X_e|")
        sizes.append((len(out), len(cutD)))
    bound = 3 * smu / R + 6 * h + 4 * N1
    rep.info.update(n=dec.n, h=h, N1=N1, gamma=g, sum_mu=round(smu, 2), E_cuts=round(e_cuts, 2),
                    bound=round(bound, 2), cut_ratio=round(e_cuts / bound, 3) if bound else None,
                    mean_size=round(float(np.mean([s for s, _ in sizes])), 2) if sizes else None)
    return rep


# ----------------------------------------------------------------------------- families
class Builder:
    def __init__(self):
        self.adj = []

    def v(self):
        self.adj.append(set()); return len(self.adj) - 1

    def e(self, a, b):
        self.adj[a].add(b); self.adj[b].add(a)

    def path_between(self, a, b, k):
        """a face of length k on the edge ab."""
        prev = a; new = []
        for _ in range(k - 2):
            x = self.v(); self.e(prev, x); prev = x; new.append(x)
        self.e(prev, b)
        return [a] + new + [b]

    def cycle_at(self, a, k):
        prev = a; new = []
        for _ in range(k - 1):
            x = self.v(); self.e(prev, x); prev = x; new.append(x)
        self.e(prev, a)
        return [a] + new

    def leg(self, a, k):
        for _ in range(k):
            x = self.v(); self.e(a, x); a = x
        return a

    def fan(self, u, h, k):
        """k - 1 triangles on the edge uh, all at the hub h."""
        prev = u
        for _ in range(k - 1):
            x = self.v(); self.e(prev, x); self.e(h, x); prev = x
        return prev


def cycle(L):
    b = Builder(); b.v(); b.cycle_at(0, L)
    return b.adj


def ring(L):
    b = Builder()
    for i in range(L):
        b.v()
    for i in range(L):
        b.e(i, (i + 1) % L)
    return b


def fan_ring(L, blocks, k, legs=0):
    """a hole of length L with fans of k - 1 triangles on evenly spaced edges."""
    b = ring(L)
    for t in range(blocks):
        u = t * L // blocks
        end = b.fan(u, (u + 1) % L, k)
        if legs:
            b.leg(end, legs)
    return b.adj


def stacked_fan_hole(L, k):
    """a hole of length L with a fan on every edge, hubs alternating."""
    b = ring(L)
    for i in range(L):
        u, h = (i, (i + 1) % L) if i % 2 == 0 else ((i + 1) % L, i)
        b.fan(u, h, k)
    return b.adj


def theta_chain(L, k):
    """k faces of length L in a row, consecutive ones sharing an edge."""
    b = Builder(); a0, a1 = b.v(), b.v(); b.e(a0, a1); edge = (a0, a1)
    for _ in range(k):
        f = b.path_between(edge[0], edge[1], L)
        edge = (f[len(f) // 2 - 1], f[len(f) // 2])
    return b.adj


def flower(L, k, legs=0):
    """k cycles of length L through one vertex."""
    b = Builder(); b.v()
    for _ in range(k):
        c = b.cycle_at(0, L)
        if legs:
            b.leg(c[len(c) // 2], legs)
    return b.adj


def big_flower(k, L, tri, legs):
    """k blocks at one vertex: every third a cycle of length L, the others of length tri."""
    b = Builder(); b.v()
    for j in range(k):
        c = b.cycle_at(0, L if j % 3 == 0 else tri)
        if legs and j % 4 == 0:
            b.leg(c[len(c) // 2], legs)
    return b.adj


def hole_tree(L, depth, branching):
    """faces of length L glued along edges in a tree pattern."""
    b = Builder(); a0, a1 = b.v(), b.v(); b.e(a0, a1); frontier = [(a0, a1)]
    for _ in range(depth):
        nf = []
        for x, y in frontier:
            f = b.path_between(x, y, L)
            edges = list(zip(f[1:-1], f[2:-1]))
            nf += edges[::max(1, len(edges) // branching)][:branching]
        frontier = nf
    return b.adj


def ladder_legs(m, legs):
    b = Builder(); t, s = b.v(), b.v(); b.e(t, s); first = t
    for i in range(m):
        c = b.v(); b.e(t, c); b.e(s, c)
        if i % 2 == 0:
            t = c
        else:
            s = c
    b.leg(first, legs); b.leg(t, legs)
    return b.adj


def staircase(phases, k, legs):
    """triangulated strip whose hub switches sides every k triangles (long runs of high degree)."""
    b = Builder(); t, s = b.v(), b.v(); b.e(t, s); first = t
    for ph in range(phases):
        for _ in range(k):
            c = b.v(); b.e(t, c); b.e(s, c)
            if ph % 2 == 0:
                s = c
            else:
                t = c
    b.leg(first, legs); b.leg(t, legs)
    return b.adj


def polygon_chain(L, k, legs, offset=None):
    """k faces of length L in a row with legs at both ends."""
    b = Builder(); a0, a1 = b.v(), b.v(); b.e(a0, a1); b.leg(a0, legs); edge = (a0, a1)
    for j in range(k):
        f = b.path_between(edge[0], edge[1], L)
        mid = len(f) // 2 if offset is None else (offset + j) % (len(f) - 3) + 1
        edge = (f[mid], f[mid + 1])
    b.leg(edge[0], legs)
    return b.adj


def ladder_with_holes(m, L, every):
    b = Builder(); t, s = b.v(), b.v(); b.e(t, s); outer = []
    for i in range(m):
        c = b.v(); b.e(t, c); b.e(s, c)
        if i % 2 == 0:
            outer.append((t, c)); t = c
        else:
            outer.append((s, c)); s = c
    for j, (x, y) in enumerate(outer):
        if j % every == 0:
            b.path_between(x, y, L)
    return b.adj


def random_op(n, rng, short_max, hole_lens, p_hole=0.1, p_pend=0.1, p_cyc=0.05, pref=False):
    """random outerplanar graph: faces glued on outer edges (preferentially at high degree if pref),
    pendant edges and new blocks."""
    b = Builder(); a0, a1 = b.v(), b.v(); b.e(a0, a1); outer = [(a0, a1)]
    while len(b.adj) < n:
        r = rng.random()
        deg = [len(s) for s in b.adj] if pref else None
        if r < p_pend:
            v = rng.choices(range(len(b.adj)), weights=[d * d + 1 for d in deg])[0] if pref \
                else rng.randrange(len(b.adj))
            x = b.v(); b.e(v, x); outer.append((v, x))
            continue
        k = rng.choice(hole_lens) if rng.random() < p_hole else rng.randint(3, short_max)
        if r < p_pend + p_cyc:
            c = b.cycle_at(rng.randrange(len(b.adj)), k)
            outer += list(zip(c, c[1:] + c[:1]))
            continue
        i = rng.choices(range(len(outer)), weights=[deg[x] ** 2 + deg[y] ** 2 for x, y in outer])[0] if pref \
            else rng.randrange(len(outer))
        x, y = outer[i]
        f = b.path_between(x, y, k)
        outer[i] = outer[-1]; outer.pop()
        outer += list(zip(f, f[1:]))
    return b.adj


# ----------------------------------------------------------------------------- suites
def suite(name):
    """list of (label, kind, builder, args, ell, R, options)."""
    T = []
    if name == "faces":          # exhaustive cycle enumeration on small graphs, all checks
        for s in range(60):
            rng = random.Random(s)
            ell = rng.choice([3, 4, 5, 6])
            T.append((f"small random {s}", "det", "random_op",
                      (rng.randint(8, 22), s, rng.randint(3, 6), [rng.randint(4, 9)], 0.3, s % 2 == 0),
                      ell, rng.choice([2, 3, 4]), dict(all_cycles=True)))
    if name == "det":            # long core paths, long short faces, holes of length ell + 1, random choices
        for R in (2, 4):
            T += [("long cycle", "det", "cycle", (120,), 5, R, {}),
                  ("ladder + legs", "det", "ladder_legs", (150, R + 3), 4, R, {}),
                  ("staircase k=5", "det", "staircase", (20, 5, R + 3), 4, R, {}),
                  ("staircase k=2", "det", "staircase", (60, 2, R + 3), 4, R, {}),
                  ("stacked fans L=40", "det", "stacked_fan_hole", (40, 3), 5, R, {}),
                  ("polygon chain L=14", "det", "polygon_chain", (14, 12, R + 3), 14, R, {}),
                  ("polygon chain L=16 skew", "det", "polygon_chain", (16, 10, R + 3, 2), 16, R, {})]
        for ell in (14, 17):
            for R in (3, 5):
                T += [("theta, holes ell+1", "det", "theta_chain", (ell + 1, 6), ell, R, {}),
                      ("hole tree, holes ell+1", "det", "hole_tree", (ell + 1, 2, 4), ell, R, {}),
                      ("random, holes ell+1", "det", "random_op", (120, ell + R, ell, [ell + 1, ell + 2], 0.3, False),
                       ell, R, {})]
        for s in range(4):
            T += [(f"random choices {s}", "det", "random_op", (70, 77 + s, 5, [6, 7, 9], 0.2, True), 5, 3, dict(rng=s)),
                  (f"fan ring choices {s}", "det", "fan_ring", (7, 3, 9, 5), 6, 3, dict(rng=s))]
    if name == "wrap":           # holes much shorter than the windows: windows wrap around them
        for R in (6, 10, 16):
            T += [("wrap fan ring", "det", "fan_ring", (4, 2, 6), 3, R, {}),
                  ("wrap stacked fans", "det", "stacked_fan_hole", (5, 3), 4, R, {}),
                  ("wrap theta", "det", "theta_chain", (5, 3), 4, R, {}),
                  ("wrap ladder + holes", "det", "ladder_with_holes", (12, 5, 3), 4, R, {}),
                  ("wrap cycle", "det", "cycle", (5,), 4, R, {})]
    if name == "degree":         # high degree: B R / gamma_f must not grow with the degree
        for k in (10, 40, 120, 200):
            T += [(f"fan ring k={k}", "det", "fan_ring", (5, 2, k), 4, 3, dict(cover=k < 100)),
                  (f"fan ring + legs k={k}", "det", "fan_ring", (6, 3, k, 5), 5, 3, dict(cover=k < 100))]
        T.append(("big flower k=10", "det", "big_flower", (10, 6, 3, 5), 5, 3, {}))
        for k in (10, 30, 60):
            T.append((f"stacked fans k={k}", "det", "stacked_fan_hole", (5, k), 4, 3, {}))
    if name == "regime":         # the theorem's ell = R + 13, holes of length ell + 1
        for R in (3, 5, 8):
            ell = R + 13; L = ell + 1
            T += [("theta", "det", "theta_chain", (L, 6), ell, R, dict(cover=False)),
                  ("hole tree", "det", "hole_tree", (L, 2, 5), ell, R, dict(cover=False)),
                  ("flower + legs", "det", "flower", (L, 5, R + 2), ell, R, dict(cover=False)),
                  ("cycle", "det", "cycle", (L,), ell, R, {}),
                  ("random", "det", "random_op", (150, L, ell, [L], 0.4, False), ell, R, dict(cover=False))]
    if name == "rand":           # the randomized version with ell = 6R + 5
        for R in (1, 2, 3):
            ell = 6 * R + 5; L = ell + 1
            T += [("cycle", "rand", "cycle", (L,), ell, R, {}),
                  ("cycle + 3", "rand", "cycle", (L + 3,), ell, R, {}),
                  ("fan ring", "rand", "fan_ring", (L, 3, 6), ell, R, {}),
                  ("fan ring + legs", "rand", "fan_ring", (L, 2, 5, 2 * R + 3), ell, R, {}),
                  ("stacked fans", "rand", "stacked_fan_hole", (L, 3), ell, R, {}),
                  ("theta", "rand", "theta_chain", (L, 3), ell, R, {}),
                  ("flower + legs", "rand", "flower", (L, 3, 2 * R + 2), ell, R, {}),
                  ("hole tree", "rand", "hole_tree", (L, 2, 2), ell, R, {}),
                  ("random", "rand", "random_op", (80, 11 + R, ell, [L, L + 2], 0.2, False), ell, R, {}),
                  ("random preferential", "rand", "random_op", (80, 17 + R, min(ell, 8), [L], 0.15, True), ell, R, {})]
    if name == "sensitivity":    # outside the theorem's range the checks must fire
        T.append(("cycle, ell=5, R=5", "rand-expect", "cycle", (6,), 5, 5, {}))
        T.append(("cycle of length 15, ell=14", "lifts-expect", "cycle", (15,), 14, 1, {}))
    return T


def build(builder, args):
    if builder == "random_op":
        n, seed, short_max, holes, p_hole, pref = args
        return random_op(n, random.Random(seed), short_max, holes, p_hole=p_hole, pref=pref)
    return globals()[builder](*args)


def job(task):
    label, kind, builder, args, ell, R, opt = task
    t0 = time.time()
    try:
        adj = [set(s) for s in build(builder, args)]
        if kind == "det":
            rng = random.Random(opt["rng"]) if "rng" in opt else None
            rep = run_det(label, adj, ell, R, rng=rng, cover=opt.get("cover", True),
                          all_cycles=opt.get("all_cycles", False))
        elif kind == "rand":
            rep = run_rand(label, adj, ell, R)
        elif kind == "rand-expect":                       # lifts closer than 3R must be reported
            rep = run_rand(label, adj, ell, R, samples=2)
            rep.viol = [] if any("3R" in c for c, _ in rep.viol) else [("sensitivity: no violation reported", None)]
        else:                                             # (iii) is tight: lifts at distance exactly ell + 1
            rep = Report(f"{label} ell={ell}"); dec = Decomp(adj, inner_faces(adj), ell)
            U = Unfold(dec, dec.own[0]); root = U.hv(0, 0)
            d = U.bfs([root], ell + 1)
            lifts = sorted(dv for z, dv in d.items() if z[1] == 0 and z != root)
            if lifts[:1] != [ell + 1]:
                rep.bad("sensitivity: no second lift at distance ell + 1", lifts[:3])
    except Exception:
        rep = Report(f"{label} ell={ell} R={R}"); rep.bad("EXCEPTION", traceback.format_exc()[-1500:])
    rep.info["t"] = round(time.time() - t0, 1)
    return rep.name, rep.viol, rep.info


def main():
    args = sys.argv[1:]
    workers = 4
    if "--workers" in args:
        i = args.index("--workers"); workers = int(args[i + 1]); del args[i:i + 2]
    names = args or ["faces", "det", "wrap", "degree", "regime", "rand", "sensitivity"]
    nbad = 0
    for name in names:
        tasks = suite(name)
        print(f"== {name}: {len(tasks)} instances", flush=True)
        t0 = time.time(); rows = []
        with Pool(workers) as p:
            for label, viol, info in p.imap_unordered(job, tasks):
                rows.append((label, viol, info))
                if viol:
                    nbad += 1
                    print(f"VIOLATION {label}: {viol[:3]}", flush=True)
        for label, viol, info in sorted(rows):
            keep = {k: info[k] for k in ("n", "maxdeg", "h", "N1", "gf", "gamma", "BR_gf", "wrap", "infinite",
                                         "E_cuts", "bound", "cut_ratio", "t") if k in info}
            print(f"  {label:42s} {keep}", flush=True)
        if name in ("det", "wrap", "degree", "regime", "faces"):
            br = [info["BR_gf"] for _, _, info in rows if "BR_gf" in info]
            wr = sum(info.get("wrap", 0) for _, _, info in rows)
            print(f"  max B R / gamma_f = {max(br) if br else None}, wrapping windows = {wr}", flush=True)
        if name == "rand":
            cr = [info["cut_ratio"] for _, _, info in rows if info.get("cut_ratio") is not None]
            print(f"  max E[cuts] / (3 sum mu / R + 6h + 4N1) = {max(cr)}", flush=True)
        print(f"  {name}: {sum(1 for r in rows if r[1])} instances with violations, {round(time.time() - t0)}s",
              flush=True)
    print("all checks passed" if nbad == 0 else f"{nbad} instances with violations")
    sys.exit(1 if nbad else 0)


if __name__ == "__main__":
    main()
