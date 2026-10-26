"""Compare one-level star-selection rules on planar families (fraction of w(Q) contracted).

Every rule returns S = [(leaf, centre)]; levels.contract() asserts the stars are disjoint.
"""
import random
import sys

import numpy as np
from scipy.spatial import Delaunay

import levels as L


# ---------- planar families ----------
def _relabel(edges, n, rng, wfun):
    ids = list(range(n))
    rng.shuffle(ids)
    Q = {i: {} for i in ids}
    for a, b in edges:
        a, b = ids[a], ids[b]
        if a != b and b not in Q[a]:
            Q[a][b] = Q[b][a] = wfun(rng)
    return Q


def _tri_edges(pts):
    E = set()
    for s in Delaunay(pts).simplices:
        for i in range(3):
            a, b = sorted((int(s[i]), int(s[(i + 1) % 3])))
            E.add((a, b))
    return E, Delaunay(pts).simplices


def fam_delaunay(n, rng, wfun):
    E, _ = _tri_edges(np.random.default_rng(rng.randrange(1 << 30)).random((n, 2)))
    return _relabel(E, n, rng, wfun)


def fam_trigrid(k, rng, wfun):
    idx = lambda i, j: i * k + j
    E = [(idx(i, j), idx(i + di, j + dj)) for i in range(k) for j in range(k)
         for di, dj in ((0, 1), (1, 0), (1, 1)) if i + di < k and j + dj < k]
    return _relabel(E, k * k, rng, wfun)


def fam_sqgrid(k, rng, wfun):
    idx = lambda i, j: i * k + j
    E = [(idx(i, j), idx(i + di, j + dj)) for i in range(k) for j in range(k)
         for di, dj in ((0, 1), (1, 0)) if i + di < k and j + dj < k]
    return _relabel(E, k * k, rng, wfun)


def fam_k2n(n, rng, wfun):
    return _relabel([(0, i) for i in range(2, n + 2)] + [(1, i) for i in range(2, n + 2)], n + 2, rng, wfun)


def fam_stacked(h, rng, wfun):
    # hub triangulation plus one degree-3 vertex in every face (Apollonian step)
    E, faces = _tri_edges(np.random.default_rng(rng.randrange(1 << 30)).random((h, 2)))
    E = list(E)
    for f, s in enumerate(faces):
        v = h + f
        E += [(int(s[0]), v), (int(s[1]), v), (int(s[2]), v)]
    return _relabel(E, h + len(faces), rng, wfun)


def fam_hubdeg2(h, rng, wfun, k=4):
    # hub triangulation, every hub edge doubled by k paths of length 2
    E, _ = _tri_edges(np.random.default_rng(rng.randrange(1 << 30)).random((h, 2)))
    E2, v = list(E), h
    for a, b in E:
        for _ in range(k):
            E2 += [(a, v), (b, v)]
            v += 1
    return _relabel(E2, v, rng, wfun)


def fam_cubic(n, rng, wfun):
    # planar dual of a Delaunay triangulation: 3-regular
    tri = Delaunay(np.random.default_rng(rng.randrange(1 << 30)).random((n, 2)))
    E = [(f, int(g)) for f, nb in enumerate(tri.neighbors) for g in nb if g > f]
    return _relabel(E, len(tri.simplices), rng, wfun)


# ---------- rules ----------
def rule_rank(Q, rng):
    return L.select(Q, L.heaviest(Q), 2, rng)


def _join(Q, centres, cand):
    # each candidate joins its heaviest centre neighbour (ties: smaller id)
    S = []
    for P in cand:
        cs = [X for X in Q[P] if X in centres]
        if cs:
            S.append((P, max(cs, key=lambda X: (Q[P][X], -X))))
    return S


def rule_rc(Q, rng, p=0.375, rounds=1, lonely=False):
    centres, S, free = set(), [], set(Q)
    for _ in range(rounds):
        new = {P for P in free if Q[P] and rng.random() < p}
        centres |= new
        free -= new
        s = _join(Q, centres, free)
        S += s
        free -= {P for P, _ in s}
    if lonely:  # centres nobody joined may join a centre that has leaves
        busy = {X for _, X in S}
        S += _join(Q, busy, [C for C in centres if C not in busy])
    return S


def rule_degmax(Q, rng, rounds=3):
    # Luby rounds: centre iff (weighted degree * U) beats all free neighbours; others join heaviest centre
    wdeg = {P: sum(nb.values()) for P, nb in Q.items()}
    centres, S, free = set(), [], {P for P in Q if Q[P]}
    for _ in range(rounds):
        sc = {P: wdeg[P] * rng.random() for P in free}
        new = {P for P in free if all(sc[P] > sc[X] for X in Q[P] if X in free)}
        centres |= new
        free -= new
        s = _join(Q, centres, free)
        S += s
        free -= {P for P, _ in s}
    return S


RULES = {
    "rank(forest)": rule_rank,
    "rc p=.375": rule_rc,
    "rc p=.3 x3": lambda Q, r: rule_rc(Q, r, 0.3, 3),
    "rc p=.3 x3+lonely": lambda Q, r: rule_rc(Q, r, 0.3, 3, True),
    "degmax x3": rule_degmax,
}

unit = lambda r: 1
unif = lambda r: r.random()
expo = lambda r: r.expovariate(1)

FAMILIES = {
    "delaunay": lambda r, w: fam_delaunay(3000, r, w),
    "trigrid": lambda r, w: fam_trigrid(50, r, w),
    "sqgrid": lambda r, w: fam_sqgrid(50, r, w),
    "K2n": lambda r, w: fam_k2n(2000, r, w),
    "stacked": lambda r, w: fam_stacked(1000, r, w),
    "hub+deg2": lambda r, w: fam_hubdeg2(300, r, w),
    "cubic": lambda r, w: fam_cubic(2000, r, w),
}


def _add(Q, a, b, w):
    Q.setdefault(a, {})[b] = w
    Q.setdefault(b, {})[a] = w


def adv_pendtrap(r):  # heavy triangulation, every vertex with 5 light pendants
    Q = fam_delaunay(1000, r, unit)
    v = max(Q) + 1
    for P in list(Q):
        for _ in range(5):
            _add(Q, P, v, 0.02)
            v += 1
    return Q


def adv_matching(r):  # heavy maximal matching inside a triangulation
    Q = fam_delaunay(2000, r, unit)
    used = set()
    for P in Q:
        for X in Q[P]:
            if P not in used and X not in used:
                Q[P][X] = Q[X][P] = 10
                used |= {P, X}
    return Q


def adv_k2n_infl(r):  # K_{2,n} whose leaves are inflated by light pendants
    Q = fam_k2n(300, r, unit)
    hubs = [P for P in Q if len(Q[P]) == 300]
    v = max(Q) + 1
    for P in list(Q):
        if P not in hubs:
            for _ in range(20):
                _add(Q, P, v, 0.01)
                v += 1
    return Q


def adv_caterpillar(r):  # spine weights increasing, two slightly lighter pendants per spine vertex
    Q, m = {}, 3000
    ids = list(range(3 * m))
    r.shuffle(ids)
    for i in range(m - 1):
        _add(Q, ids[i], ids[i + 1], 1 + i / m)
    for i in range(m):
        for j in (1, 2):
            _add(Q, ids[i], ids[j * m + i], 1 + (i - 0.5) / m)
    return Q


ADV = {"pendtrap": adv_pendtrap, "matching": adv_matching, "K2n-infl": adv_k2n_infl,
       "caterpil": adv_caterpillar, "K2n": lambda r: fam_k2n(300, r, unit),
       "sqgrid": lambda r: fam_sqgrid(40, r, unit)}


def frac(Q, rule, rng):
    w0 = L.weight(Q)
    return (w0 - L.weight(L.contract(Q, rule(Q, rng)))) / w0


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    if len(sys.argv) > 2 and sys.argv[2] == "adv":
        print(" " * 20 + "".join(f"{f:>10s}" for f in ADV) + "       min")
        for rname, rule in RULES.items():
            vals = [sum(frac(g(rng), rule, rng) for _ in range(20)) / 20 for g in ADV.values()]
            print(f"{rname:20s}" + "".join(f"{v:10.3f}" for v in vals) + f"{min(vals):10.3f}")
        return
    trials = 3
    for wname, wf in (("unit", unit), ("unif", unif), ("expo", expo)):
        print(f"\nweights={wname}   (fraction of w(Q) contracted in one level; higher is better)")
        print(" " * 20 + "".join(f"{f:>10s}" for f in FAMILIES) + "       min")
        for rname, rule in RULES.items():
            vals = []
            for fname, fam in FAMILIES.items():
                vals.append(sum(frac(fam(rng, wf), rule, rng) for _ in range(trials)) / trials)
            print(f"{rname:20s}" + "".join(f"{v:10.3f}" for v in vals) + f"{min(vals):10.3f}")


if __name__ == "__main__":
    main()
