"""One level of heavy-star contraction (Amiri-Siebertz Alg. 1) under three arc-selection rules.

rule0: paper -- drop the reciprocal arc with larger-id tail, fair coins, select tail->head.
       Guarantee E[contracted] >= w(Q)/(8a).
rule1: keep both reciprocal arcs, fair coins.            Guarantee >= W_A/4 >= w(Q)/(4a).
rule2: keep both, random ranks r; select (P,X) iff r(X) > r(P) and r(X) > r(h(X)).
       Guarantee >= W_A/3 >= w(Q)/(3a).
W_A = sum over non-isolated parts P of w(heaviest edge at P).
"""
import random
import sys

import numpy as np
from scipy.spatial import Delaunay


def heaviest(Q):
    # h(P): heaviest incident edge, ties -> smaller id of the other endpoint (ids = part labels)
    return {P: max(nb, key=lambda X: (nb[X], -X)) for P, nb in Q.items() if nb}


def select(Q, h, rule, rng):
    arcs = list(h.items())
    if rule == 0:
        arcs = [(P, X) for P, X in arcs if not (h.get(X) == P and P > X)]
    if rule in (0, 1):
        head = {P: rng.random() < 0.5 for P in Q}
        return [(P, X) for P, X in arcs if not head[P] and head[X]]
    r = {P: rng.random() for P in Q}
    return [(P, X) for P, X in arcs if r[X] > r[P] and r[X] > r[h[X]]]


def contract(Q, S):
    centers = {X for _, X in S}
    leaves = {P for P, _ in S}
    assert not centers & leaves, "a part is both centre and leaf"
    assert len(leaves) == len(S), "a leaf joined two centres"
    rep = {P: P for P in Q}
    for P, X in S:
        rep[P] = X
    N = {}
    for P, nb in Q.items():
        for X, w in nb.items():
            a, b = rep[P], rep[X]
            if a != b:
                N.setdefault(a, {})
                N[a][b] = N[a].get(b, 0) + w
    for P in Q:
        N.setdefault(rep[P], {})
    return N


def weight(Q):
    return sum(w for nb in Q.values() for w in nb.values()) / 2


def delaunay(n, rng):
    pts = np.array([[rng.random(), rng.random()] for _ in range(n)])
    ids = list(range(n))
    rng.shuffle(ids)  # adversary-free random identifiers
    Q = {i: {} for i in ids}
    for s in Delaunay(pts).simplices:
        for i in range(3):
            a, b = ids[s[i]], ids[s[(i + 1) % 3]]
            Q[a][b] = Q[b][a] = 1
    return Q


def path(n, rng):
    ids = list(range(n))
    rng.shuffle(ids)
    Q = {i: {} for i in ids}
    for a, b in zip(ids, ids[1:]):
        Q[a][b] = Q[b][a] = 1
    return Q


def one_level(Q, rule, rng):
    h = heaviest(Q)
    WA = sum(Q[P][X] for P, X in h.items())
    w0 = weight(Q)
    w1 = weight(contract(Q, select(Q, h, rule, rng)))
    return (w0 - w1) / w0, (w0 - w1) / WA


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    a = 3
    bound = {0: 1 / (8 * a), 1: 1 / (4 * a), 2: 1 / (3 * a)}
    for name, gen in [("delaunay", lambda: delaunay(3000, rng)), ("path", lambda: path(20000, rng))]:
        for rule in (0, 1, 2):
            fr = [one_level(gen(), rule, rng) for _ in range(5)]
            fq = sum(x for x, _ in fr) / len(fr)
            fa = sum(y for _, y in fr) / len(fr)
            print(f"{name:9s} rule{rule}: contracted/w(Q)={fq:.3f} (proved >= {bound[rule]:.3f})  /W_A={fa:.3f}")
        # multi-level: per-level empirical q on a triangulation
    for rule in (0, 1, 2):
        Q = delaunay(3000, rng)
        qs = []
        for _ in range(6):
            w0 = weight(Q)
            if w0 == 0:
                break
            Q = contract(Q, select(Q, heaviest(Q), rule, rng))
            qs.append(weight(Q) / w0)
        print(f"levels rule{rule}: q per level =", " ".join(f"{q:.3f}" for q in qs))


if __name__ == "__main__":
    main()
