"""Battery for the cleaned hub rule (round_exp.hubrule_clean) against hubrule_all.

mode uonly : adversary picks D1 and identifiers, score (|D| - |D1|) / LP_U (uonly_hub families).
mode direct: adversary picks U directly (any vertices of degree >= 3), score |D minus D1| / LP_U.
mode dense : hub-dense planar girth-5 families, adversary picks D1, score |D| / LP (full LP).
mode pocket: the periodic pocket structures of pocket_enum, per-period slope against the full LP
             and against LP_U.
"""
import itertools
import random
import sys

import networkx as nx
import numpy as np

import uonly_direct
import uonly_hub
from adv_round import lp_given_S, search as full_search
from adv_battery import hub_pentagons
from dense_hub_battery import greedy_girth5, grid_faces
from diamond_check import parts
from round_exp import (girth_ok, hubrule_all, hubrule_clean, pentagon_flower, random_planar_girth,
                       subdivided_triangulation, uhub_idrule, hubrule_r12,
                       hubrule_r13, r13_size)


def clean_size_U(adj, U, rank):
    H, Z, U2, T, P, keepW, L = parts(adj, U, rank)
    return sum(H[v] and U[v] for v in range(len(adj))) + sum(keepW) + sum(T)


def uhub_size_U(adj, U, rank):
    n = len(adj)
    HU = [U[v] and sum(U[w] for w in adj[v]) >= 4 for v in range(n)]
    U2 = [U[v] and not HU[v] for v in range(n)]
    J = [False] * n
    for v in range(n):
        if U2[v]:
            nb = [w for w in adj[v] if U2[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    R = [U2[v] and not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    return sum(HU) + sum(J) + sum(R)


def r12_size_U(adj, U, rank):
    S = [False] * len(adj)
    # hubrule_r12 with D1 empty: x = 0 everywhere gives U = all vertices; emulate U by a fake D1
    n = len(adj)
    import numpy as _np
    from round_exp import _idrule_on
    H = [sum(U[w] for w in adj[v]) >= 4 and (U[v] or any(U[w] for w in adj[v])) for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    T = _idrule_on(adj, U2, rank)
    Q = [U[v] and not U2[v] and not any(T[w] for w in adj[v]) for v in range(n)]
    a = [sum(Q[w] for w in adj[v]) if H[v] else -1 for v in range(n)]
    sel = [False] * n
    Ql = [False] * n
    for q in range(n):
        if Q[q]:
            c = [w for w in adj[q] + [q] if H[w] and a[w] >= 4]
            if c:
                sel[max(c, key=lambda w: (a[w], -rank[w]))] = True
            else:
                Ql[q] = True
    T2 = _idrule_on(adj, Ql, rank)
    return sum(T) + sum(sel) + sum(T2)


def r13_size_U(adj, U, rank):
    return r13_size(adj, U, rank)


def all_size_U(adj, U, rank):
    H, Z, U2, T, P, keepW, L = parts(adj, U, rank)
    return sum(H) + sum(T)


def planar_fams(rng):
    fams = [("dodecahedron", nx.dodecahedral_graph()), ("pentagon flower k=8", pentagon_flower(8)),
            ("hub pentagons 6,2", hub_pentagons(6, 2, rng)), ("hub pentagons 4,4", hub_pentagons(4, 4, rng))]
    for n in (30, 50, 70):
        fams.append((f"random planar g>=5 n={n}", random_planar_girth(n, 5, rng)))
    for n in (12, 20):
        fams.append((f"subdivided triangulation n={n}", subdivided_triangulation(n, rng)))
    for n in (30, 45, 60):
        fams.append((f"greedy maximal girth5 n={n}", greedy_girth5(n, rng)))
    for m in (4, 5):
        fams.append((f"subdivided grid + faces m={m}", grid_faces(m)))
    return fams


def direct_search(adj, size, rng, iters):
    n = len(adj)
    cand = [v for v in range(n) if len(adj[v]) >= 3]
    U = [False] * n
    for v in cand:
        U[v] = rng.random() < 0.6
    rank = list(range(n)); rng.shuffle(rank)

    def sc():
        if not any(U):
            return -1
        val = uonly_direct.lp_u(adj, U)
        return size(adj, U, rank) / val if val else -1

    cur = sc()
    for _ in range(iters):
        if rng.random() < 0.5:
            v = rng.choice(cand); U[v] = not U[v]
            new = sc()
            if new >= cur:
                cur = new
            else:
                U[v] = not U[v]
        else:
            a, b = rng.randrange(n), rng.randrange(n)
            rank[a], rank[b] = rank[b], rank[a]
            new = sc()
            if new >= cur:
                cur = new
            else:
                rank[a], rank[b] = rank[b], rank[a]
    return cur


KEYS = ("clean", "all")


def main(mode="uonly", seed=1, iters=2000, keys="clean,all"):
    global KEYS
    KEYS = tuple(keys.split(","))
    rng = random.Random(int(seed)); iters = int(iters)
    worst = {}
    if mode == "pocket":
        import pocket_enum
        for P in range(3, 9):
            for top, bot in itertools.product(pocket_enum.hub_families(P), repeat=2):
                for off in range(P):
                    vals = []
                    for K in (6, 12):
                        G, S, n = pocket_enum.build(P, K, top, bot, off)
                        if any(G.degree(u) < 3 for u in range(n)) or not (girth_ok(G, 5) and nx.check_planarity(G)[0]):
                            break
                        nodes = list(range(n)) + [v for v in G if not isinstance(v, int)]
                        idx = {v: i for i, v in enumerate(nodes)}
                        adj = [sorted(idx[w] for w in G[v]) for v in nodes]
                        N = len(nodes)
                        A = np.eye(N)
                        for v in range(N):
                            for w in adj[v]:
                                A[v, w] = 1
                        Sl = [v in S for v in nodes]
                        full = lp_given_S(A, Sl, 1 / 3)
                        uval, _ = uonly_hub.lp_u(adj, Sl)
                        if full is None or uval is None:
                            break
                        x = np.array([1 / 3 if s else 0.0 for s in Sl])
                        rk = list(range(N))
                        vals.append((sum(Sl), full, uval, hubrule_clean(adj, x, rk, 1 / 3), hubrule_all(adj, x, rk, 1 / 3)))
                    if len(vals) < 2:
                        continue
                    (s1, f1, u1, c1, a1), (s2, f2, u2, c2, a2) = vals
                    for k, d1, d2 in (("clean", c1, c2), ("all", a1, a2)):
                        rf = (d2 - d1) / (f2 - f1)
                        ru = ((d2 - s2) - (d1 - s1)) / (u2 - u1) if u2 > u1 else 0
                        if rf > worst.get((k, "full"), (0,))[0]:
                            worst[(k, "full")] = (rf, P, top, bot, off)
                        if ru > worst.get((k, "uonly"), (0,))[0]:
                            worst[(k, "uonly")] = (ru, P, top, bot, off)
            print(P, {k: round(v[0], 4) for k, v in worst.items()}, flush=True)
        print("worst", worst)
        return
    for name, G in planar_fams(rng):
        assert girth_ok(G, 5) and nx.check_planarity(G)[0], name
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        out = []
        RULE = {"clean": hubrule_clean, "all": hubrule_all, "uhub": uhub_idrule, "r12": hubrule_r12,
                "r13": hubrule_r13}
        SIZE = {"clean": clean_size_U, "all": all_size_U, "uhub": uhub_size_U, "r12": r12_size_U,
                "r13": r13_size_U}
        for k in KEYS:
            if mode == "uonly":
                r = max(uonly_hub.search(adj, RULE[k], rng, iters) for _ in range(3))
            elif mode == "direct":
                r = max(direct_search(adj, SIZE[k], rng, iters) for _ in range(3))
            else:
                r = max(full_search(adj, RULE[k], 1 / 3, rng, iters) for _ in range(2))
            worst[k] = max(worst.get(k, 0), r)
            out.append(f"{k}={r:.3f}")
        print(f"{name:32s} n={len(adj):3d} " + "  ".join(out), flush=True)
    print(mode, "max:", {k: round(v, 3) for k, v in worst.items()})


if __name__ == "__main__":
    main(*sys.argv[1:])
