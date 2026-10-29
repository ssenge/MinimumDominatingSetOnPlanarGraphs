"""Check the Hub Lemma: if G[U] has maximum degree <= 2, then with H = {w outside U and D1 with
>= 4 neighbours in U}, U' = U minus N(H) and D = D1 + H + U', we have
|D| <= 3 x(V) - (|U_H| - e(B)/3) <= 3 x(V) - 0.2 |U_H|, for the cheapest x with {x >= 1/3} = D1.
Adversarial local search over D1 on planar girth >= 5 graphs; reports the smallest slack seen."""
import random
import sys

import networkx as nx
import numpy as np

from adv_battery import hub_pentagons
from adv_round import lp_given_S
from round_exp import pentagon_flower, random_planar_girth, subdivided_triangulation


def parts(adj, S):
    n = len(adj)
    U = [not (S[v] or any(S[w] for w in adj[v])) for v in range(n)]
    if any(U[v] and sum(U[w] for w in adj[v]) > 2 for v in range(n)):
        return None
    H = [not U[v] and not S[v] and sum(U[w] for w in adj[v]) >= 4 for v in range(n)]
    UH = [U[v] and any(H[w] for w in adj[v]) for v in range(n)]
    eB = sum(sum(U[w] for w in adj[v]) for v in range(n) if H[v])
    D = sum(S) + sum(H) + sum(U[v] and not UH[v] for v in range(n))
    return D, sum(UH), eB


def main(seed=1, iters=1500):
    rng = random.Random(seed)
    fams = [("pentagon flower k=8", pentagon_flower(8)), ("hub pentagons 6,2", hub_pentagons(6, 2, rng)),
            ("hub pentagons 4,4", hub_pentagons(4, 4, rng))]
    for n in (12, 20, 30):
        fams.append((f"subdivided triangulation n={n}", subdivided_triangulation(n, rng)))
    for n in (40, 70):
        fams.append((f"random planar girth>=5 n={n}", random_planar_girth(n, 5, rng)))
    for name, G in fams:
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        n = len(adj)
        A = np.eye(n)
        for v in range(n):
            for w in adj[v]:
                A[v, w] = 1
        best = None  # smallest (3 LP - |D|) - 0.2 |U_H| seen; must be >= 0
        maxuh = 0
        for _ in range(3):
            S = [rng.random() < 0.7 for _ in range(n)]  # start dense: small U, valid
            for _ in range(iters):
                v = rng.randrange(n)
                S[v] = not S[v]
                p = parts(adj, S)
                val = lp_given_S(A, S, 1 / 3) if p else None
                if val is None:
                    S[v] = not S[v]
                    continue
                D, uh, eB = p
                assert eB <= 2.4 * uh + 1e-9, (name, eB, uh)
                slack = 3 * val - D - 0.2 * uh
                assert slack >= -1e-6, (name, "Hub Lemma fails", D, val, uh)
                maxuh = max(maxuh, uh)
                if best is None or slack < best:
                    best = slack
                elif rng.random() < 0.5:
                    S[v] = not S[v]
        print(f"{name:32s} min slack {best if best is None else round(best, 4)}   max |U_H| seen {maxuh}",
              flush=True)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
