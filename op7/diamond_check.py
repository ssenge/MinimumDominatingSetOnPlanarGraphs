"""Uniform-dual inequality for the cleaned hub rule (no LP needed).

With y = 1/rho on U: rho LP_U >= |U| - (1/3) sum_v (L_v - rho)^+, L_v = |N[v] n U|. For the cleaned
rule (round_exp.hubrule_clean) this gives |D minus D1| <= rho LP_U whenever
  slack = 3|P| + 3|Z| - 3|H*_W| - sum_{v: L_v > rho} (L_v - rho) >= 0,
where H = vertices with >= 4 U-neighbours, Z = U n N(H) minus H, U' = U minus N[H], T = idrule on
G[U'], P = U' minus T, H*_W = hubs outside U with a U-neighbour that has no T-neighbour.
slack(adj, U, rank, rho) returns the slack and the parts.
"""
import random
import sys


def parts(adj, U, rank):
    n = len(adj)
    cnt = [sum(U[w] for w in adj[v]) for v in range(n)]
    H = [cnt[v] >= 4 for v in range(n)]
    U2 = [U[v] and not H[v] and not any(H[w] for w in adj[v]) for v in range(n)]
    J = [False] * n
    for v in range(n):
        if U2[v]:
            nb = [w for w in adj[v] if U2[w]]
            sm = sum(rank[w] < rank[v] for w in nb)
            J[v] = sm < len(nb) - sm
    R = [U2[v] and not J[v] and not any(J[w] for w in adj[v]) for v in range(n)]
    Tset = [J[v] or R[v] for v in range(n)]
    domT = [Tset[v] or any(Tset[w] for w in adj[v]) for v in range(n)]
    keepW = [H[v] and not U[v] and any(U[w] and not domT[w] for w in adj[v]) for v in range(n)]
    Z = [U[v] and not H[v] and not U2[v] for v in range(n)]
    P = [U2[v] and not Tset[v] for v in range(n)]
    L = [cnt[v] + (1 if U[v] else 0) for v in range(n)]
    return H, Z, U2, Tset, P, keepW, L


def slack(adj, U, rank, rho):
    H, Z, U2, Tset, P, keepW, L = parts(adj, U, rank)
    oc = sum(L[v] - rho for v in range(len(adj)) if L[v] > rho and (U[v] or any(U[w] for w in adj[v])))
    return 3 * sum(P) + 3 * sum(Z) - 3 * sum(keepW) - oc


if __name__ == "__main__":
    pass
