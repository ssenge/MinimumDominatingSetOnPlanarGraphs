"""Do clusters of U-hubs break the rules that put every U-hub into D?

Host: the dodecahedron C (cubic, girth 5) with one pendant vertex per C-vertex placed inside a face,
plus random filling points; all points are Delaunay triangulated and edges are added greedily
(C edges and pendant edges first) as long as girth >= 5. The adversary then picks U directly
(uonly_direct style, starting from C plus the pendants) and identifiers, maximizing
|D minus D1| / LP_U for: uhub (R2), uhub_clean (U-hubs join only if not dominated by T),
clean (hubrule_clean), plain idrule on G[U].
"""
import random
import sys

import networkx as nx
import numpy as np
from scipy.spatial import Delaunay

import uonly_direct
from clean_battery import clean_size_U, uhub_size_U, r12_size_U, r13_size_U
from round_exp import girth_ok


def uhub_clean_size_U(adj, U, rank):
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
    T = [J[v] or R[v] for v in range(n)]
    keep = [HU[v] and not any(T[w] for w in adj[v]) for v in range(n)]
    return sum(keep) + sum(T)


def idrule_size_U(adj, U, rank):
    return uonly_direct.hub_size(adj, U, rank, "idrule")


SIZES = {"uhub": uhub_size_U, "uhub_clean": uhub_clean_size_U, "clean": clean_size_U, "idrule": idrule_size_U,
         "r12": r12_size_U, "r13": r13_size_U}


def can_add(G, a, b, g=5):
    if G.has_edge(a, b):
        return False
    try:
        d = nx.shortest_path_length(G, a, b)
    except nx.NetworkXNoPath:
        return True
    return d + 1 >= g


def host(nfill, rng, per_face=False):
    C = nx.dodecahedral_graph()
    pos = nx.planar_layout(C)
    ok, emb = nx.check_planarity(C)
    faces, seen = [], set()
    for u, v in emb.edges():
        if (u, v) not in seen:
            faces.append(emb.traverse_face(u, v, mark_half_edges=seen))
    pts = {v: np.array(pos[v]) for v in C}
    G = nx.Graph(C)
    nid = 20
    face_of = {}
    for a in C:
        fs = [f for f in faces if a in f]
        for f in (fs if per_face else [rng.choice(fs)]):
            cen = np.mean([pts[b] for b in f], axis=0)
            if len(f) == 5 and np.linalg.norm(cen) < 1e-9:
                cen = pts[a] * 1.5
            pts[nid] = pts[a] + 0.3 * (cen - pts[a])
            G.add_edge(a, nid); nid += 1
    for _ in range(nfill):
        pts[nid] = np.array([rng.uniform(-1.2, 1.2), rng.uniform(-1.2, 1.2)])
        G.add_node(nid); nid += 1
    keys = sorted(pts)
    P = np.array([pts[k] for k in keys])
    E = set()
    for t in Delaunay(P).simplices:
        for i in range(3):
            a, b = keys[t[i]], keys[t[(i + 1) % 3]]
            E.add((min(a, b), max(a, b)))
    E = list(E); rng.shuffle(E)
    for a, b in E:
        if a < 20 and b < 20:
            continue  # keep C exactly the dodecahedron (its own edges are already in)
        if can_add(G, a, b):
            G.add_edge(a, b)
            if not nx.check_planarity(G)[0]:
                G.remove_edge(a, b)
    planar = nx.check_planarity(G)[0]
    return nx.convert_node_labels_to_integers(G), planar


def search(adj, size, rng, iters, init):
    n = len(adj)
    cand = [v for v in range(n) if len(adj[v]) >= 3]
    U = [v in init and len(adj[v]) >= 3 for v in range(n)]
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


def main(seed=1, trials=4, iters=3000, per_face=0):
    rng = random.Random(int(seed)); per_face = bool(int(per_face))
    worst = {}
    for tr in range(int(trials)):
        for nfill in (20, 40, 60):
            G, planar = host(nfill, rng, per_face)
            assert planar and girth_ok(G, 5)
            adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
            init = set(range(80 if per_face else 40))
            out = []
            for k, size in SIZES.items():
                r = max(search(adj, size, rng, int(iters), init) for _ in range(2))
                worst[k] = max(worst.get(k, 0), r)
                out.append(f"{k}={r:.3f}")
            print(f"trial {tr} fill {nfill} n={len(adj)} " + " ".join(out), flush=True)
    print("max:", {k: round(v, 3) for k, v in worst.items()})


if __name__ == "__main__":
    main(*sys.argv[1:])
