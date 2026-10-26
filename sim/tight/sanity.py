# Check Facts A, B and the lemma sum_v g(d_v) >= c'|E| (s=5/8) on many planar graphs and random subgraphs.
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import rules as RU
from apo import apollonian
s, c = 5 / 8, 71423 / 262144

def stats(E, n):
    deg = [0] * n
    for a, b in E: deg[a] += 1; deg[b] += 1
    m = len(E); nz = sum(d > 0 for d in deg)
    A = sum(min(d, 3) for d in deg) >= m
    B = sum(min(d, 6) for d in deg) >= 2 * m - 2 * nz
    return A, B, sum(1 - s ** d for d in deg) / m

def edges(Q):
    ids = {u: i for i, u in enumerate(Q)}
    return [(ids[u], ids[x]) for u in Q for x in Q[u] if ids[u] < ids[x]], len(Q)

r = random.Random(0)
graphs = {"apollonian7": apollonian(7)}
for name, Q in {"delaunay": RU.fam_delaunay(3000, r, RU.unit), "stacked": RU.fam_stacked(1500, r, RU.unit),
                "trigrid": RU.fam_trigrid(40, r, RU.unit), "sqgrid": RU.fam_sqgrid(40, r, RU.unit),
                "K2n": RU.fam_k2n(500, r, RU.unit), "hubdeg2": RU.fam_hubdeg2(200, r, RU.unit),
                "cubic": RU.fam_cubic(2000, r, RU.unit)}.items():
    graphs[name] = edges(Q)
worst = (9, None)
for name, (E, n) in graphs.items():
    for keep in (1.0, 0.9, 0.7, 0.5, 0.3, 0.15):
        for _ in range(5 if keep < 1 else 1):
            Es = [e for e in E if r.random() < keep]
            if not Es: continue
            A, B, ratio = stats(Es, n)
            assert A and B, (name, keep)
            worst = min(worst, (ratio, f"{name} keep={keep}"))
print(f"c' = {c:.6f}; worst observed ratio {worst[0]:.6f} on {worst[1]}; facts A,B held everywhere")
