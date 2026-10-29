# exact join-only ratio sum_v (1-s^d)/m for unit weights, and simulated full ratio (with internal edges)
import math, os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import rules as RU

def apollonian(depth):
    E = {(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)}
    faces = [(0, 1, 3), (1, 2, 3), (0, 2, 3), (0, 1, 2)]
    n = 4
    for _ in range(depth):
        nf = []
        for a, b, c in faces:
            v = n; n += 1
            E |= {(a, v), (b, v), (c, v)}
            nf += [(a, b, v), (b, c, v), (a, c, v)]
        faces = nf
    return E, n

def ratio(E, n, s):
    deg = [0] * n
    for a, b in E: deg[a] += 1; deg[b] += 1
    return sum(1 - s ** d for d in deg) / len(E)

def stacked_on(base_E, base_faces, n):  # one stacking level over given faces
    E = set(base_E)
    for a, b, c in base_faces:
        E |= {(a, n), (b, n), (c, n)}; n += 1
    return E, n

if __name__ == "__main__":
    for s in (0.62, 0.65, 0.6687, 0.69, 0.72):
        row = [s * ratio(*apollonian(d), s) for d in (3, 5, 7, 9)]
        bip = s * (1 - s ** 4) / 3
        k2n = s * (1 - s ** 2) / 2
        print(f"s={s:.4f} join-only f: apollonian depth3/5/7/9 = " + " ".join(f"{v:.4f}" for v in row) + f"   bipyr {bip:.4f}  K2n {k2n:.4f}")
    E, n = apollonian(7)
    r = random.Random(1)
    Q = RU._relabel(list(E), n, r, RU.unit)
    for p in (0.30, 0.35, 0.40, 0.45):
        full = sum(RU.frac(Q, lambda Q, rr: RU.rule_rc(Q, rr, p), r) for _ in range(3)) / 3
        print(f"apollonian depth7 p={p}: full (with internal edges) {full:.4f}   join-only exact {(1-p)*ratio(E, n, 1-p):.4f}")
