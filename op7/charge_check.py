"""Charge-level instance check of the R13 certificate (discharge_r13v7, argument in SOUNDNESS.md).

check_r13z.py tests the type model and the total |D'| <= rho dual(y). This script tests the local
argument itself. For an instance it computes the actual charge of every vertex and of both parts
of every heavy U-hub: initial charge, overclaim payments of Z1, the transfer on every edge and
every payment to a heavy hub (values from the exact LP solution of cert_exact.py), and the Euler
terms from the actual degrees (leaves, light-hub returns). Every vertex or part with an LP row
must end with at least the certified margin, every light hub with at least 0, and the total must
equal rho dual(y) - |D'| plus the Euler sums.

Usage: GIRTH=5 MOD=discharge_r13v8 python3 charge_check.py rho seed rounds iters
(needs certs/{MOD}_g{GIRTH}_rho{rho}_exact.pkl from cert_exact.py; MOD defaults to v8, where a
heavy U-hub is one entity and the family Zh exists; with MOD=discharge_r13v7 the two parts of a
heavy U-hub are checked separately)
"""
import importlib
import os
import pickle
import random
import sys

import networkx as nx

from check_r13z import classify, graphs
from round_exp import random_planar_girth

MOD = os.environ.get("MOD", "discharge_r13v8")
r7 = importlib.import_module(MOD)
C = r7.C53
R9 = getattr(r7, "R9", 1 / 9)  # return of a light hub to each Q_l-neighbour


def load(rho):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certs",
                        f"{MOD}_g{r7.GIRTH}_rho{rho}_exact.pkl")
    x = [float(v) for v in pickle.load(open(path, "rb"))["x"]]
    lp, info = r7.build(float(rho))
    assert len(x) == lp.nv
    UT, HT, LT, HHT, ZT = r7.types()
    zz = [t for t in ZT if "Z1" in t[1]]
    return x, info, {t: i for i, t in enumerate(zz)}


def tau(deg):
    return 0.0 if deg == 0 else (-0.5 if deg == 1 else deg / 2 - C)


def charges(adj, U, rank, rho, x, info, zord):
    typ, size, s = classify(adj, U, rank, full=True)
    n = len(adj)
    H, U2, T, Z, Q, Z1 = s["H"], s["U2"], s["T"], s["Z"], s["Q"], s["Z1"]
    heavy, HU, lightU, Qh, Ql, T2 = s["heavy"], s["HU"], s["lightU"], s["Qh"], s["Ql"], s["T2"]
    choice, nsel = s["choice"], s["nsel"]
    X, val = info["X"], (lambda v: x[v])
    eps = info["eps"]
    y = [0.0] * n
    for v, t in typ.items():
        y[v] = (1 - x[eps[t]]) / 3
    Y = [y[v] + sum(y[w] for w in adj[v]) for v in range(n)]
    over = [max(0.0, Y[v] - 1) for v in range(n)]
    Y1 = [sum(y[w] for w in adj[v] if Z1[w]) for v in range(n)]
    nhub = [sum(H[w] for w in adj[v]) for v in range(n)]
    for v in range(n):
        if not U[v] and not H[v]:
            assert over[v] < 1e-12, "overclaim at a non-hub outside U"
    ent = {}
    split = "Zh" not in info["nu"]  # v7: vertex part and hub part of a heavy U-hub separately

    def key(v):  # the entity that holds the hub side of a heavy hub
        return ("hp", v) if HU[v] and split else v

    def vkey(v):  # the entity that holds the vertex side of a heavy U-hub
        return ("vp", v) if split else v

    for v in range(n):
        if HU[v] and not split:
            ent[v] = rho * y[v] - rho / 3 * over[v] + rho / 3 * Y1[v] - (nsel[v] > 0)
        elif HU[v]:
            ent[("vp", v)] = rho * y[v]
            ent[("hp", v)] = -rho / 3 * over[v] + rho / 3 * Y1[v] - (nsel[v] > 0)
        elif H[v]:  # W-hubs and light U-hubs
            ent[v] = (rho * y[v] if U[v] else 0.0) - rho / 3 * over[v] + rho / 3 * Y1[v] \
                - (nsel[v] > 0) - (U[v] and T2[v])
        elif U[v]:
            ent[v] = rho * y[v] - rho / 3 * over[v] - (T[v] or T2[v])
            if Z1[v]:
                ent[v] -= nhub[v] * rho / 3 * y[v]

    def move(a, b, amt):  # a receives amt from b
        ent[a] += amt
        ent[b] -= amt

    hcls, lcls, lbase = r7.hcls, r7.lcls, r7.lbase
    for u in range(n):
        for v in adj[u]:
            if v < u or not (U[u] and U[v]):
                continue
            if HU[u] or HU[v]:
                continue  # no transfers at vertex parts of heavy U-hubs
            cat = {}
            for w in (u, v):
                cat[w] = "U2" if U2[w] else "Z1" if Z1[w] else "Qh" if Qh[w] else "Ql"
            cu, cv = cat[u], cat[v]
            if cu == cv == "U2" or cu == cv == "Ql":
                sm, lg = (u, v) if rank[u] < rank[v] else (v, u)
                f = (lambda t: t) if cu == "U2" else lbase
                k = val(X[("arc", f(typ[sm]), f(typ[lg]))])
                move(sm, lg, k)
                continue
            pair = {cu: u, cv: v}
            if set(pair) == {"U2", "Qh"}:
                p, q = pair["U2"], pair["Qh"]
                move(p, q, val(X[("edge", (typ[p], "Qh"), (hcls(typ[q]), "P"))]))
            elif set(pair) == {"U2", "Ql"}:
                p, q = pair["U2"], pair["Ql"]
                move(p, q, val(X[("edge", (typ[p], "Ql"), (lcls(typ[q]), "P"))]))
            elif cu == cv == "Qh":
                a, b = hcls(typ[u]), hcls(typ[v])
                if a != b:  # the LP orders the classes as sorted tuples; the first receives
                    (ca, pa), (cb, pb) = sorted([(a, u), (b, v)])
                    move(pa, pb, val(X[("edge", (ca, "Qh"), (cb, "Qh"))]))
            elif set(pair) == {"Qh", "Ql"}:
                qh, ql = pair["Qh"], pair["Ql"]
                k = "QlT" if T2[ql] else "QlP"
                move(qh, ql, val(X[("edge", (hcls(typ[qh]), k), (lcls(typ[ql]), "Qh"))]))
            elif set(pair) == {"Z1", "U2"}:
                z, p = pair["Z1"], pair["U2"]
                move(z, p, val(X[("edge", (typ[z], "T" if T[p] else "P"), (typ[p], "Z1"))]))
            elif set(pair) == {"Z1", "Qh"} or set(pair) == {"Z1", "Ql"}:
                z = pair["Z1"]
                q = pair.get("Qh", pair.get("Ql"))
                if lightU[q]:
                    continue  # Z1 - light U-hub: no transfer
                if Qh[q]:
                    move(z, q, val(X[("edge", (typ[z], "Qh"), (hcls(typ[q]), "Z1"))]))
                else:
                    move(z, q, val(X[("edge", (typ[z], "Ql"), (lcls(typ[q]), "Z1"))]))
            elif cu == cv == "Z1":
                if typ[u] != typ[v]:
                    a, b = sorted((u, v), key=lambda w: zord[typ[w]])
                    move(a, b, val(X[("edge", (typ[a], "Z1"), (typ[b], "Z1"))]))
            else:
                raise AssertionError(f"edge kind {cu}-{cv} not expected")
    # payments to heavy hubs
    gs, gn, hs, hn = info["gs"], info["gn"], info["hs"], info["hn"]
    for q in range(n):
        if not Qh[q]:
            continue
        t = typ[q]
        hubs = [w for w in adj[q] + [q] if heavy[w]]
        dom = any(T2[u] for u in adj[q])
        for w in hubs:
            if HU[q]:
                if w == q and not split:
                    continue  # v8: the payment to its own hub part is internal
                amt = val(hs[t]) if w == choice[q] else val(hn[t])
                move(key(w), vkey(q), amt)
            elif w == choice[q] and not dom:
                move(key(w), q, val(gs[t]))
            else:
                move(key(w), q, val(gn[t]))
    # Euler terms
    nu, lam, nuHU = info["nu"], val(info["lam"]), val(info["nu"]["HU"])
    inZ = [Z[v] or H[v] for v in range(n)]
    rich = [Qh[v] and not heavy[v] and sum(heavy[w] for w in adj[v]) >= 3 for v in range(n)]
    esum = 0.0
    for f in ("Z", "ZU"):
        inF = [inZ[v] or (f == "ZU" and U2[v]) for v in range(n)]

        def edge_in(u, v):
            if not (inF[u] and inF[v]):
                return False
            if U[u] and U[v]:
                return f == "ZU" or (Z[u] and Z[v])
            return (Z[u] and H[v] and not U[v]) or (Z[v] and H[u] and not U[u])
        deg = [sum(edge_in(v, w) for w in adj[v]) if inF[v] else 0 for v in range(n)]
        th = [tau(deg[v]) for v in range(n)]
        for w in range(n):
            if H[w] and not heavy[w]:
                for q in adj[w]:
                    if Ql[q]:
                        assert edge_in(w, q)
                        th[w] -= R9
                        th[q] += R9
        nf = val(nu[f])
        esum += nf * sum(th)
        assert sum(th) <= 1e-9, f"Euler sum of {f} positive"
        for v in range(n):
            if not th[v] and not deg[v]:
                continue
            if HU[v] and split:
                kw = sum(heavy[w] and not U[w] for w in adj[v])
                ent[("vp", v)] += nf * kw / 2
                ent[("hp", v)] += nf * (th[v] - kw / 2)
            elif v in ent:
                ent[v] += nf * th[v]
            if lightU[v]:  # budget of a light U-hub: what its vertex part does not claim
                kw = sum(heavy[w] and not U[w] for w in adj[v])
                assert th[v] - kw / 2 >= -1e-12, "light U-hub budget"
    if not split:  # Zh = G[Q_h + heavy W-hubs] without W-hub - W-hub edges
        inh = [Qh[v] or (heavy[v] and not U[v]) for v in range(n)]
        dzh = [sum(inh[w] and (U[v] or U[w]) for w in adj[v]) if inh[v] else 0 for v in range(n)]
        th = [tau(d) for d in dzh]
        assert sum(th) <= 1e-9, "Euler sum of Zh positive"
        nf = val(nu["Zh"])
        esum += nf * sum(th)
        for v in range(n):
            if th[v]:
                ent[key(v)] += nf * th[v]
    dHU = [sum(HU[w] for w in adj[v]) if HU[v] else 0 for v in range(n)]
    thu = [tau(d) for d in dHU]
    assert sum(thu) <= 1e-9
    esum += nuHU * sum(thu)
    for v in range(n):
        if HU[v]:
            ent[vkey(v)] += nuHU * thu[v]
    dB = [sum(heavy[w] for w in adj[v]) if rich[v] else sum(rich[w] for w in adj[v]) if heavy[v] else 0
          for v in range(n)]
    tb = [lam * (d / 2 - 1.5) if d else 0.0 for d in dB]
    esum += sum(tb)
    for v in range(n):
        if tb[v]:
            ent[key(v)] += tb[v]
    # total: rho dual(y) - |D'| + Euler sums
    dual = sum(y) - sum(over) / 3
    tot = sum(ent.values())
    assert abs(tot - (rho * dual - size + esum)) < 1e-7, (tot, rho * dual - size + esum)
    light = [v for v in range(n) if H[v] and not heavy[v] and not U[v]]
    lp_ent = [k for k in ent if k not in light]
    return min((ent[k], k) for k in lp_ent), min([ent[k] for k in light] or [1.0]), typ


def regress(rho, x, info, zord):
    """The counterexamples of the referee pass against v6f (discharge_r13z): a Q_h leaf next to a
    light W-hub (v6f: charge -0.085), a "u"-type next to a light W-hub, and stars of heavy U-hubs
    (coefU). U is every vertex except the named W-hubs; all graphs are trees."""
    def tree(edges, notU):
        G = nx.Graph(edges)
        G = nx.convert_node_labels_to_integers(G, label_attribute="name")
        return G, [G.nodes[v]["name"] not in notU for v in G]
    cases = [("Q_h leaf", *tree([("w", f"q{i}") for i in range(1, 5)] + [("l", v) for v in ("q1", "r1", "r2", "z")]
                               + [("z", "t")], {"w", "l"})),
             ("u-type", *tree([("h", v) for v in ("q", "a1", "a2", "z1")] + [("z1", "t1"), ("l", "q"), ("l", "b1"),
                              ("l", "b2"), ("l", "z2"), ("z2", "t2")], {"l"}))]
    for k in (6, 7, 9):
        cases.append((f"star k={k}", *tree([("h", f"h{i}") for i in range(k)]
                                          + [(f"h{i}", f"x{i}_{j}") for i in range(k) for j in range(3)], set())))
    rng = random.Random(0)
    for name, G, U in cases:
        adj = [sorted(G[v]) for v in G]
        worst = 1e9
        for _ in range(50):
            rank = list(range(len(adj))); rng.shuffle(rank)
            m, lt, _ = charges(adj, U, rank, rho, x, info, zord)
            worst = min(worst, m[0], lt)
        print(f"regression {name:10s} min charge {worst:.6f}", flush=True)
        assert worst >= -1e-9, "NEGATIVE CHARGE"  # light hubs need only 0, rows the margin


def high_girth(rng):
    """Instances for g >= 7: random trees (infinite girth; with early vertices as hubs of high
    degree) and girth-5 planar graphs with every edge subdivided s times (girth >= 5 (s + 1))."""
    out = []
    for n, k in ((40, 1), (80, 1), (40, 4), (80, 4)):  # parent among the first i/k vertices
        G = nx.Graph()
        for i in range(1, n):
            G.add_edge(i, rng.randrange(max(1, i // k)))
        out.append(("tree" if k == 1 else "hubtree", G))
    for s in (1, 2, 5):
        G = nx.convert_node_labels_to_integers(random_planar_girth(25, 5, rng))
        H = nx.Graph()
        for u, v in G.edges():
            nx.add_path(H, [u] + [("s", u, v, i) for i in range(s)] + [v])
        out.append((f"sub{s}", H))
    return out


def main(rho="3.87", seed=1, rounds=10, iters=200):
    rng = random.Random(int(seed))
    x, info, zord = load(rho)
    rho = float(rho)
    print(f"g={r7.GIRTH} rho={rho} solution loaded", flush=True)
    regress(rho, x, info, zord)
    worst = (1e9, None)
    wlight = 1e9
    for name, G in graphs(rng) + high_girth(rng):
        G = nx.convert_node_labels_to_integers(G)
        if nx.girth(G) < r7.GIRTH:  # the Euler constant needs girth >= GIRTH
            continue
        adj = [sorted(G[v]) for v in range(G.number_of_nodes())]
        n = len(adj)
        best = (1e9, None)
        for _ in range(int(rounds)):
            p = rng.choice((0.4, 0.6, 0.8, 1.0))
            U = [rng.random() < p for _ in range(n)]
            rank = list(range(n)); rng.shuffle(rank)
            cur, lt, _ = charges(adj, U, rank, rho, x, info, zord)
            wlight = min(wlight, lt)
            for _ in range(int(iters)):
                if rng.random() < 0.5:
                    v = rng.randrange(n); U[v] = not U[v]
                    new, lt, _ = charges(adj, U, rank, rho, x, info, zord)
                    if new[0] <= cur[0]:
                        cur = new
                    else:
                        U[v] = not U[v]
                else:
                    i, j = rng.randrange(n), rng.randrange(n)
                    rank[i], rank[j] = rank[j], rank[i]
                    new, lt, _ = charges(adj, U, rank, rho, x, info, zord)
                    if new[0] <= cur[0]:
                        cur = new
                    else:
                        rank[i], rank[j] = rank[j], rank[i]
                wlight = min(wlight, lt)
            best = min(best, cur, key=lambda z: z[0])
        print(f"{name:8s} n={n:3d} min charge {best[0]:.6f} at {best[1]}", flush=True)
        worst = min(worst, (best[0], name), key=lambda z: z[0])
    print(f"overall min charge (rows) {worst[0]:.6f} ({worst[1]}); light hubs {wlight:.6f}", flush=True)
    marg = x[info["tmarg"]]
    assert worst[0] >= marg - 1e-9 and wlight >= -1e-9, "CHARGE BELOW THE CERTIFIED MARGIN"


if __name__ == "__main__":
    main(*sys.argv[1:])
