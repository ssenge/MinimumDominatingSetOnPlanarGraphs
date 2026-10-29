"""Discharging LP for rule R13 (round_exp.hubrule_r13), U-only relaxation, with U-hubs (v6).

R13: H = vertices with >= 4 neighbours in U (W-hubs outside U, U-hubs H_U inside U),
U' = U minus N[H], T = idrule(G[U']), P = U' minus T, Z = U minus U', Q = Z minus N(T) (contains
H_U), Z1 = Z n N(T). a_w = |N(w) n Q| for hubs, heavy: a_w >= 4. Q_h = vertices of Q with a heavy
hub in the closed neighbourhood, Q_l = Q minus Q_h, T2 = idrule(G[Q_l]) (subcubic). A vertex of
Q_h without a T2-neighbour selects a heavy hub of maximum load in its closed neighbourhood.
D' = T + T2 + selected hubs. Claim: |D'| <= rho LP_U.

Dual y = (1 - eps)/3 on U. Charge of v: rho y_v - (rho/3)(Y(v) - 1)^+ - [v in D'] + transfers
+ Euler terms; the claim follows if every row below is >= 0.

U-hubs are split into a vertex part and a hub part.
  - Heavy U-hub h: the hub part is a heavy hub whose Q-neighbours are N(h) n Q plus the vertex
    part, and its row carries the whole overclaim of h and the Euler term of h. The vertex part
    (type ('HH', K, ss), K = number of heavy hubs in N[h], 4 = >= 4, ss = selects itself) only
    has rho y_h and pays its K heavy hubs like a Q_h vertex.
  - Light U-hub h (<= 3 Q-neighbours): the vertex part is an ordinary Q_h- or Q_l-type over its
    Q-neighbours (flag "U"), with its own overclaim over them but without Euler terms. Its
    Z1-neighbours pay their own share of Y(h). The Euler term of h (degree >= 4) is its
    light-hub budget, as for a light W-hub.
Light hubs (W or U): every Z1-neighbour pays rho/3 y to each of its hubs, which covers the
overclaim beyond the <= 3 Q-neighbours. Euler budget (families "Z", "ZU", c = 5/3): degree >= 4;
an isolated Q_l vertex with one light hub leaves the families and pays 7/18 nu to the hub; the hub
returns nu/9 to every other Q_l-neighbour (all mixes of <= 3 Q-neighbours checked).
Families: "Z" = Z and all hubs, edges inside Z and from Z to hubs; "ZU" adds U' and its edges.
lam (deg_B/2 - 3/2): B = edges between rich Q_h vertices (>= 3 heavy hubs, not heavy hubs
themselves) and heavy hubs; bipartite, so girth >= 6.

Types:
  ('U', fs, nh, nl, nz): U' vertex (never next to a U-hub).
  ('L', fs2, np, nh, nz, nlh, hk): Q_l vertex. hk = "n" (no U-hub neighbour, >= nlh W-hubs),
      "u" (a light U-hub among its Q-neighbours, >= 0 W-hubs), "U" (vertex part of a light U-hub,
      np = nz = 0).
  ('H', us, ch, hk): Q_h vertex, us over P, Qh, QlT, QlP, Z1, Hh (heavy U-hub, also one of its
      1 + ch heavy hubs); hk = "n" or "U" (vertex part of a light U-hub, us over Q-slots only).
  ('HH', K, ss): vertex part of a heavy U-hub.
  ('Z', slots, nhub): Z1 vertex, slots over T, P, Qh, Ql, Z1, Hh, Hl (U-hubs, counted in nhub).
"""
import itertools
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import discharge_a2 as d2
from discharge_h import LP

HORD = ("P", "Qh", "QlT", "QlP", "Z1", "Hh")
C53 = 5 / 3


def types():
    UT, HT, LT, HHT, ZT = [], [], [], [], []
    for fs in d2.all_types(False):
        c = d2.cls(fs)
        r = 3 - len(fs)
        for nh in range(r + 1):
            for nl in range(r + 1 - nh):
                for nz in range(r + 1 - nh - nl):
                    if (nh or nl) and c != "P":
                        continue
                    UT.append(("U", fs, nh, nl, nz))
    for fs in d2.all_types(False):
        r = 3 - len(fs)
        for np_ in range(r + 1):
            for nh in range(r + 1 - np_):
                for nz in range(r + 1 - np_ - nh):
                    iso = len(fs) + np_ + nh + nz == 0
                    for nlh in ((1, 2) if iso else (1,)):
                        LT.append(("L", fs, np_, nh, nz, nlh, "n"))
                    if len(fs) + nh:
                        LT.append(("L", fs, np_, nh, nz, 1, "u"))
                    if np_ == 0 and nz == 0:
                        LT.append(("L", fs, 0, nh, 0, 1, "U"))
    for k in range(4):
        for us in itertools.combinations_with_replacement(HORD, k):
            for ch in range(4):
                if us.count("Hh") > 1 + ch:
                    continue
                HT.append(("H", us, ch, "n"))
                if "P" not in us and "Z1" not in us:
                    HT.append(("H", us, ch, "U"))
    for K in (1, 2, 3, 4):
        for ss in (0, 1):
            if ss or K >= 2:
                HHT.append(("HH", K, ss))
    for k in range(3):
        for rest in itertools.combinations_with_replacement(("T", "P", "Qh", "Ql", "Z1", "Hh", "Hl"), k):
            sl = tuple(sorted(("T",) + rest))
            nU = sl.count("Hh") + sl.count("Hl")
            for nhub in (1, 2, 3):
                if nhub >= min(nU, 3) and nhub >= 1:
                    ZT.append(("Z", sl, nhub))
    return UT, HT, LT, HHT, ZT


def hcls(t):
    return ("H", t[1])


def lcls(t):
    return ("L", d2.cls(t[1]), len(t[1]), t[2], t[3], t[4])


def dom(t):
    """A Q_h vertex with a neighbour in T2: it does not select."""
    return "QlT" in t[1]


def rich(t):
    return 1 + t[2] >= 3


ZFAMS = ("Z", "ZU")


def build(rho, margin=0.0, zfams=ZFAMS):
    lp = LP()
    UT, HT, LT, HHT, ZT = types()
    eps = {t: lp.var(0.0, 1.0) for t in UT + HT + LT + HHT + ZT}
    lam = lp.var(0.0, 5.0)
    nu = {f: lp.var(0.0, 5.0) for f in zfams}
    tmarg = lp.var(-5.0, 5.0)

    def zterms(dz, dzu):
        """Terms of the Z-families for a vertex of degree dz in "Z" and dzu in "ZU"."""
        return [(nu[f], d / 2 - C53) for f, d in (("Z", dz), ("ZU", dzu)) if f in zfams and d]
    m = {}

    def mv(key):
        if key not in m:
            m[key] = lp.var()
        return m[key]

    def arcs(TT):
        sl = {t: set(t[1]) for t in TT}
        for tu in TT:
            for tv in TT:
                slv = d2.slot_of(tv[1], tu[1], "i", False)
                slu = d2.slot_of(tu[1], tv[1], "o", False)
                if slv in sl[tv] and slu in sl[tu]:
                    k = lp.var()
                    lp.le([(mv((tv, slv, "A")), 1), (k, 1)], 0)
                    lp.le([(mv((tv, slv, "B")), 1), (k, 1), (eps[tu], -rho / 9)], 0)
                    lp.le([(mv((tu, slu, "A")), 1), (k, -1)], 0)
                    lp.le([(mv((tu, slu, "B")), 1), (k, -1), (eps[tv], -rho / 9)], 0)

    arcs(UT)
    arcs(LT)
    HC = sorted({hcls(t) for t in HT})
    LC = sorted({lcls(t) for t in LT})
    emin = {c: lp.var(0.0, 1.0) for c in HC + LC + ["HH", "Hl"]}
    for t in HT:
        lp.le([(emin[hcls(t)], 1), (eps[t], -1)], 0)
        if t[3] == "U":
            lp.le([(emin["Hl"], 1), (eps[t], -1)], 0)
    for t in LT:
        lp.le([(emin[lcls(t)], 1), (eps[t], -1)], 0)
        if t[6] == "U":
            lp.le([(emin["Hl"], 1), (eps[t], -1)], 0)
    for t in HHT:
        lp.le([(emin["HH"], 1), (eps[t], -1)], 0)

    def edge(a_key, b_key, ea, eb):
        """Edge between slot a_key (endpoint a) and slot b_key (endpoint b); flow f from b to a.
        ea, eb: eps variables of the endpoints (for the other side's B bound)."""
        f = lp.var()
        lp.le([(mv(a_key + ("A",)), 1), (f, -1)], 0)
        lp.le([(mv(a_key + ("B",)), 1), (f, -1), (eb, -rho / 9)], 0)
        lp.le([(mv(b_key + ("A",)), 1), (f, 1)], 0)
        lp.le([(mv(b_key + ("B",)), 1), (f, 1), (ea, -rho / 9)], 0)

    def noflow(key, e):
        """A slot without transfers; the neighbour's eps is at least e (for the B bound)."""
        lp.le([(mv(key + ("A",)), 1)], 0)
        lp.le([(mv(key + ("B",)), 1), (e, -rho / 9)], 0)

    # P (U') - Q_h and P - Q_l edges, by (full U'-type, Q-class)
    for tp in UT:
        if tp[2]:
            for c in HC:
                if "P" in c[1]:
                    edge((tp, "Qh"), (c, "P"), eps[tp], emin[c])
        if tp[3]:
            for c in LC:
                if c[3] >= 1:
                    edge((tp, "Ql"), (c, "P"), eps[tp], emin[c])
    # Q_h - Q_h by classes
    hq = [c for c in HC if "Qh" in c[1]]
    for i, a in enumerate(hq):
        noflow((a, "Qh"), emin[a])
        for b in hq[i + 1:]:
            edge((a, "Qh"), (b, "Qh"), emin[a], emin[b])
    # Q_h - Q_l by classes
    for a in HC:
        for k in ("QlT", "QlP"):
            if k not in a[1]:
                continue
            for b in LC:
                if b[4] >= 1 and (b[1] != "P") == (k == "QlT"):
                    edge((a, k), (b, "Qh"), emin[a], emin[b])
    # Q_h - heavy U-hub: no transfers
    for a in HC:
        if "Hh" in a[1]:
            noflow((a, "Hh"), emin["HH"])
    # edges at Z1 (full Z1-types on one side)
    for tz in ZT:
        sl = set(tz[1])
        for tp in UT:
            k = "T" if d2.cls(tp[1]) != "P" else "P"
            if tp[4] and k in sl:
                edge((tz, k), (tp, "Z1"), eps[tz], eps[tp])
        if "Qh" in sl:
            for c in HC:
                if "Z1" in c[1]:
                    edge((tz, "Qh"), (c, "Z1"), eps[tz], emin[c])
        if "Ql" in sl:
            for c in LC:
                if c[5] >= 1:
                    edge((tz, "Ql"), (c, "Z1"), eps[tz], emin[c])
        if "Hh" in sl:
            noflow((tz, "Hh"), emin["HH"])
        if "Hl" in sl:
            noflow((tz, "Hl"), emin["Hl"])
    zz = [t for t in ZT if "Z1" in t[1]]
    for i, a in enumerate(zz):
        noflow((a, "Z1"), eps[a])
        for b in zz[i + 1:]:
            edge((a, "Z1"), (b, "Z1"), eps[a], eps[b])
    # payments to heavy hubs and the hub-side lower bounds M (kinds sel/non x rich, selU/nonU)
    gs = {t: lp.var() for t in HT if not dom(t)}
    gn = {t: lp.var() for t in HT if t[2] or dom(t)}
    kinds = [(kd, rc) for kd in ("sel", "non") for rc in (0, 1)] + [("selU", 0), ("nonU", 0)]
    M = {(kd, rc, ver): lp.var(0.0, 50.0) for kd, rc in kinds for ver in "AB"}
    for t in HT:
        rc = int(rich(t))
        eh = [(lam, -0.5)] if rc else []
        for kd, g in ((("sel", gs[t]),) if t in gs else ()) + ((("non", gn[t]),) if t in gn else ()):
            lp.le([(M[(kd, rc, "A")], 1), (g, -1)] + eh, 0)
            lp.le([(M[(kd, rc, "B")], 1), (g, -1), (eps[t], -rho / 9)] + eh, -rho / 9)
    hs = {t: lp.var() for t in HHT}
    hn = {t: lp.var() for t in HHT if t[1] >= 2}
    for t in HHT:
        for kd, g in (("selU", hs[t]),) + ((("nonU", hn[t]),) if t in hn else ()):
            lp.le([(M[(kd, 0, "A")], 1), (g, -1)], 0)
            lp.le([(M[(kd, 0, "B")], 1), (g, -1), (eps[t], -rho / 9)], -rho / 9)
    # U' rows
    for t in UT:
        fs, nh, nl, nz = t[1:]
        inT = 0.0 if d2.cls(fs) == "P" else 1.0
        cnt = {}
        for sl in fs:
            cnt[sl] = cnt.get(sl, 0) + 1
        extraA = ([(mv((t, "Qh", "A")), nh)] if nh else []) + ([(mv((t, "Ql", "A")), nl)] if nl else [])
        extraB = ([(mv((t, "Qh", "B")), nh)] if nh else []) + ([(mv((t, "Ql", "B")), nl)] if nl else [])
        if nz:
            extraA.append((mv((t, "Z1", "A")), nz)); extraB.append((mv((t, "Z1", "B")), nz))
        eu = zterms(0, len(fs) + nh + nl + nz)
        lp.ge([(eps[t], -rho / 3), (tmarg, -1)] + [(mv((t, sl, "A")), c) for sl, c in cnt.items()] + extraA + eu,
              inT + margin - rho / 3, ("A", t))
        if len(fs) + nh + nl + nz == 3:
            lp.ge([(eps[t], -2 * rho / 9), (tmarg, -1)] + [(mv((t, sl, "B")), c) for sl, c in cnt.items()] + extraB + eu,
                  inT + margin - 2 * rho / 9, ("B", t))
    # Q_h rows
    for t in HT:
        us, ch, hk = t[1], t[2], t[3]
        c = hcls(t)
        base = [(eps[t], -rho / 3), (tmarg, -1)] + ([(gs[t], -1)] if t in gs else [])
        if t in gn:
            base.append((gn[t], -(ch + int(dom(t)))))
        if rich(t):
            base.append((lam, (1 + ch) / 2 - 1.5))
        cntu = {k: us.count(k) for k in HORD}
        if hk == "n":
            # heavy U-hub neighbours are counted among the 1 + ch heavy hubs, not as U-slots
            dz = cntu["Qh"] + cntu["QlT"] + cntu["QlP"] + cntu["Z1"] + 1 + ch
            base += zterms(dz, dz + cntu["P"])
        rowA = list(base) + [(mv((c, k, "A")), n) for k, n in cntu.items() if n]
        lp.ge(rowA, margin - rho / 3, ("A", t))
        if len(us) == 3:
            rowB = list(base) + [(eps[t], rho / 9)] + [(mv((c, k, "B")), n) for k, n in cntu.items() if n]
            lp.ge(rowB, margin - 2 * rho / 9, ("B", t))
        if ch == 3:
            lp.ge([(gn[t], -1), (lam, 0.5)] + ([(nu[f], 0.5) for f in zfams] if hk == "n" else []), 0,
                  ("coef", t))
    # Q_l rows
    for t in LT:
        fs, np_, nh, nz, nlh, hk = t[1:]
        c = lcls(t)
        inT = 0.0 if d2.cls(fs) == "P" else 1.0
        cnt = {}
        for sl in fs:
            cnt[sl] = cnt.get(sl, 0) + 1
        extraA = ([(mv((c, "P", "A")), np_)] if np_ else []) + ([(mv((c, "Qh", "A")), nh)] if nh else [])
        extraB = ([(mv((c, "P", "B")), np_)] if np_ else []) + ([(mv((c, "Qh", "B")), nh)] if nh else [])
        if nz:
            extraA.append((mv((c, "Z1", "A")), nz)); extraB.append((mv((c, "Z1", "B")), nz))
        el = []
        if hk != "U":
            nW = nlh if hk == "n" else 0  # lower bound on the number of W-hubs
            dz = len(fs) + nh + nz + nW
            if dz == 1 and hk == "n" and not (len(fs) + nh + nz + np_):
                # a leaf of the Z-families: leave it and its hub edge out, and pay 7/18 nu to the light hub
                el = [(nu[f], -7 / 18) for f in zfams]
            else:
                # every light hub returns nu/9 to each Q-neighbour that is not a leaf. A light hub has
                # <= 3 Q-neighbours and degree >= 4; with k1 leaves and k2 receivers (k1 + k2 <= 3)
                # its row k1 * 7/18 - k2/9 + (4 - k1)/2 - 5/3 >= 0 holds in all cases.
                el = zterms(dz, dz + np_) + [(nu[f], max(nlh, 1) / 9) for f in zfams]
        lp.ge([(eps[t], -rho / 3), (tmarg, -1)] + [(mv((t, sl, "A")), k) for sl, k in cnt.items()] + extraA + el,
              inT + margin - rho / 3, ("A", t))
        if len(fs) + np_ + nh + nz == 3:
            lp.ge([(eps[t], -2 * rho / 9), (tmarg, -1)] + [(mv((t, sl, "B")), k) for sl, k in cnt.items()] + extraB + el,
                  inT + margin - 2 * rho / 9, ("B", t))
    # vertex parts of heavy U-hubs: rho y, pays hs to the selected hub and hn to the K - 1 others
    for t in HHT:
        K = t[1]
        row = [(eps[t], -rho / 3), (hs[t], -1), (tmarg, -1)] + ([(hn[t], -(K - 1))] if K >= 2 else [])
        lp.ge(row, margin - rho / 3, ("HH", t))
        if K == 4:
            lp.ge([(hn[t], -1)], 0, ("coef", t))
    # heavy hub rows (W-hubs and hub parts of heavy U-hubs): 4-multisets over the kinds
    for ms in itertools.combinations_with_replacement(kinds, 4):
        kept = 1.0 if any(kd in ("sel", "selU") for kd, rc in ms) else 0.0
        hasr = any(rc for kd, rc in ms)
        for ver, cst in (("A", 0.0), ("B", rho / 3)):
            row = [(M[(kd, rc, ver)], 1) for kd, rc in ms] + [(tmarg, -1)]
            if hasr:
                row.append((lam, -1.5))
            row += [(nu[f], 4 / 2 - C53) for f in zfams]
            lp.ge(row, margin + kept - cst, ("hub", ver, ms))
    # Z1 rows: charge rho y - overclaim - nhub rho/3 y, transfers, Euler terms
    for tz in ZT:
        sl, nhub = tz[1], tz[2]
        cnt = {k: sl.count(k) for k in ("T", "P", "Qh", "Ql", "Z1", "Hh", "Hl")}
        dz = nhub + cnt["Qh"] + cnt["Ql"] + cnt["Z1"]
        eu = zterms(dz, dz + cnt["T"] + cnt["P"]) + [(tmarg, -1)]
        pay = nhub * rho / 9
        lp.ge([(eps[tz], -rho / 3 + pay)] + [(mv((tz, k, "A")), n) for k, n in cnt.items() if n] + eu,
              margin - rho / 3 + pay, ("A", tz))
        if len(sl) == 3:
            lp.ge([(eps[tz], -2 * rho / 9 + pay)] + [(mv((tz, k, "B")), n) for k, n in cnt.items() if n] + eu,
                  margin - 2 * rho / 9 + pay, ("B", tz))
        if nhub == 3:
            lp.ge([(eps[tz], rho / 9)] + [(nu[f], 0.5) for f in zfams], rho / 9, ("coef", tz))
    return lp, dict(eps=eps, lam=lam, tmarg=tmarg, nu=nu)


def solve(rho, margin=0.0, verbose=True):
    lp, info = build(rho, margin)
    A = coo_matrix((lp.v, (lp.r, lp.c)), shape=(lp.nr, lp.nv)).tocsr()
    cobj = np.zeros(lp.nv); cobj[info["tmarg"]] = -1.0
    res = linprog(cobj, A_ub=A, b_ub=np.array(lp.b), bounds=list(zip(lp.lo, lp.hi)), method="highs")
    if verbose:
        ex = ""
        if res.status == 0:
            ex = f" lam={res.x[info['lam']]:.4f} " + " ".join(f"{f}={res.x[v]:.4f}" for f, v in info["nu"].items())
        print(f"rho={rho:.5f} vars={lp.nv} rows={lp.nr} status={res.status} max margin="
              f"{-res.fun if res.status == 0 else None}" + ex, flush=True)
    return res, lp, info


def build_for_diag(rho):
    lp, info = build(rho)
    return lp, None, None, info["tmarg"]


if __name__ == "__main__":
    for rho in map(float, sys.argv[1:] or ["3.25"]):
        solve(rho)
