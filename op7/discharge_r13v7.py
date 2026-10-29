"""Discharging LP for rule R13 (round_exp.hubrule_r13), U-only relaxation, with U-hubs (v7).

v7 = v6f (discharge_r13z.py) with five soundness fixes.
  - The own vertex part of a heavy U-hub has no edge to its hub part, so it gets its own kinds
    own_s1, own_s2 (selects itself) and own_n. It is a member of every row of its hub part, also
    at load >= 6, and its bound carries no nu/2 there (v6f counted a half-edge that does not exist).
  - coefU: an extra heavy U-hub neighbour of a heavy U-hub is a member of its hub part, whose
    bucket-6 rows already use that half-edge in the families Z and ZU; only nu_HU/2 is free.
  - Leaf rule for Q_h vertices: a Q_h vertex may have light W-hub neighbours that its type does not
    count, so counted degree 1 means degree 1 (leaf, -1/2) or degree >= 2 (1 - c): min of both.
  - The same for Q_l vertices next to a light U-hub ("u"): min(-7/18, 1 - c + 2/9), where 2/9 are
    the returns of the light U-hub and of a light W-hub.
  - A Q_l vertex of type "n" whose Z-neighbours are all W-hubs records their exact number (1, or
    2 = >= 2) also when it has P-neighbours; v6f did so only without P-neighbours and still read
    nlh = 1 (>= 1) as a leaf of Z.

v6f = v6e plus the Euler family "HU" = G[heavy U-hubs] (planar, girth >= 5). The vertex part of a
heavy U-hub has degree KU - 1 there (exact for KU <= 5); a leaf pays nu_HU/2 to its neighbour,
an isolated vertex leaves the family. For KU = 6 (>= 6) every further heavy U-hub neighbour
adds nu_HU/2 (coefU row).

v6e = v6d with three refinements.
  - HH-types count their heavy U-hubs exactly: KU <= 5, or KU = 6 (= >= 6) only for ab = 6.
    All heavy U-hubs in N(h) are Q-neighbours of h, so KU - 1 <= a_h <= load of the selected hub.
    For KU >= 6 (a_h >= 6), each heavy U-hub neighbour beyond the fifth claims nu/2 of the hub
    part's half-edge: the hub part's row samples 4 of its >= a_h + 1 members, and the claimed
    edges (at most a_h - 5 of them, chosen to spare one selector) leave >= 6 members to sample.
  - A light U-hub in Q_h (H-type with hk = "U") gets nu/2 for each heavy W-hub neighbour: these
    edges are not among its >= 4 U-neighbour edges that its light-hub budget uses.
  - Family leaves: an H- or Z1-type of degree 1 in a family leaves it and pays nu/2 to its
    neighbour (a hub), which keeps the hub's Euler term unchanged. Removing degree-1 vertices
    keeps the family planar of girth >= 5, and sum (deg/2 - 5/3) <= 0 holds for any such graph.

v6d = v6c with selector counts: a selecting Q_h- or HH-type carries c = number of vertices that
select its selected hub (1, or 2 = >= 2). Kinds sel1/sel2/selU1/selU2; a hub row only admits
consistent multisets (exact rows: c = min(#selectors, 2); load >= 6: c = 1 means exactly one
selector in the sub-multiset).

v6c = v6b with hub loads: heavy hubs fall into load buckets 4, 5, 6 (= >= 6). Hubs of load 4 and
5 get rows over their exact member multisets (a U-hub's hub part has its own vertex part as one
more member), so the members' lower bounds M may be negative there; only bucket 6 uses
4-sub-multisets with M >= 0. Q_h- and HH-types carry ab = load bucket of their selected hub,
which (max-load selection) bounds the loads of all their heavy hubs.

v6b = v6 with smaller LP: the variants "n", "u", "U" of a Q_l-type share the F2-arc transfers
(keyed by the base type), and the B bound of an arc uses the smallest eps over the variants.

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
    part, and its row carries the whole overclaim of h and its Euler share a_h/2 - c. The vertex
    part (type 'HH' below) only has rho y_h, its HU-term and the halves of its heavy W-hub edges,
    and pays its KW + KU heavy hubs (its own hub part included) like a Q_h vertex.
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
      np = nz = 0); for "n" without fs, nh, nz, nlh is the exact number of W-hubs (2 = >= 2).
  ('H', us, ch, hk, ab, c): Q_h vertex, us over P, Qh, QlT, QlP, Z1, Hh (heavy U-hub, also one
      of its 1 + ch heavy hubs, ch = 3 = >= 3); hk = "n" or "U" (vertex part of a light U-hub, us
      over Q-slots only); ab = load bucket of the selected (or heaviest) hub; c = selector count
      of the selected hub, 0 if the vertex has a T2-neighbour.
  ('HH', KW, KU, ss, ab, c): vertex part of a heavy U-hub h. KW = heavy W-hubs in N(h) (3 = >= 3),
      KU = heavy U-hubs in N[h] (h included; 6 = >= 6 only for ab = 6), ss = h selects itself.
  ('Z', slots, nhub): Z1 vertex, slots over T, P, Qh, Ql, Z1, Hh, Hl (U-hubs, counted in nhub).
"""
import itertools
import os
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import discharge_a2 as d2
from discharge_h import LP

HORD = ("P", "Qh", "QlT", "QlP", "Z1", "Hh")
BKT = (4, 5, 6)
# Euler constant g/(g-2) of planar graphs of girth >= g (GIRTH, default 5); the light-hub
# budget row and the leaf rules hold for every constant <= 5/3
GIRTH = int(os.environ.get("GIRTH", "5"))
C53 = GIRTH / (GIRTH - 2)


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
                    # no Z-neighbour in U: the Z-degree is the number of W-hubs, kept exact
                    zl = len(fs) + nh + nz == 0
                    for nlh in ((1, 2) if zl else (1,)):
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
                for ab in BKT:
                    for c in ((0,) if "QlT" in us else (1, 2)):
                        HT.append(("H", us, ch, "n", ab, c))
                        if "P" not in us and "Z1" not in us:
                            HT.append(("H", us, ch, "U", ab, c))
    for KW in range(4):
        for KU in range(1, 7):
            for ss in (0, 1):
                if ss or KW + KU >= 2:
                    for ab in BKT:
                        if KU - 1 > (ab if ab < 6 else 6):
                            continue
                        for c in (1, 2):
                            HHT.append(("HH", KW, KU, ss, ab, c))
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


def lbase(t):
    """The Q_l-type without the hub data: F2-arcs are keyed by it."""
    return t[:5]


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
    nuHU = lp.var(0.0, 5.0)
    tmarg = lp.var(-5.0, 5.0)

    def zterms(dz, dzu, exact=True):
        """Terms of the Z-families for a vertex of degree dz in "Z" and dzu in "ZU". exact: the
        counted degree is the true degree when it is 1 (else the vertex may have uncounted light
        W-hub neighbours, and degree 1 only bounds the degree from below)."""
        leaf = -0.5 if exact else min(-0.5, 1 - C53)
        return [(nu[f], leaf if d == 1 else d / 2 - C53) for f, d in (("Z", dz), ("ZU", dzu))
                if f in zfams and d]
    m = {}
    X = {}  # transfer variables by key, for charge_check.py

    def mv(key):
        if key not in m:
            m[key] = lp.var()
        return m[key]

    def arcs(TT, ev):
        sl = {t: set(t[1]) for t in TT}
        for tu in TT:
            for tv in TT:
                slv = d2.slot_of(tv[1], tu[1], "i", False)
                slu = d2.slot_of(tu[1], tv[1], "o", False)
                if slv in sl[tv] and slu in sl[tu]:
                    k = lp.var()
                    X[("arc", tu, tv)] = k
                    lp.le([(mv((tv, slv, "A")), 1), (k, 1)], 0)
                    lp.le([(mv((tv, slv, "B")), 1), (k, 1), (ev[tu], -rho / 9)], 0)
                    lp.le([(mv((tu, slu, "A")), 1), (k, -1)], 0)
                    lp.le([(mv((tu, slu, "B")), 1), (k, -1), (ev[tv], -rho / 9)], 0)

    arcs(UT, eps)
    LB = sorted({lbase(t) for t in LT})
    ebase = {b: lp.var(0.0, 1.0) for b in LB}
    for t in LT:
        lp.le([(ebase[lbase(t)], 1), (eps[t], -1)], 0)
    arcs(LB, ebase)
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
        X[("edge", a_key, b_key)] = f
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
    kinds = ([(kd, rc) for kd in ("sel1", "sel2", "non") for rc in (0, 1)]
             + [("selU1", 0), ("selU2", 0), ("nonU", 0)])
    M = {(kd, rc, b, ver): lp.var(0.0 if b == 6 else -50.0, 50.0) for kd, rc in kinds for b in BKT for ver in "AB"}
    # the own vertex part of a heavy U-hub: always in its hub part's rows, no half-edge
    OWN = [("own_s1", 0), ("own_s2", 0), ("own_n", 0)]
    M.update({(kd, rc, b, ver): lp.var(-50.0, 50.0) for kd, rc in OWN for b in BKT for ver in "AB"})

    def mbound_own(kd, b, g, et):
        lp.le([(M[(kd, 0, b, "A")], 1), (g, -1)], 0)
        lp.le([(M[(kd, 0, b, "B")], 1), (g, -1), (et, -rho / 9)], -rho / 9)

    def mbound(kd, rc, b, g, et, eh):
        # bucket 6: the hub's Euler half nu/2 of the member edge is part of M (M >= 0 there)
        e6 = [(nu[f], -0.5) for f in zfams] if b == 6 else []
        lp.le([(M[(kd, rc, b, "A")], 1), (g, -1)] + eh + e6, 0)
        lp.le([(M[(kd, rc, b, "B")], 1), (g, -1), (et, -rho / 9)] + eh + e6, -rho / 9)
    for t in HT:
        rc = int(rich(t))
        eh = [(lam, -0.5)] if rc else []
        ab = t[4]
        if t in gs:
            mbound("sel%d" % t[5], rc, ab, gs[t], eps[t], eh)
        if t in gn:
            for b in BKT:
                if b <= ab:
                    mbound("non", rc, b, gn[t], eps[t], eh)
    hs = {t: lp.var() for t in HHT}
    hn = {t: lp.var() for t in HHT if t[1] + t[2] >= 2}
    for t in HHT:
        ab = t[4]
        if t[3]:
            mbound_own("own_s%d" % t[5], ab, hs[t], eps[t])
        else:
            mbound("selU%d" % t[5], 0, ab, hs[t], eps[t], [])
            for b in BKT:
                if b <= ab:
                    mbound_own("own_n", b, hn[t], eps[t])
        if t in hn:
            for b in BKT:
                if b <= ab:
                    mbound("nonU", 0, b, hn[t], eps[t], [])
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
            base += zterms(dz, dz + cntu["P"], exact=False)
        else:
            # light U-hub: its heavy W-hub edges are beyond the U-edges of its light-hub budget
            nWh = 1 + ch - cntu["Hh"]
            if nWh:
                base += [(nu[f], nWh / 2) for f in zfams]
        rowA = list(base) + [(mv((c, k, "A")), n) for k, n in cntu.items() if n]
        lp.ge(rowA, margin - rho / 3, ("A", t))
        if len(us) == 3:
            rowB = list(base) + [(eps[t], rho / 9)] + [(mv((c, k, "B")), n) for k, n in cntu.items() if n]
            lp.ge(rowB, margin - 2 * rho / 9, ("B", t))
        if ch == 3:
            lp.ge([(gn[t], -1), (lam, 0.5)] + [(nu[f], 0.5) for f in zfams], 0,
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
            for f, d in (("Z", dz), ("ZU", dz + np_)):
                if f not in zfams:
                    continue
                if d == 1:
                    # a leaf of the family; its one edge goes to a light hub (a W-hub, or the light
                    # U-hub of a "u"-type): leave it out, and pay 7/18 nu to the light hub. A
                    # "u"-type does not count its W-hubs: with one it has degree >= 2 and gets
                    # nu/9 from both light hubs
                    el.append((nu[f], -7 / 18 if hk == "n" else min(-7 / 18, 1 - C53 + 2 / 9)))
                else:
                    # every light hub returns nu/9 to each Q-neighbour that is not a leaf. A light
                    # hub has <= 3 Q-neighbours and degree >= 4; with k1 leaves and k2 receivers
                    # (k1 + k2 <= 3) its row k1 * 7/18 - k2/9 + (4 - k1)/2 - 5/3 >= 0 always holds.
                    el.append((nu[f], d / 2 - C53 + max(nlh, 1) / 9))
        b = lbase(t)
        lp.ge([(eps[t], -rho / 3), (tmarg, -1)] + [(mv((b, sl, "A")), k) for sl, k in cnt.items()] + extraA + el,
              inT + margin - rho / 3, ("A", t))
        if len(fs) + np_ + nh + nz == 3:
            lp.ge([(eps[t], -2 * rho / 9), (tmarg, -1)] + [(mv((b, sl, "B")), k) for sl, k in cnt.items()] + extraB + el,
                  inT + margin - 2 * rho / 9, ("B", t))
    # vertex parts of heavy U-hubs: rho y, pays hs to the selected hub and hn to the K - 1 others
    # (K = KW + KU heavy hubs in N[h]). An edge to a heavy W-hub is not among the Q-member edges
    # that the hub part's row counts, so its half nu/2 goes to the vertex part.
    for t in HHT:
        KW, KU = t[1], t[2]
        K = KW + KU
        row = [(eps[t], -rho / 3), (hs[t], -1), (tmarg, -1)] + ([(hn[t], -(K - 1))] if K >= 2 else [])
        row += [(nu[f], KW / 2) for f in zfams] if KW else []
        dH = KU - 1
        if dH:
            row.append((nuHU, -0.5 if dH == 1 else dH / 2 - C53))
        lp.ge(row, margin - rho / 3, ("HH", t))
        if KW == 3:
            lp.ge([(hn[t], -1)] + [(nu[f], 0.5) for f in zfams], 0, ("coefW", t))
        if KU == 6 and t[4] == 6:
            lp.ge([(hn[t], -1), (nuHU, 0.5)], 0, ("coefU", t))
    # heavy hub rows (W-hubs and hub parts of heavy U-hubs). Load 4, 5: exact member multisets
    # (a W-hub has a members, a U-hub's hub part a + 1, one of them its own vertex part);
    # load >= 6: 4-sub-multisets (M >= 0 there). Degree in the Z-families >= load.
    def hubrows(b, size, own):
        for ms0 in itertools.combinations_with_replacement(kinds, size):
          for ok in (OWN if own else [None]):
            ms = ms0 + ((ok,) if ok else ())
            sels = [kd for kd, rc in ms if kd.startswith("sel") or kd.startswith("own_s")]
            cs = {kd[-1] for kd in sels}
            if len(cs) > 1:
                continue
            if sels:
                c = int(cs.pop())
                if b < 6 and c != min(len(sels), 2):
                    continue
                if b == 6 and c == 1 and len(sels) != 1:
                    continue
            kept = 1.0 if sels else 0.0
            hasr = any(rc for kd, rc in ms)
            for ver, cst in (("A", 0.0), ("B", rho / 3)):
                row = [(M[(kd, rc, b, ver)], 1) for kd, rc in ms] + [(tmarg, -1)]
                if hasr:
                    row.append((lam, -1.5))
                # degree >= b for b = 4, 5; for b = 6 the sampled members carry nu/2 each in M
                row += [(nu[f], (b if b < 6 else 0) / 2 - C53) for f in zfams]
                lp.ge(row, margin + kept - cst, ("hub", b, ver, ms))
    for own in (False, True):  # W-hubs; hub parts of heavy U-hubs (own vertex part added)
        hubrows(4, 4, own)
        hubrows(5, 5, own)
        hubrows(6, 4, own)
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
    # derived variables, in dependency order: each is bounded above by rows over earlier ones
    dep = [list(ebase.values()) + list(emin.values()), list(m.values()) + list(M.values())]
    return lp, dict(eps=eps, lam=lam, tmarg=tmarg, nu=dict(nu, HU=nuHU), dep=dep,
                    X=X, gs=gs, gn=gn, hs=hs, hn=hn)


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
