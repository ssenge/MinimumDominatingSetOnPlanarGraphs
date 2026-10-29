"""Discharging LP for rule R12 (round_exp.hubrule_r12), U-only relaxation, no hubs inside U (v4b).

v4b adds Z1 rows (charge 0, they only receive) and Euler families through Z1 and the light hubs:
  "Z":  vertices Z = Q + Z1 and all W-hubs, edges inside Z and between Z and the hubs;
  "ZU": the same plus U' and the edges of U with an endpoint in U'.
Every U-neighbour of a hub lies in Z, so every hub has degree >= 4 in both and needs no row.
A Q_l vertex has >= 1 (light) hub since Q_l is inside Z; the rows use that lower bound.

R12: H = vertices outside U with >= 4 neighbours in U (H_U assumed empty), Z = U n N(H),
U' = U minus Z, T = idrule(G[U']), P = U' minus T, Q = Z minus N(T), Z1 = Z n N(T).
a_w = |N(w) n Q|; heavy hubs: a_w >= 4. Q_h = vertices of Q with a heavy hub: each selects a heavy hub
of maximum load. Q_l = Q minus Q_h: T2 = idrule(G[Q_l]) (subcubic). D' = T + selected + T2.
Claim: |D'| <= rho LP_U.

Dual y = (1 - eps)/3 on U, eps = 1 on Z1. Light hubs (a_w <= 3) have Y(w) <= 1 and cost nothing.
Euler term lam (deg_B/2 - 3/2) on B = edges between rich q (>= 3 heavy hubs) and heavy hubs.
Types:
  ('U', fs, nh, nl, nz): vertex of U' with F-skeleton fs and nh, nl, nz neighbours in Q_h, Q_l, Z1.
  ('H', us, ch): vertex of Q_h with U-slots us over P, Qh, Ql, Z1 and ch further heavy hubs (3 = >= 3).
  ('L', fs2, np, nh, nz): vertex of Q_l with skeleton fs2 in G[Q_l] and np, nh, nz neighbours in
  P, Q_h, Z1.
Transfers: F-arcs and F2-arcs between full types; edges P-Q, Qh-Qh, Qh-Ql by classes.
"""
import itertools
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import discharge_a2 as d2
from discharge_h import LP


def types():
    UT, HT, LT = [], [], []
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
                    LT.append(("L", fs, np_, nh, nz))
    for k in range(4):
        for us in itertools.combinations_with_replacement(("P", "Qh", "Ql", "Z1"), k):
            for ch in range(4):
                HT.append(("H", us, ch))
    ZT = []
    for k in range(3):
        for rest in itertools.combinations_with_replacement(("T", "P", "Qh", "Ql", "Z1"), k):
            for nhub in (1, 2, 3):
                ZT.append(("Z", tuple(sorted(("T",) + rest)), nhub))
    return UT, HT, LT, ZT


def hcls(t):
    return ("H", t[1])


def lcls(t):
    return ("L", d2.cls(t[1]), len(t[1]), t[2], t[3], t[4])


def rich(t):
    return 1 + t[2] >= 3


# Euler families on subgraphs with c = 5/3 (girth 5): which vertex classes are in, and whether the
# Q_h - heavy hub edges are in. Z1 is never in (it has no rows).
FAMS = {"Ua": (1, 1, 1, 0), "Ub": (1, 1, 1, 1), "Qc": (0, 1, 1, 1), "Qd": (0, 1, 1, 0)}


ZFAMS = ("Z", "ZU")


def build(rho, margin=0.0, fams=tuple(FAMS), zfams=ZFAMS):
    lp = LP()
    UT, HT, LT, ZT = types()
    eps = {t: lp.var(0.0, 1.0) for t in UT + HT + LT}
    lam = lp.var(0.0, 5.0)
    nu = {f: lp.var(0.0, 5.0) for f in tuple(fams) + tuple(zfams)}
    tmarg = lp.var(-5.0, 5.0)
    C53 = 5 / 3

    def fam_terms(deg_of):
        """deg_of(f) -> degree of the vertex in family f (None if the vertex is not in f)."""
        out = []
        for f in fams:
            d = deg_of(FAMS[f])
            if d:
                out.append((nu[f], d / 2 - C53))
        return out

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
    emin = {c: lp.var(0.0, 1.0) for c in HC + LC}
    for t in HT:
        lp.le([(emin[hcls(t)], 1), (eps[t], -1)], 0)
    for t in LT:
        lp.le([(emin[lcls(t)], 1), (eps[t], -1)], 0)

    def edge(a_key, b_key, ea, eb):
        """Edge between slot a_key (endpoint a) and slot b_key (endpoint b); flow f from b to a.
        ea, eb: (var, coef) giving rho/9 * eps of the endpoint (for the other side's B bound)."""
        f = lp.var()
        lp.le([(mv(a_key + ("A",)), 1), (f, -1)], 0)
        lp.le([(mv(a_key + ("B",)), 1), (f, -1), (eb, -rho / 9)], 0)
        lp.le([(mv(b_key + ("A",)), 1), (f, 1)], 0)
        lp.le([(mv(b_key + ("B",)), 1), (f, 1), (ea, -rho / 9)], 0)

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
        lp.le([(mv((a, "Qh", "A")), 1)], 0)
        lp.le([(mv((a, "Qh", "B")), 1), (emin[a], -rho / 9)], 0)
        for b in hq[i + 1:]:
            edge((a, "Qh"), (b, "Qh"), emin[a], emin[b])
    # Q_h - Q_l by classes
    for a in HC:
        if "Ql" not in a[1]:
            continue
        for b in LC:
            if b[4] >= 1:
                edge((a, "Ql"), (b, "Qh"), emin[a], emin[b])
    # flows into Z1 (Z1 has y = 0, so the B bounds of the sender equal the A bounds)
    def zflow(a_key, z_key):
        f = lp.var()
        lp.le([(mv(a_key + ("A",)), 1), (f, 1)], 0)
        lp.le([(mv(a_key + ("B",)), 1), (f, 1)], 0)
        lp.le([(mv(z_key + ("A",)), 1), (f, -1)], 0)
    for tz in ZT:
        sl = set(tz[1])
        for tp in UT:
            if tp[4] and ("T" if d2.cls(tp[1]) != "P" else "P") in sl:
                zflow((tp, "Z1"), (tz, "T" if d2.cls(tp[1]) != "P" else "P"))
        if "Qh" in sl:
            for c in HC:
                if "Z1" in c[1]:
                    zflow((c, "Z1"), (tz, "Qh"))
        if "Ql" in sl:
            for c in LC:
                if c[5] >= 1:
                    zflow((c, "Z1"), (tz, "Ql"))
    # hub transfers and hub-side bounds
    gs = {t: lp.var() for t in HT}
    gn = {t: lp.var() for t in HT if t[2]}
    M = {(kd, rc, ver): lp.var(0.0, 50.0) for kd in ("sel", "non") for rc in (0, 1) for ver in "AB"}
    for t in HT:
        rc = int(rich(t))
        eh = [(lam, -0.5)] if rc else []
        for kd, g in (("sel", gs[t]),) + ((("non", gn[t]),) if t in gn else ()):
            lp.le([(M[(kd, rc, "A")], 1), (g, -1)] + eh, 0)
            lp.le([(M[(kd, rc, "B")], 1), (g, -1), (eps[t], -rho / 9)] + eh, -rho / 9)
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
        eu = fam_terms(lambda F: F[0] * (len(fs) + F[1] * nh + F[2] * nl))
        eu += zterms(0, len(fs) + nh + nl + nz)
        lp.ge([(eps[t], -rho / 3), (tmarg, -1)] + [(mv((t, sl, "A")), c) for sl, c in cnt.items()] + extraA + eu,
              inT + margin - rho / 3, ("A", t))
        if len(fs) + nh + nl + nz == 3:
            lp.ge([(eps[t], -2 * rho / 9), (tmarg, -1)] + [(mv((t, sl, "B")), c) for sl, c in cnt.items()] + extraB + eu,
                  inT + margin - 2 * rho / 9 - nz * rho / 9, ("B", t))
    # Q_h rows
    for t in HT:
        us, ch = t[1], t[2]
        c = hcls(t)
        base = [(eps[t], -rho / 3), (gs[t], -1), (tmarg, -1)]
        if ch:
            base.append((gn[t], -ch))
        if rich(t):
            base.append((lam, (1 + ch) / 2 - 1.5))
        cntu = {k: us.count(k) for k in ("P", "Qh", "Ql")}
        base += fam_terms(lambda F: F[1] * (F[0] * cntu["P"] + cntu["Qh"] + F[2] * cntu["Ql"] + F[3] * (1 + ch)))
        nz1 = us.count("Z1")
        dz = cntu["Qh"] + cntu["Ql"] + nz1 + 1 + ch
        base += zterms(dz, dz + cntu["P"])
        if nz1:
            cntu["Z1"] = nz1
        rowA = list(base) + [(mv((c, k, "A")), n) for k, n in cntu.items() if n]
        lp.ge(rowA, margin - rho / 3, ("A", t))
        if len(us) == 3:
            rowB = list(base) + [(eps[t], rho / 9)] + [(mv((c, k, "B")), n) for k, n in cntu.items() if n]
            lp.ge(rowB, margin - 2 * rho / 9 - us.count("Z1") * rho / 9, ("B", t))
        if ch == 3:
            lp.ge([(gn[t], -1), (lam, 0.5)] + [(nu[f], 0.5) for f in fams if FAMS[f][3]]
                  + [(nu[f], 0.5) for f in zfams], 0, ("coef", t))
    # Q_l rows
    for t in LT:
        fs, np_, nh, nz = t[1:]
        nlh = 1  # Q_l lies in Z without heavy hubs, so it has >= 1 light hub
        c = lcls(t)
        inT = 0.0 if d2.cls(fs) == "P" else 1.0
        cnt = {}
        for sl in fs:
            cnt[sl] = cnt.get(sl, 0) + 1
        extraA = ([(mv((c, "P", "A")), np_)] if np_ else []) + ([(mv((c, "Qh", "A")), nh)] if nh else [])
        extraB = ([(mv((c, "P", "B")), np_)] if np_ else []) + ([(mv((c, "Qh", "B")), nh)] if nh else [])
        if nz:
            extraA.append((mv((c, "Z1", "A")), nz)); extraB.append((mv((c, "Z1", "B")), nz))
        el = fam_terms(lambda F: F[2] * (F[0] * np_ + F[1] * nh + len(fs)))
        dz = len(fs) + nh + nz + nlh
        el += zterms(dz, dz + np_)
        lp.ge([(eps[t], -rho / 3), (tmarg, -1)] + [(mv((t, sl, "A")), k) for sl, k in cnt.items()] + extraA + el,
              inT + margin - rho / 3, ("A", t))
        if len(fs) + np_ + nh + nz == 3:
            lp.ge([(eps[t], -2 * rho / 9), (tmarg, -1)] + [(mv((t, sl, "B")), k) for sl, k in cnt.items()] + extraB + el,
                  inT + margin - 2 * rho / 9 - nz * rho / 9, ("B", t))
    # heavy hub rows: 4-multisets over Q-kinds
    kinds = [(kd, rc) for kd in ("sel", "non") for rc in (0, 1)]
    for ms in itertools.combinations_with_replacement(kinds, 4):
        kept = 1.0 if any(kd == "sel" for kd, rc in ms) else 0.0
        hasr = any(rc for kd, rc in ms)
        for ver, cst in (("A", 0.0), ("B", rho / 3)):
            row = [(M[(kd, rc, ver)], 1) for kd, rc in ms] + [(tmarg, -1)]
            if hasr:
                row.append((lam, -1.5))
            row += [(nu[f], 4 / 2 - C53) for f in tuple(f for f in fams if FAMS[f][3]) + tuple(zfams)]
            lp.ge(row, margin + kept - cst, ("hub", ver, ms))
    # Z1 rows: charge 0, receive from U', Q_h, Q_l neighbours, pay the Euler terms
    for tz in ZT:
        sl, nhub = tz[1], tz[2]
        cnt = {k: sl.count(k) for k in ("T", "P", "Qh", "Ql")}
        dz = nhub + sl.count("Qh") + sl.count("Ql") + sl.count("Z1")
        row = [(mv((tz, k, "A")), n) for k, n in cnt.items() if n] + [(tmarg, -1)]
        row += zterms(dz, dz + cnt["T"] + cnt["P"])
        lp.ge(row, margin, ("Z", tz))
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
