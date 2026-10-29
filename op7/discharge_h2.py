"""Discharging LP for the max-load selection hub rule, U-only relaxation, no hubs inside U (v2).

Rule: H = vertices outside U with >= 4 neighbours in U, Z = U n N(H), U' = U minus Z, F = G[U'],
T = idrule(F), P = U' minus T, Q = Z minus N(T), Z1 = Z n N(T). For a hub w let a_w = |N(w) n Q|.
Every q in Q selects a hub neighbour with the largest a_w. D' = T + selected hubs.
Claim: |D'| <= rho LP_U.

Dual y = (1 - eps)/3 on U with eps = 1 on Z1. A hub with a_w <= 3 has Y(w) <= 1 (no overclaim).
Hub buckets: a = 1, 2, 3 (light) and 4 (= a_w >= 4, heavy). A q is rich if it has >= 3 heavy hubs.
Euler term lam (deg_B(v)/2 - 3/2) on B = edges between rich q and heavy hubs (bipartite, girth >= 6).
Q-type ('Q', us, asel, cl, ch): us = sorted U-slots over P, Q, Z1; asel = bucket of the selected hub;
cl, ch = numbers of non-selected light and heavy hubs (3 stands for >= 3, with a nonnegative marginal
coefficient). Transfers P-Q depend on (P-type, Q-class), Q-Q on the classes, Q-class = (us, asel).
"""
import itertools
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import discharge_a2 as d2
from discharge_h import LP, utypes


def qtypes():
    out = []
    for k in range(4):
        for us in itertools.combinations_with_replacement(("P", "Q", "Z1"), k):
            for asel in (1, 2, 3, 4):
                for cl in range(4):
                    for ch in (range(4) if asel == 4 else (0,)):
                        out.append(("Q", us, asel, cl, ch))
    return out


def rich(t):
    return t[2] == 4 and 1 + t[4] >= 3


def qcls(t):
    return (t[1], t[2])


def build(rho, margin=0.0):
    lp = LP()
    UT, QT = utypes(), qtypes()
    eps = {t: lp.var(0.0, 1.0) for t in UT + QT}
    lam = lp.var(0.0, 5.0)
    tmarg = lp.var(-5.0, 5.0)
    m = {}

    def mv(key):
        if key not in m:
            m[key] = lp.var()
        return m[key]

    # F arcs
    fs_slots = {t: set(t[1]) for t in UT}
    for tu in UT:
        for tv in UT:
            slv = d2.slot_of(tv[1], tu[1], "i", False)
            slu = d2.slot_of(tu[1], tv[1], "o", False)
            if slv in fs_slots[tv] and slu in fs_slots[tu]:
                k = lp.var()
                lp.le([(mv((tv, slv, "A")), 1), (k, 1)], 0)
                lp.le([(mv((tv, slv, "B")), 1), (k, 1), (eps[tu], -rho / 9)], 0)
                lp.le([(mv((tu, slu, "A")), 1), (k, -1)], 0)
                lp.le([(mv((tu, slu, "B")), 1), (k, -1), (eps[tv], -rho / 9)], 0)
    classes = sorted({qcls(t) for t in QT})
    emin = {c: lp.var(0.0, 1.0) for c in classes}
    for t in QT:
        lp.le([(emin[qcls(t)], 1), (eps[t], -1)], 0)
    # P-Q edges: f(tp, c) = amount a q of class c sends to p
    PQ = [t for t in UT if t[2] > 0]
    for c in classes:
        if "P" not in c[0]:
            continue
        for tp in PQ:
            f = lp.var()
            lp.le([(mv((tp, "Q", "A")), 1), (f, -1)], 0)
            lp.le([(mv((tp, "Q", "B")), 1), (f, -1), (emin[c], -rho / 9)], 0)
            lp.le([(mv((c, "P", "A")), 1), (f, 1)], 0)
            lp.le([(mv((c, "P", "B")), 1), (f, 1), (eps[tp], -rho / 9)], 0)
    # Q-Q edges between classes
    qc = [c for c in classes if "Q" in c[0]]
    for i, a in enumerate(qc):
        lp.le([(mv((a, "Q", "A")), 1)], 0)
        lp.le([(mv((a, "Q", "B")), 1), (emin[a], -rho / 9)], 0)
        for b in qc[i + 1:]:
            h = lp.var()
            lp.le([(mv((a, "Q", "A")), 1), (h, -1)], 0)
            lp.le([(mv((a, "Q", "B")), 1), (h, -1), (emin[b], -rho / 9)], 0)
            lp.le([(mv((b, "Q", "A")), 1), (h, 1)], 0)
            lp.le([(mv((b, "Q", "B")), 1), (h, 1), (emin[a], -rho / 9)], 0)
    # Q -> hub transfers: g[(t, kind)], kind in sel, nl (non-selected light), nh (non-selected heavy)
    g = {}
    for t in QT:
        g[(t, "sel")] = lp.var()
        if t[3]:
            g[(t, "nl")] = lp.var()
        if t[4]:
            g[(t, "nh")] = lp.var()
    # hub-side lower bounds M[(a, kind, rich, ver)]
    M = {}
    for a in (1, 2, 3, 4):
        for kd in ("sel", "non"):
            for rc in ((0, 1) if a == 4 else (0,)):
                for ver in ("AB" if a == 4 else "A"):
                    M[(a, kd, rc, ver)] = lp.var(0.0 if a == 4 else -50.0, 50.0)
    for t in QT:
        rc = int(rich(t))
        e_half = [(lam, -0.5)] if rc else []
        # selected hub has bucket asel
        a = t[2]
        slots = [("sel", a, g[(t, "sel")])]
        if t[3]:
            slots += [("non", b, g[(t, "nl")]) for b in range(1, min(a, 3) + 1)]
        if t[4]:
            slots.append(("non", 4, g[(t, "nh")]))
        for kd, b, gv in slots:
            rcb = rc if b == 4 else 0
            eh = e_half if b == 4 else []
            lp.le([(M[(b, kd, rcb, "A")], 1), (gv, -1)] + eh, 0)
            if b == 4:
                lp.le([(M[(b, kd, rcb, "B")], 1), (gv, -1), (eps[t], -rho / 9)] + eh, -rho / 9)
    # U'-type rows
    for t in UT:
        fs, nq, nz = t[1], t[2], t[3]
        inT = 0.0 if d2.cls(fs) == "P" else 1.0
        cnt = {}
        for sl in fs:
            cnt[sl] = cnt.get(sl, 0) + 1
        rowA = [(eps[t], -rho / 3), (tmarg, -1)] + [(mv((t, sl, "A")), c) for sl, c in cnt.items()]
        if nq:
            rowA.append((mv((t, "Q", "A")), nq))
        lp.ge(rowA, inT + margin - rho / 3, ("A", t))
        if len(fs) + nq + nz == 3:
            rowB = [(eps[t], -2 * rho / 9), (tmarg, -1)] + [(mv((t, sl, "B")), c) for sl, c in cnt.items()]
            if nq:
                rowB.append((mv((t, "Q", "B")), nq))
            lp.ge(rowB, inT + margin - 2 * rho / 9 - nz * rho / 9, ("B", t))
    # Q-type rows
    for t in QT:
        us, asel, cl, ch = t[1], t[2], t[3], t[4]
        c = qcls(t)
        npp, nqq, nzz = us.count("P"), us.count("Q"), us.count("Z1")
        h4 = (asel == 4) + ch
        base = [(eps[t], -rho / 3), (g[(t, "sel")], -1), (tmarg, -1)]
        if cl:
            base.append((g[(t, "nl")], -cl))
        if ch:
            base.append((g[(t, "nh")], -ch))
        if rich(t):
            base.append((lam, h4 / 2 - 1.5))
        rowA = list(base)
        if npp:
            rowA.append((mv((c, "P", "A")), npp))
        if nqq:
            rowA.append((mv((c, "Q", "A")), nqq))
        lp.ge(rowA, margin - rho / 3, ("A", t))
        if len(us) == 3:
            rowB = list(base) + [(eps[t], rho / 9)]
            if npp:
                rowB.append((mv((c, "P", "B")), npp))
            if nqq:
                rowB.append((mv((c, "Q", "B")), nqq))
            lp.ge(rowB, margin - 2 * rho / 9 - nzz * rho / 9, ("B", t))
        if cl == 3:
            lp.ge([(g[(t, "nl")], -1)], 0, ("coef nl", t))
        if ch == 3:
            lp.ge([(g[(t, "nh")], -1), (lam, 0.5)], 0, ("coef nh", t))
    # hub rows
    for a in (1, 2, 3):
        for ms in itertools.combinations_with_replacement(("sel", "non"), a):
            kept = 1.0 if "sel" in ms else 0.0
            lp.ge([(M[(a, kd, 0, "A")], 1) for kd in ms] + [(tmarg, -1)], margin + kept, ("hub", a, ms))
    kinds4 = [(kd, rc) for kd in ("sel", "non") for rc in (0, 1)]
    for ms in itertools.combinations_with_replacement(kinds4, 4):
        kept = 1.0 if any(kd == "sel" for kd, rc in ms) else 0.0
        hasr = any(rc for kd, rc in ms)
        for ver, cst in (("A", 0.0), ("B", rho / 3)):
            row = [(M[(4, kd, rc, ver)], 1) for kd, rc in ms] + [(tmarg, -1)]
            if hasr:
                row.append((lam, -1.5))
            lp.ge(row, margin + kept - cst, ("hub4", ver, ms))
    return lp, eps, lam, tmarg, UT, QT


def solve(rho, margin=0.0, verbose=True):
    lp, eps, lam, tmarg, UT, QT = build(rho, margin)
    A = coo_matrix((lp.v, (lp.r, lp.c)), shape=(lp.nr, lp.nv)).tocsr()
    cobj = np.zeros(lp.nv); cobj[tmarg] = -1.0
    res = linprog(cobj, A_ub=A, b_ub=np.array(lp.b), bounds=list(zip(lp.lo, lp.hi)), method="highs")
    if verbose:
        print(f"rho={rho:.5f} vars={lp.nv} rows={lp.nr} status={res.status} max margin="
              f"{-res.fun if res.status == 0 else None}" + (f" lam={res.x[lam]:.4f}" if res.status == 0 else ""), flush=True)
    return res, eps, lam, tmarg, UT, QT


if __name__ == "__main__":
    for rho in map(float, sys.argv[1:] or ["3.25"]):
        solve(rho)
