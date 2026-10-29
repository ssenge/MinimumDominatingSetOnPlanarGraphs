"""Discharging LP for the selection hub rule, U-only relaxation, without hubs inside U (v1).

Rule: H = vertices outside U with >= 4 neighbours in U (H_U is assumed empty here), Z = U n N(H),
U' = U minus Z, F = G[U'] subcubic, T = idrule(F), P = U' minus T, Q = Z minus N(T), Z1 = Z n N(T).
Every q in Q selects one hub neighbour; D' = T + selected hubs. Claim: |D'| <= rho LP_U.

Dual y = (1 - eps)/3 on U, eps = 1 on Z1. Charges: rho y_v - (rho/3)(Y(v) - 1)^+ - [v in D'] plus
transfers, plus the Euler term lam (deg_B(v)/2 - 3/2) on the bipartite planar graph B of H-Q edges
(girth >= 6, so e(B) <= 3/2 |V(B)|). Types:
  U'-type  ('U', Fslots, nQ, nZ1): Fslots as in discharge_a2 (dir, nbr in J, nbr F-degree).
  Q-type   ('Q', Uslots, nW): Uslots a sorted tuple over 'P', 'Q', 'Z1'; nW = number of hubs,
           the type with nW = KMAX stands for all nW >= KMAX (marginal coefficient >= 0).
  Hubs: one row per 4-multiset of neighbour kinds (sel, non, z1), with nonnegative coefficients
  (so every larger multiset is covered).
A feasible LP is a local proof of the claim for every planar graph of girth >= 5 without U-hubs.
"""
import itertools
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import discharge_a2 as d2

KMAX = 4


def utypes():
    out = []
    for fs in d2.all_types(False):
        c = d2.cls(fs)
        for nq in range(4 - len(fs)):
            for nz in range(4 - len(fs) - nq):
                if nq and c != "P":
                    continue
                out.append(("U", fs, nq, nz))
    return out


def qtypes():
    out = []
    for k in range(4):
        for us in itertools.combinations_with_replacement(("P", "Q", "Z1"), k):
            for nw in range(1, KMAX + 1):
                out.append(("Q", us, nw))
    return out


class LP:
    def __init__(self):
        self.nv = 0
        self.lo, self.hi = [], []
        self.r, self.c, self.v, self.b = [], [], [], []
        self.nr = 0
        self.lab = []

    def var(self, lo=-50.0, hi=50.0):
        self.lo.append(lo); self.hi.append(hi); self.nv += 1
        return self.nv - 1

    def le(self, coefs, rhs, lab=None):
        """sum coef * var <= rhs"""
        for k, a in coefs:
            self.r.append(self.nr); self.c.append(k); self.v.append(a)
        self.b.append(rhs); self.nr += 1
        self.lab.append(lab)

    def ge(self, coefs, rhs, lab=None):
        self.le([(k, -a) for k, a in coefs], -rhs, lab)


def build(rho, margin=0.0, lam_fixed=None):
    lp = LP()
    UT, QT = utypes(), qtypes()
    eps = {t: lp.var(0.0, 1.0) for t in UT + QT}
    lam = lp.var(0.0, 5.0) if lam_fixed is None else None
    tmarg = lp.var(-5.0, 5.0)  # common margin variable (maximized)
    Lam = [(lam, 1.0)] if lam is not None else []
    lamc = lam_fixed or 0.0

    def lamterm(a):
        return [(lam, a)] if lam is not None else []

    m = {}

    def mv(t, sl, ver):
        key = (t, sl, ver)
        if key not in m:
            m[key] = lp.var()
        return m[key]

    # F arcs between U'-types (u smaller than v)
    fs_slots = {t: set(t[1]) for t in UT}
    for tu in UT:
        for tv in UT:
            slv = d2.slot_of(tv[1], tu[1], "i", False)
            slu = d2.slot_of(tu[1], tv[1], "o", False)
            if slv in fs_slots[tv] and slu in fs_slots[tu]:
                k = lp.var()
                lp.le([(mv(tv, slv, "A"), 1), (k, 1)], 0)
                lp.le([(mv(tv, slv, "B"), 1), (k, 1), (eps[tu], -rho / 9)], 0)
                lp.le([(mv(tu, slu, "A"), 1), (k, -1)], 0)
                lp.le([(mv(tu, slu, "B"), 1), (k, -1), (eps[tv], -rho / 9)], 0)
    # P-Q edges: f = amount q sends to p
    for tp in UT:
        if tp[2] == 0:
            continue
        for tq in QT:
            if "P" not in tq[1]:
                continue
            f = lp.var()
            lp.le([(mv(tp, "Q", "A"), 1), (f, -1)], 0)
            lp.le([(mv(tp, "Q", "B"), 1), (f, -1), (eps[tq], -rho / 9)], 0)
            lp.le([(mv(tq, "P", "A"), 1), (f, 1)], 0)
            lp.le([(mv(tq, "P", "B"), 1), (f, 1), (eps[tp], -rho / 9)], 0)
    # Q-Q edges: h = amount b sends to a (antisymmetric)
    qq = [t for t in QT if "Q" in t[1]]
    for i, a in enumerate(qq):
        lp.le([(mv(a, "Q", "A"), 1)], 0)
        lp.le([(mv(a, "Q", "B"), 1), (eps[a], -rho / 9)], 0)
        for b in qq[i + 1:]:
            h = lp.var()
            lp.le([(mv(a, "Q", "A"), 1), (h, -1)], 0)
            lp.le([(mv(a, "Q", "B"), 1), (h, -1), (eps[b], -rho / 9)], 0)
            lp.le([(mv(b, "Q", "A"), 1), (h, 1)], 0)
            lp.le([(mv(b, "Q", "B"), 1), (h, 1), (eps[a], -rho / 9)], 0)
    # Q -> hub transfers and the hub-side lower bounds
    gs = {t: lp.var() for t in QT}
    gn = {t: lp.var() for t in QT if t[2] >= 2}
    M = {(kd, ver): lp.var(0.0, 50.0) for kd in ("sel", "non") for ver in "AB"}
    for t in QT:
        for kd, g in (("sel", gs[t]),) + ((("non", gn[t]),) if t in gn else ()):
            lp.le([(M[(kd, "A")], 1), (g, -1)] + lamterm(-0.5), 0.5 * lamc)
            lp.le([(M[(kd, "B")], 1), (g, -1), (eps[t], -rho / 9)] + lamterm(-0.5), 0.5 * lamc - rho / 9)
    # vertex rows: U'-types
    for t in UT:
        fs, nq, nz = t[1], t[2], t[3]
        inT = 0.0 if d2.cls(fs) == "P" else 1.0
        cnt = {}
        for sl in fs:
            cnt[sl] = cnt.get(sl, 0) + 1
        rowA = [(eps[t], -rho / 3), (tmarg, -1)] + [(mv(t, sl, "A"), c) for sl, c in cnt.items()]
        if nq:
            rowA.append((mv(t, "Q", "A"), nq))
        lp.ge(rowA, inT + margin - rho / 3, ("A", t))
        if len(fs) + nq + nz == 3:
            rowB = [(eps[t], -2 * rho / 9), (tmarg, -1)] + [(mv(t, sl, "B"), c) for sl, c in cnt.items()]
            if nq:
                rowB.append((mv(t, "Q", "B"), nq))
            lp.ge(rowB, inT + margin - 2 * rho / 9 - nz * rho / 9, ("B", t))
    # vertex rows: Q-types
    for t in QT:
        us, nw = t[1], t[2]
        npp, nqq, nzz = us.count("P"), us.count("Q"), us.count("Z1")
        base = [(eps[t], -rho / 3), (gs[t], -1), (tmarg, -1)] + lamterm(nw / 2 - 1.5)
        if nw >= 2:
            base.append((gn[t], -(nw - 1)))
        cst = -rho / 3 + lamc * (nw / 2 - 1.5)
        rowA = list(base)
        if npp:
            rowA.append((mv(t, "P", "A"), npp))
        if nqq:
            rowA.append((mv(t, "Q", "A"), nqq))
        lp.ge(rowA, margin + cst, ("A", t))
        if len(us) == 3:
            rowB = list(base) + [(eps[t], rho / 9)]
            if npp:
                rowB.append((mv(t, "P", "B"), npp))
            if nqq:
                rowB.append((mv(t, "Q", "B"), nqq))
            lp.ge(rowB, margin + cst + rho / 9 - nzz * rho / 9, ("B", t))
        if nw == KMAX:
            lp.ge([(gn[t], -1)] + lamterm(0.5), -0.5 * lamc, ("coef", t))
    # hub rows
    for ms in itertools.combinations_with_replacement(("sel", "non", "z1"), 4):
        kept = 1.0 if "sel" in ms else 0.0
        hasq = "sel" in ms or "non" in ms
        for ver, cst in (("A", 0.0), ("B", rho / 3)):
            row = [(M[(kd, ver)], 1) for kd in ms if kd != "z1"] + [(tmarg, -1)]
            row += lamterm(-1.5 if hasq else 0.0)
            lp.ge(row, margin + kept - cst + (1.5 * lamc if hasq else 0.0), ("hub", ver, ms))
    return lp, eps, lam, tmarg, UT, QT


def solve(rho, margin=0.0, verbose=True):
    lp, eps, lam, tmarg, UT, QT = build(rho, margin)
    A = coo_matrix((lp.v, (lp.r, lp.c)), shape=(lp.nr, lp.nv)).tocsr()
    cobj = np.zeros(lp.nv); cobj[tmarg] = -1.0
    res = linprog(cobj, A_ub=A, b_ub=np.array(lp.b), bounds=list(zip(lp.lo, lp.hi)), method="highs")
    if verbose:
        print(f"rho={rho:.5f} vars={lp.nv} rows={lp.nr} status={res.status} max margin={-res.fun if res.status == 0 else None}"
              + (f" lam={res.x[lam]:.4f}" if res.status == 0 else ""), flush=True)
    return res, eps, lam, tmarg, UT, QT


if __name__ == "__main__":
    for rho in map(float, sys.argv[1:] or ["3.25"]):
        solve(rho)
