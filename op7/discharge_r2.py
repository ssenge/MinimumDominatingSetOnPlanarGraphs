"""Discharging LP for rule R2 (round_exp.uhub_idrule), U-only relaxation.

R2: H_U = vertices of U with >= 4 neighbours in U join D; T = idrule on F' = G[U minus H_U] (subcubic);
hubs outside U never join. Claim: |H_U| + |T| <= rho LP_U for planar graphs of girth >= 5.

Dual: y in [0, 1] on F'-vertices by type, y = eta <= 1/3 on H_U. LP_U >= sum y - 1/3 sum_v (Y(v) - 1)^+.
Charge of v: rho y_v - (rho/3)(Y(v) - 1)^+ - [v in D'] + transfers + Euler terms.
Vertices outside U by number of U-neighbours: W1 (never overclaims), W2, W3 (paid per edge by
(rho/3) (y - 1/2)^+ resp. (rho/3) (y - 1/3)^+), W-hubs (>= 4; rows over 4-multisets of neighbour kinds
with nonnegative coefficients, so every larger multiset is covered).
Euler terms: a multiplier times sum_v (deg_S(v)/2 - c) <= 0 for a subgraph S, c = 3/2 when S is
bipartite (c = gb/(gb-2), gb = even girth bound) and c = g/(g-2) otherwise; vertices without an S-edge are left out.
  E_j (j = 1, 2, 3): hubs (W-hubs and H_U) to F'-vertices with >= j hub neighbours, c = 3/2.
  G[H_U], c = 5/3.
  FAMILIES (UU, W2, W3, HB): edges U-U (if UU) plus U-W2, U-W3, U-(W-hub) as flagged; bipartite ones
  use only F'-vertices on the U side. A W2 or W3 vertex of S passes its own term to its U-neighbours.
F'-type ('U', fs, nHU, kh, n2, n3): fs = skeleton as in discharge_a2 (F'-slots), nHU = number of H_U
neighbours, kh = number of W-hubs (KB = at least KB), n2, n3 = numbers of W2, W3 neighbours (2 = at
least 2). Transfers on F'-edges depend on the two classes xsk = (skeleton, min(hub count, XCLS)) only.
"""
import itertools
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import discharge_a2 as d2
from discharge_h import LP

KB = 4  # hub-count bucket cap
FAMILIES = [(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, 1),
            (0, 0, 0, 1), (0, 0, 1, 1), (0, 1, 1, 1), (0, 0, 1, 0)]


def ftypes():
    out = []
    for fs in d2.all_types(False):
        for nhu in range(4 - len(fs)):
            for kh in range(KB + 1):
                for n2 in range(3):
                    for n3 in range(3):
                        out.append(("U", fs, nhu, kh, n2, n3))
    return out


XCLS = 2


def xsk(t):
    """Aggregation class for F'-edge transfers: skeleton plus the capped hub count."""
    return (t[1], min(t[2] + t[3], XCLS))


def kbucket(t):
    return min(t[2] + t[3], KB)


def build(rho, margin=0.0, families=FAMILIES, use_lam=True, use_mu=True, g=5):
    cgen = g / (g - 2)
    gb = g + (g % 2)
    cbip = gb / (gb - 2)
    lp = LP()
    FT = ftypes()
    XS = sorted({xsk(t) for t in FT})
    y = {t: lp.var(0.0, 1.0) for t in FT}
    p2 = {t: lp.var(0.0, 1.0) for t in FT}
    p3 = {t: lp.var(0.0, 1.0) for t in FT}
    gW = {t: lp.var() for t in FT if t[3] > 0}
    gH = {t: lp.var() for t in FT if t[2] > 0}
    lam = {j: lp.var(0.0, 5.0 if use_lam else 0.0) for j in (1, 2, 3)}
    mu = lp.var(0.0, 5.0 if use_mu else 0.0)
    fam = {f: lp.var(0.0, 5.0) for f in families}
    eta = lp.var(0.0, 1 / 3)
    ghw = lp.var()
    tmarg = lp.var(-5.0, 5.0)
    ymax = {s: lp.var(0.0, 1.0) for s in XS}
    for t in FT:
        lp.le([(y[t], 1), (ymax[xsk(t)], -1)], 0)
        lp.ge([(p2[t], 1), (y[t], -1)], -0.5)
        lp.ge([(p3[t], 1), (y[t], -1)], -1 / 3)

    def cst(f):
        return cgen if f[0] else cbip

    def w_edge_gain(f, k):
        """Gain of a U-vertex per edge to a W_k vertex (k = 2, 3) in family f: own half + share."""
        return 0.5 + (k / 2 - cst(f)) / k

    m = {}

    def mv(key):
        if key not in m:
            m[key] = lp.var()
        return m[key]

    sl_of = {s: set(s[0]) for s in XS}
    for su in XS:
        for sv in XS:
            slv = d2.slot_of(sv[0], su[0], "i", False)
            slu = d2.slot_of(su[0], sv[0], "o", False)
            if slv in sl_of[sv] and slu in sl_of[su]:
                k = lp.var()
                lp.le([(mv((sv, slv, "A")), 1), (k, 1)], 0)
                lp.le([(mv((sv, slv, "B")), 1), (k, 1), (ymax[su], rho / 3)], 0)
                lp.le([(mv((su, slu, "A")), 1), (k, -1)], 0)
                lp.le([(mv((su, slu, "B")), 1), (k, -1), (ymax[sv], rho / 3)], 0)

    def lam_edge(c):
        return [(lam[j], 0.5) for j in (1, 2, 3) if c >= j]

    MW = {(c, ver): lp.var(0.0, 50.0) for c in range(1, KB + 1) for ver in "AB"}
    MH = {(c, ver): lp.var(0.0, 50.0) for c in range(1, KB + 1) for ver in "AB"}
    for t in FT:
        c = kbucket(t)
        for gv, MM, ok in ((gW.get(t), MW, t[3] > 0), (gH.get(t), MH, t[2] > 0)):
            if not ok:
                continue
            lp.le([(MM[(c, "A")], 1), (gv, -1)] + [(v, -a) for v, a in lam_edge(c)], 0)
            lp.le([(MM[(c, "B")], 1), (gv, -1), (y[t], rho / 3)] + [(v, -a) for v, a in lam_edge(c)], 0)
    # F'-vertex rows
    for t in FT:
        fs, nhu, kh, n2, n3 = t[1:]
        inT = 0.0 if d2.cls(fs) == "P" else 1.0
        k = kh + nhu
        cnt = {}
        for sl in fs:
            cnt[sl] = cnt.get(sl, 0) + 1
        base = [(y[t], rho), (tmarg, -1), (p2[t], -n2 * rho / 3), (p3[t], -n3 * rho / 3)]
        if kh:
            base.append((gW[t], -kh))
        if nhu:
            base.append((gH[t], -nhu))
        for j in (1, 2, 3):
            if k >= j:
                base.append((lam[j], k / 2 - cbip))
        dU = len(fs) + nhu
        for f in families:
            UU, W2, W3, HB = f
            deg = UU * dU + W2 * n2 + W3 * n3 + HB * kh
            if deg:
                val = deg / 2 - cst(f) + W2 * n2 * (1 - cst(f)) / 2 + W3 * n3 * (1.5 - cst(f)) / 3
                base.append((fam[f], val))
        xs = xsk(t)
        rowA = base + [(mv((xs, sl, "A")), c) for sl, c in cnt.items()]
        lp.ge(rowA, inT + margin, ("A", t))
        rowB = base + [(y[t], -rho / 3)] + [(mv((xs, sl, "B")), c) for sl, c in cnt.items()]
        if nhu:
            rowB.append((eta, -rho / 3 * nhu))
        lp.ge(rowB, inT + margin - rho / 3, ("B", t))
        if kh == KB:
            lp.ge([(gW[t], -1)] + lam_edge(KB) + [(fam[f], 0.5) for f in families if f[3]], 0, ("coef kh", t))
        if n2 == 2:
            lp.ge([(p2[t], -rho / 3)] + [(fam[f], w_edge_gain(f, 2)) for f in families if f[1]], 0)
        if n3 == 2:
            lp.ge([(p3[t], -rho / 3)] + [(fam[f], w_edge_gain(f, 3)) for f in families if f[2]], 0)
    kinds = list(range(1, KB + 1)) + ["HU"]
    # W-hub rows
    for ms in itertools.combinations_with_replacement(kinds, 4):
        cs = [c for c in ms if c != "HU"]
        nh = len(ms) - len(cs)
        econst = [(lam[j], -cbip) for j in (1, 2, 3) if any(c >= j for c in cs)]
        for f in families:
            if f[3]:
                deg = len(cs) + (nh if f[0] else 0)
                if deg:
                    econst.append((fam[f], deg / 2 - cst(f)))
        for ver, cs0 in (("A", 0.0), ("B", rho / 3)):
            row = [(MW[(c, ver)], 1) for c in cs] + [(tmarg, -1)] + econst
            if nh:
                row.append((ghw, nh))
                if ver == "B":
                    row.append((eta, -rho / 3 * nh))
            lp.ge(row, margin - cs0, ("hubW", ver, ms))
    uu_hub = [f for f in families if f[0] and f[3]]
    lp.ge([(ghw, 1)] + [(fam[f], 0.5) for f in uu_hub], 0)
    lp.ge([(ghw, 1), (eta, -rho / 3)] + [(fam[f], 0.5) for f in uu_hub], 0)
    lp.ge([(ghw, -1)] + [(fam[f], 0.5) for f in uu_hub], 0)
    uu = [f for f in families if f[0]]
    lp.ge([(mu, 0.5)] + [(fam[f], 0.5) for f in uu], 0)
    lp.ge([(mu, 0.5), (eta, -rho / 3)] + [(fam[f], 0.5) for f in uu], 0)
    # H_U rows (cost 1)
    for ms in itertools.combinations_with_replacement(kinds, 4):
        cs = [c for c in ms if c != "HU"]
        nh = len(ms) - len(cs)
        econst = [(lam[j], -cbip) for j in (1, 2, 3) if any(c >= j for c in cs)]
        if nh:
            econst.append((mu, nh / 2 - cgen))
        for f in uu:
            econst.append((fam[f], len(ms) / 2 - cgen))
        for ver, cs0 in (("A", 0.0), ("B", rho / 3)):
            row = [(MH[(c, ver)], 1) for c in cs] + [(tmarg, -1), (eta, rho)] + econst
            if ver == "B":
                row.append((eta, -rho / 3 * (1 + nh)))
            lp.ge(row, margin + 1.0 - cs0, ("hubU", ver, ms))
    info = dict(y=y, lam=lam, mu=mu, fam=fam, eta=eta, tmarg=tmarg, FT=FT)
    return lp, info


def solve(rho, margin=0.0, verbose=True, **kw):
    lp, info = build(rho, margin, **kw)
    A = coo_matrix((lp.v, (lp.r, lp.c)), shape=(lp.nr, lp.nv)).tocsr()
    cobj = np.zeros(lp.nv); cobj[info["tmarg"]] = -1.0
    res = linprog(cobj, A_ub=A, b_ub=np.array(lp.b), bounds=list(zip(lp.lo, lp.hi)), method="highs")
    if verbose:
        extra = ""
        if res.status == 0:
            x = res.x
            extra = " lam=" + ",".join(f"{x[info['lam'][j]]:.3f}" for j in (1, 2, 3)) + f" mu={x[info['mu']]:.3f}"
            extra += " fam=" + ",".join(f"{''.join(map(str, f))}:{x[v]:.3f}" for f, v in info["fam"].items())
            extra += f" eta={x[info['eta']]:.3f}"
        print(f"rho={rho:.5f} vars={lp.nv} rows={lp.nr} status={res.status} max margin="
              f"{-res.fun if res.status == 0 else None}" + extra, flush=True)
    return res, lp, info


G_DIAG = 5


def build_for_diag(rho):
    lp, info = build(rho, g=G_DIAG)
    return lp, None, None, info["tmarg"]


if __name__ == "__main__":
    g = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    for rho in map(float, sys.argv[2:] or ["3.25"]):
        print("g =", g, end=" ")
        solve(rho, g=g)
