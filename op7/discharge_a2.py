"""Discharging LP for piece (a) with richer types.

Vertex type: sorted tuple of neighbour slots (dir, nbr_in_J, nbr_degree[, nbr_s]) where dir = 'i'
for a smaller and 'o' for a larger neighbour. Class of v: J if #i < #o, else P if some slot has
nbr_in_J, else R. Unknowns as in discharge_a.py: eps(type) in [0, 1], kappa on each compatible arc
type pair, lower-bound variables per (type, slot, version). Feasible LP = local proof that
|P| >= Phi_F for every subcubic graph F and every ordering.
"""
import itertools
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def isJ(t):
    s = sum(1 for sl in t if sl[0] == "i")
    return s < len(t) - s


def cls(t):
    if isJ(t):
        return "J"
    return "P" if any(sl[1] for sl in t) else "R"


def all_types(with_s):
    opts = []
    for dirn in ("i", "o"):
        for j in (0, 1):
            for dg in (1, 2, 3):
                if with_s:
                    for s in range(dg + 1):
                        opts.append((dirn, j, dg, s))
                else:
                    opts.append((dirn, j, dg))
    T = []
    for d in range(4):
        for combo in itertools.combinations_with_replacement(opts, d):
            t = tuple(sorted(combo))
            if ok(t, with_s):
                T.append(t)
    return T


def ok(t, with_s):
    """Local sanity: a J neighbour must be consistent with its own J rule given the arc direction."""
    for sl in t:
        dirn, j, dg = sl[0], sl[1], sl[2]
        if with_s:
            s = sl[3]
            # neighbour u has s smaller neighbours; if dirn == 'i' u < v so v is larger: u has l >= 1
            l = dg - s
            if dirn == "i" and l < 1:
                return False
            if dirn == "o" and s < 1:
                return False
            if j != (s < l):
                return False
        else:
            if j and dirn == "o":
                # u larger than v and u in J: u has s <= 1 (deg 3) or s = 0 (deg <= 2): impossible if deg <= 2
                if dg <= 2:
                    return False
    return True


def slot_of(tv, tu, dirn_from_v, with_s):
    """The slot that u occupies in v's type (dirn_from_v = 'i' if u is smaller)."""
    base = (dirn_from_v, int(isJ(tu)), len(tu))
    if with_s:
        base = base + (sum(1 for sl in tu if sl[0] == "i"),)
    return base


def main(with_s=0, margin=0.0, rho=3.0, quiet=False):
    with_s = bool(int(with_s)); rho = float(rho)
    T = all_types(with_s)
    nT = len(T)
    eps = {t: i for i, t in enumerate(T)}
    nv = nT
    kap = {}
    # arc u -> v (u smaller): v has slot ('i', ...) describing u, u has slot ('o', ...) describing v
    slots_of = {t: set(t) for t in T}
    for tu in T:
        for tv in T:
            if slot_of(tv, tu, "i", with_s) in slots_of[tv] and slot_of(tu, tv, "o", with_s) in slots_of[tu]:
                kap[(tu, tv)] = nv; nv += 1
    mvar = {}
    for t in T:
        for sl in set(t):
            for ver in ("A", "B"):
                mvar[(t, sl, ver)] = nv; nv += 1
    if not quiet: print("types", nT, "arc pairs", len(kap), "vars", nv, flush=True)
    rows = []
    rhs = []
    def add(coefs, b):
        rows.append(coefs); rhs.append(b)
    # contributions
    for (tu, tv), k in kap.items():
        # at v (head): u is slot ('i',...) ; contribution -kappa ; B adds eps(u)/3
        slv = slot_of(tv, tu, "i", with_s)
        add([(mvar[(tv, slv, "A")], 1), (k, 1)], 0)
        add([(mvar[(tv, slv, "B")], 1), (k, 1), (eps[tu], -rho / 9)], 0)
        slu = slot_of(tu, tv, "o", with_s)
        add([(mvar[(tu, slu, "A")], 1), (k, -1)], 0)
        add([(mvar[(tu, slu, "B")], 1), (k, -1), (eps[tv], -rho / 9)], 0)
    missing = 0
    for t in T:
        for sl in set(t):
            # a slot with no compatible neighbour type: the type is not realizable, skip it
            pass
    for t in T:
        inT = 0.0 if cls(t) == "P" else 1.0
        cnt = {}
        for sl in t:
            cnt[sl] = cnt.get(sl, 0) + 1
        # charge = rho/3 (1 - eps_v) - rho/9 (1 - eps(N[v]))^+ - inT + transfers >= margin
        add([(eps[t], rho / 3)] + [(mvar[(t, sl, "A")], -c) for sl, c in cnt.items()], rho / 3 - inT - margin)
        if len(t) == 3:
            add([(eps[t], rho / 3 - rho / 9)] + [(mvar[(t, sl, "B")], -c) for sl, c in cnt.items()],
                rho / 3 - rho / 9 - inT - margin)
    # slots with no compatible arc would leave m unbounded above: bound m by a big constant
    A = lil_matrix((len(rows), nv))
    for i, row in enumerate(rows):
        for k, v in row:
            A[i, k] += v
    bounds = [(0, 1)] * nT + [(-50, 50)] * (nv - nT)
    r = linprog(np.zeros(nv), A_ub=A.tocsr(), b_ub=np.array(rhs), bounds=bounds, method="highs")
    if quiet: return r.status == 0
    print("feasible:", r.status == 0, r.message, flush=True)
    if r.status == 0:
        x = r.x
        for t in T:
            if x[eps[t]] > 1e-9:
                print(cls(t), t, "eps=%.4f" % x[eps[t]])
        return
    m = len(rhs)
    from scipy.sparse import hstack, identity
    A2 = hstack([A.tocsr(), -identity(m)]).tocsr()
    c = np.concatenate([np.zeros(nv), np.ones(m)])
    r = linprog(c, A_ub=A2, b_ub=np.array(rhs), bounds=bounds + [(0, None)] * m, method="highs")
    print("min total violation", r.fun)


if __name__ == "__main__":
    main(*sys.argv[1:])
