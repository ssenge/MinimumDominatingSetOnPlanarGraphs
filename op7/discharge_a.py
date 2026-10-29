"""Computer search for a discharging proof of piece (a): |P| >= Phi_F for idrule on subcubic F.

Vertex type tau = (d, s, sJ, lJ): degree, number of smaller neighbours, smaller / larger neighbours
in J. Class: J if s < l, else P if sJ + lJ >= 1, else R. Unknowns: eps(tau) in [0, 1] and a transfer
kappa(tau1, tau2) on every arc from a smaller endpoint of type tau1 to a larger one of type tau2
(paid by the head, received by the tail). Charge of v:
  1[v in P] - eps(v) - [d = 3] (1/3) (1 - eps(N[v]))^+ + sum_out kappa - sum_in kappa.
Arc transfers sum to 0, so charge >= 0 at every vertex gives |P| >= sum eps + penalties >= Phi_F.
'For all neighbour types' is handled with one lower-bound variable per (type, slot kind).
"""
import itertools
import sys

import numpy as np
from scipy.optimize import linprog


def types():
    out = []
    for d in range(4):
        for s in range(d + 1):
            l = d - s
            for sJ in range(s + 1):
                for lJ in range(l + 1):
                    J = s < l
                    if J and sJ > 1:
                        continue
                    out.append((d, s, sJ, lJ))
    return out


def cls(t):
    d, s, sJ, lJ = t
    if s < d - s:
        return "J"
    return "P" if sJ + lJ else "R"


def compatible(tv, direction, tu):
    """Can a vertex of type tu be an in-neighbour (direction 'in', tu < tv) or an out-neighbour of tv?"""
    du, su, sJu, lJu = tu
    lu = du - su
    vJ = cls(tv) == "J"
    if direction == "in":  # tu is smaller: v is an out-neighbour of u
        return lu >= 1 and (lJu >= 1 if vJ else lu - lJu >= 1)
    return su >= 1 and (sJu >= 1 if vJ else su - sJu >= 1)


def build_lp(margin=0.0):
    T = types()
    ti = {t: i for i, t in enumerate(T)}
    nv = 0
    eps = {}
    for t in T:
        eps[t] = nv; nv += 1
    kap = {}
    for a in T:
        for b in T:
            if compatible(b, "in", a) and compatible(a, "out", b):
                kap[(a, b)] = nv; nv += 1
    mvar = {}
    for t in T:
        for dirn in ("in", "out"):
            for c in ("J", "N"):
                for ver in ("A", "B"):
                    mvar[(t, dirn, c, ver)] = nv; nv += 1
    rows, rhs = [], []

    def add(coefs, b):  # sum coefs * var <= b
        row = np.zeros(nv)
        for k, v in coefs:
            row[k] += v
        rows.append(row); rhs.append(b)

    for tv in T:
        d, s, sJ, lJ = tv
        l = d - s
        for dirn in ("in", "out"):
            for tu in T:
                if not compatible(tv, dirn, tu):
                    continue
                if dirn == "in" and (tu, tv) not in kap:
                    continue
                if dirn == "out" and (tv, tu) not in kap:
                    continue
                c = "J" if cls(tu) == "J" else "N"
                k = kap[(tv, tu)] if dirn == "out" else kap[(tu, tv)]
                sign = 1 if dirn == "out" else -1
                # m_A <= sign*kappa ;  m_B <= sign*kappa + eps(tu)/3
                add([(mvar[(tv, dirn, c, "A")], 1), (k, -sign)], 0)
                add([(mvar[(tv, dirn, c, "B")], 1), (k, -sign), (eps[tu], -1 / 3)], 0)
        isP = 1.0 if cls(tv) == "P" else 0.0
        slots = [("in", "J", sJ), ("in", "N", s - sJ), ("out", "J", lJ), ("out", "N", l - lJ)]
        # A:  isP - eps_v + sum slots m_A >= margin
        add([(eps[tv], 1)] + [(mvar[(tv, a, c, "A")], -k) for a, c, k in slots if k], isP - margin)
        if d == 3:
            # B: isP - eps_v - 1/3 + eps_v/3 + sum slots m_B >= margin
            add([(eps[tv], 1 - 1 / 3)] + [(mvar[(tv, a, c, "B")], -k) for a, c, k in slots if k],
                isP - 1 / 3 - margin)
    bounds = [(0, 1)] * len(eps) + [(None, None)] * (nv - len(eps))
    return np.array(rows), np.array(rhs), bounds, nv, eps, kap, T


def main():
    A, b, bounds, nv, eps, kap, T = build_lp()
    print("types", len(T), "vars", nv, "rows", len(b))
    r = linprog(np.zeros(nv), A_ub=A, b_ub=b, bounds=bounds, method="highs")
    print("feasible:", r.status == 0, r.message)
    if r.status == 0:
        for t in T:
            print(t, cls(t), "eps=%.3f" % r.x[eps[t]])
        return
    # minimal total violation
    m = len(b)
    A2 = np.hstack([A, -np.eye(m)])
    c = np.concatenate([np.zeros(nv), np.ones(m)])
    r = linprog(c, A_ub=A2, b_ub=b, bounds=bounds + [(0, None)] * m, method="highs")
    print("min total violation", r.fun)


if __name__ == "__main__":
    main()


def diagnose():
    A, b, bounds, nv, eps, kap, T = build_lp()
    m = len(b)
    A2 = np.hstack([A, -np.eye(m)])
    c = np.concatenate([np.zeros(nv), np.ones(m)])
    r = linprog(c, A_ub=A2, b_ub=b, bounds=bounds + [(0, None)] * m, method="highs")
    sl = r.x[nv:]
    # reconstruct which rows are vertex constraints
    idx = 0
    labels = []
    for tv in T:
        d, s, sJ, lJ = tv
        for dirn in ("in", "out"):
            for tu in T:
                if not compatible(tv, dirn, tu):
                    continue
                if dirn == "in" and (tu, tv) not in kap:
                    continue
                if dirn == "out" and (tv, tu) not in kap:
                    continue
                labels += [("m", tv, dirn, tu, "A"), ("m", tv, dirn, tu, "B")]
        labels.append(("A", tv))
        if d == 3:
            labels.append(("B", tv))
    for i in np.nonzero(sl > 1e-9)[0]:
        print(labels[i], round(sl[i], 4))
