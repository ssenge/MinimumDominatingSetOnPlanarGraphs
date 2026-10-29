"""Exact rational check of a certificate LP (discharge_r13z and modules with the same interface).

Solves the LP in floating point, then builds an exact assignment and checks every row with
rational arithmetic:
  - every coefficient and right-hand side is replaced by the rational with denominator <= 10^4
    nearest to it (all constants of the LP are such rationals; the check asserts that the float
    lies within 1e-11 of it, which makes the rational unique);
  - the LP is solved with every row tightened by 1e-6; the primary variables (eps, lam, nu,
    transfers, payments) are then rounded to multiples of 10^-9
    and clamped to their bounds;
  - the derived variables (info["dep"], in dependency order: emin/ebase, then the lower bounds m
    and M) are set to the smallest of their upper bounds, computed exactly;
  - the margin variable is set to 0, and every row is checked exactly. The certified margin is the
    smallest exact slack over the rows that contain the margin variable.
Usage: GIRTH=5 python3 cert_exact.py discharge_r13z 3.9
"""
import importlib
import os
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

QMAX = 10 ** 4


def exact(c):
    f = Fraction(c).limit_denominator(QMAX)
    assert abs(float(f) - c) <= 1e-11 * max(1.0, abs(c)), c
    return f


def main(modname, rho):
    mod = importlib.import_module(modname)
    rho_f = float(rho)
    t0 = time.time()
    lp, info = mod.build(rho_f)
    A = coo_matrix((lp.v, (lp.r, lp.c)), shape=(lp.nr, lp.nv)).tocsr()
    tm = info["tmarg"]
    cobj = np.zeros(lp.nv); cobj[tm] = -1.0
    # every row tightened by 1e-6 (above the solver tolerance 1e-7), so that rounding the solution to 1e-9 cannot break rows that
    # are tight at the optimum and carry no margin variable
    res = linprog(cobj, A_ub=A, b_ub=np.array(lp.b) - 1e-6, bounds=list(zip(lp.lo, lp.hi)), method="highs")
    assert res.status == 0, res.message
    print(f"{modname} g={getattr(mod, 'GIRTH', '?')} rho={rho} float margin={-res.fun:.6f} "
          f"vars={lp.nv} rows={lp.nr} solve {time.time() - t0:.0f}s", flush=True)
    rows = [[] for _ in range(lp.nr)]
    cache = {}
    for r, c, v in zip(lp.r, lp.c, lp.v):
        if v not in cache:
            cache[v] = exact(v)
        rows[r].append((c, cache[v]))
    b = [exact(x) for x in lp.b]
    lo = [exact(x) for x in lp.lo]
    hi = [exact(x) for x in lp.hi]
    dep = info["dep"]
    depset = set(j for layer in dep for j in layer)
    x = [None] * lp.nv
    D = 10 ** 9
    for j in range(lp.nv):
        if j not in depset:
            v = Fraction(int(round(res.x[j] * D)), D)
            x[j] = min(max(v, lo[j]), hi[j])
    x[tm] = Fraction(0)
    # rows by variable with a positive coefficient (upper bounds on derived variables)
    ub_rows = {j: [] for j in depset}
    for i, row in enumerate(rows):
        for c, a in row:
            if c in depset and a > 0:
                ub_rows[c].append(i)
    for layer in dep:
        for j in layer:
            best = hi[j]
            for i in ub_rows[j]:
                a_j = None
                rest = Fraction(0)
                for c, a in rows[i]:
                    if c == j:
                        a_j = a
                    else:
                        assert x[c] is not None, ("derived variable used before it is set", c)
                        rest += a * x[c]
                best = min(best, (b[i] - rest) / a_j)
            x[j] = best
    bad = [j for j in range(lp.nv) if not (lo[j] <= x[j] <= hi[j])]
    worst, nviol, cert = None, 0, None
    for i, row in enumerate(rows):
        lhs = sum((a * x[c] for c, a in row), Fraction(0))
        slack = b[i] - lhs
        if slack < 0:
            nviol += 1
            if worst is None or slack < worst[0]:
                worst = (slack, lp.lab[i])
        if any(c == tm for c, _ in row):
            # the margin variable enters with coefficient -1 (row >= ... + margin); its slack
            # is the margin this row certifies
            cert = slack if cert is None else min(cert, slack)
    print(f"bounds violated: {len(bad)}; rows violated: {nviol}" + (f", worst {float(worst[0]):.3e} {worst[1]}" if worst else ""))
    print(f"certified margin (exact): {float(cert):.6f}  ({'VALID' if not bad and not nviol and cert >= 0 else 'NOT VALID'})"
          f"  total {time.time() - t0:.0f}s", flush=True)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certs",
                       f"{modname}_g{getattr(mod, 'GIRTH', 'x')}_rho{rho}_exact.pkl")
    pickle.dump(dict(x=x, rho=rho), open(out, "wb"))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
