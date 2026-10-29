"""Binding rows of a certificate LP: solves it and prints the rows with the largest dual weights.
Usage: python3 lp_diag.py <module> <rho> [count], e.g. GIRTH=5 python3 lp_diag.py discharge_r13z 3.25 40
"""
import importlib
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

mod = importlib.import_module(sys.argv[1])
rho = float(sys.argv[2])
lp, *rest = (mod.build_for_diag(rho) if hasattr(mod, "build_for_diag") else mod.build(rho))
A = coo_matrix((lp.v, (lp.r, lp.c)), shape=(lp.nr, lp.nv)).tocsr()
tm = rest[2]
c = np.zeros(lp.nv); c[tm] = -1
res = linprog(c, A_ub=A, b_ub=np.array(lp.b), bounds=list(zip(lp.lo, lp.hi)), method="highs")
print("margin", -res.fun)
du = -res.ineqlin.marginals
for i in np.argsort(-du)[:int(sys.argv[3]) if len(sys.argv) > 3 else 30]:
    if du[i] < 1e-6:
        break
    if lp.lab[i] is not None:
        print(round(du[i], 4), lp.lab[i])
