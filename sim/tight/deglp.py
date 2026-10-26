# Degree-sequence-only LP. Variables N_d (d=1..D, D+1 = ">D"), m normalised to 1.
#  (deg)  sum_d d N_d = 2 (class D+1: >= (D+1) N)
#  (I_k)  m <= sum_{d<k} d N_d + 3 N_{>=k}            [e(V>=k) <= 3|V>=k|; other edges touch V<k]
#  (J_k)  sum_{d>=k} (d-6) N_d <= 2 N                 [e(V>=k) <= 3|V>=k|, e(V<k,V>=k) <= 2n]
import sys
import numpy as np
from scipy.optimize import linprog

def solve(s, D=40, Ks=None, Js=None):
    C = list(range(1, D + 2)); n = len(C)
    Ks = range(1, D + 2) if Ks is None else Ks
    Js = range(1, D + 2) if Js is None else Js
    c = np.array([1 - s ** d for d in C])
    Aeq = [[d if d <= D else 0 for d in C] + [0]]  # extra var T = sum of degrees of class D+1
    Aeq[0][-1] = 1; beq = [2]
    Aub, bub, names = [], [], []
    row = [0] * n + [-1]; row[n - 1] = D + 1; Aub.append(row); bub.append(0); names.append("top deg")
    for k in Ks:
        row = [-(d if d < k else 3) for d in C] + [0]
        Aub.append(row); bub.append(-1); names.append(f"I_{k}")
    for k in Js:
        row = [(d - 6 if d >= k else 0) - 2 for d in C[:-1]] + [-6 - 2 if D + 1 >= k else -2] + [1 if D + 1 >= k else 0]
        Aub.append(row); bub.append(0); names.append(f"J_{k}")
    r = linprog(np.append(c, 0), A_ub=np.array(Aub, float), b_ub=bub, A_eq=np.array(Aeq, float), b_eq=beq,
                bounds=(0, None), method="highs")
    return r, names

if __name__ == "__main__":
    s = float(sys.argv[1]) if len(sys.argv) > 1 else 0.625
    r, names = solve(s)
    print(f"s={s} degree-only LP c'={r.fun:.6f} f={s*r.fun:.6f}")
    print("  N:", {d: round(v, 4) for d, v in zip(range(1, 42), r.x) if v > 1e-9})
    print("  duals:", {nm: round(-y, 5) for nm, y in zip(names, r.ineqlin.marginals) if abs(y) > 1e-9})
