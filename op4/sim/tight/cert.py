# Exact check of the pointwise certificate g(d) >= a*min(d,3) + b*(min(d,6)+2) for all d >= 1,
# with b = (g6-g3)/3, a = (8 g3 - 5 g6)/9, c' = a + 2b = (2 g3 + g6)/9, and the resulting kappa.
from fractions import Fraction as F
import math

def check(s):
    g = lambda d: 1 - s ** d
    b = (g(6) - g(3)) / 3
    a = (8 * g(3) - 5 * g(6)) / 9
    assert a >= 0 and b >= 0
    for d in range(1, 7):
        slack = g(d) - a * min(d, 3) - b * (min(d, 6) + 2)
        assert slack >= 0, (d, slack)
    # d >= 6: g(d) >= g(6) and the right side is constant 3a + 8b = g(6)
    assert 3 * a + 8 * b == g(6)
    c = a + 2 * b
    assert c == (2 * g(3) + g(6)) / 9
    f = s * c
    return a, b, c, f

for s in (F(5, 8), F(43, 64)):
    a, b, c, f = check(s)
    q = 1 - f
    print(f"s={s}: a={a} b={b}\n   c'={c} = {float(c):.6f}\n   f=s*c'={f} = {float(f):.6f}   kappa={math.log(3)/math.log(1/float(q)):.4f}")
print("old (orientation) f =", F(1935, 12288), float(F(1935, 12288)))
