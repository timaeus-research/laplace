import numpy as np
from scipy.integrate import quad
from math import factorial
def dfact(n):  # (n-1)!! for even n
    r = 1
    for k in range(1, n, 2): r *= k
    return r
lam, a = 2.0, 0.5; alpha = a * lam**1.5; g = lam**2
l = lambda x: lam * x**2 / 2 + alpha * x**3 / 6 + g * x**4 / 24
for t in [100.0, 1000.0, 10000.0]:
    w = lambda x: np.exp(-t * l(x)); Z = quad(w, -np.inf, np.inf, epsabs=1e-16, epsrel=1e-13)[0]
    row = []
    for n in [2, 4, 6, 8]:
        m = quad(lambda x: x**n * w(x), -np.inf, np.inf, epsabs=1e-16, epsrel=1e-13)[0] / Z
        row.append((n, t**(n / 2) * m, dfact(n) / lam**(n / 2)))
    print("t=%g even: " % t + "  ".join("n=%d: %.4f (lim %.4f)" % r for r in row))
    row = []
    for n in [1, 3, 5]:
        m = quad(lambda x: x**n * w(x), -np.inf, np.inf, epsabs=1e-16, epsrel=1e-13)[0] / Z
        # odd: <x^n> ~ -alpha/(6) * ... : t^{(n+1)/2} <x^n> -> -(alpha/6) * lam^{-(n+3)/2} * (E[g^{n+3}] - ... ) ; just print scaled value
        row.append((n, t**((n + 1) / 2) * m))
    print("        odd: " + "  ".join("n=%d: t^{(n+1)/2}<x^n> = %.4f" % r for r in row))
# known odd limits: t<x> -> -alpha/(2 lam^2); t^2<x^3> -> -5alpha/(2 lam^3)
print("expected t<x> ->", -alpha / (2 * lam**2), "; t^2<x^3> ->", -5 * alpha / (2 * lam**3), "; guess t^3<x^5> -> -(alpha/6)(E[g^8]-... )")
