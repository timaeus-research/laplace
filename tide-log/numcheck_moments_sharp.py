"""Tide moments-sharp: all-orders moment expansions of the anharmonic Gibbs law.

lam = 2, a = 1/2 (alpha^2 = a^2 lam^3), gamma = lam^2; A = alpha/(6 lam^{3/2}), B = gamma/(24 lam^2).
(1) odd: t^{k+1} <x^{2k+1}> -> -alpha (2k+3)!! / (6 lam^{k+2}); check t * (t^{k+1}<x^{2k+1}> - limit) bounded.
(2) even: t^k <x^{2k}> = (2k-1)!!/lam^k + C_k/(lam^k t) + O(t^-2), C_k = (A^2/2)((2k+5)!! - 15 (2k-1)!!) - B((2k+3)!! - 3 (2k-1)!!);
    check t^2 * (t^k <x^{2k}> - (2k-1)!!/lam^k - C_k/(lam^k t)) bounded.
"""
import numpy as np
from scipy.integrate import quad
from math import sqrt

lam = 2.0; a = 0.5; alpha = a * lam**1.5; gamma = lam**2
A = alpha / (6 * lam**1.5); B = gamma / (24 * lam**2)
def dfact(k): return 1 if k <= 0 else k * dfact(k - 2)
def ell(x): return lam * x**2 / 2 + alpha * x**3 / 6 + gamma * x**4 / 24
def mom(n, t):
    w = lambda x: np.exp(-t * ell(x)); R = 14 / sqrt(lam * t)
    Z = quad(w, -R, R, limit=500, epsabs=1e-15, epsrel=1e-14)[0]
    return quad(lambda x: x**n * w(x), -R, R, limit=500, epsabs=1e-15, epsrel=1e-14)[0] / Z
ts = [50, 100, 200, 400, 800]
print("(1) odd moments: t * (t^{k+1}<x^{2k+1}> - limit)")
for k in range(0, 4):
    lim = -alpha * dfact(2 * k + 3) / (6 * lam**(k + 2))
    print(" k=%d limit=%.5f:" % (k, lim), ["%.4f" % (t * (t**(k + 1) * mom(2 * k + 1, t) - lim)) for t in ts])
print("(2) even moments: t^2 * (t^k<x^{2k}> - (2k-1)!!/lam^k - C_k/(lam^k t))")
for k in range(1, 4):
    Ck = (A**2 / 2) * (dfact(2 * k + 5) - 15 * dfact(2 * k - 1)) - B * (dfact(2 * k + 3) - 3 * dfact(2 * k - 1))
    print(" k=%d C_k=%.5f:" % (k, Ck), ["%.4f" % (t**2 * (t**k * mom(2 * k, t) - dfact(2 * k - 1) / lam**k - Ck / (lam**k * t))) for t in ts])
print("   C_1 vs 45A^2-12B:", (A**2/2)*(105-15) - B*(15-3), 45*A**2 - 12*B, "  C_2 vs 450A^2-96B:", (A**2/2)*(945-45) - B*(105-9), 450*A**2-96*B)
