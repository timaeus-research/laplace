"""Tide 90 numerical check: the first correction to the Laplace transform of the localised energy.

Claim: Lambda_t(s) = (1+s)^(-1/2) - s e1 / ((1+s)^(3/2) t) + O(t^-2), e1 = energyLocCoeff1 = (a^2-g)/(2lam) - a alpha/(2lam^2) - gamma/(8lam^2) + 5alpha^2/(24lam^3), a = g x0.
E2: prod_i Lambda_i = (1+s)^(-d/2) - s (sum e1_i) / ((1+s)^(d/2+1) t) + O(t^-2).
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0
e1 = (a**2 - g) / (2 * lam) - a * alpha / (2 * lam**2) - gamma / (8 * lam**2) + 5 * alpha**2 / (24 * lam**3)
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def Zloc(i, u):
    lim = 14 / np.sqrt(u * lam[i]) + abs(u0[i]) + 2
    return quad(lambda x: np.exp(-u * ell(i, x) - g * (x - u0[i])**2 / 2), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
print("e1 =", e1)
for s in [-0.5, 1.0, 3.0]:
    A = 1 + s
    print(f"s = {s}: predicted 1/t coefficient -s e1 / A^1.5 = {-s*e1/A**1.5},  E2: {-s*e1.sum()/A**2}")
    for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
        r = np.array([Zloc(i, A * t) / Zloc(i, t) for i in range(2)])
        c = t * (r - A**-0.5)
        r2 = t**2 * (r - A**-0.5 + s * e1 / (A**1.5 * t))
        prod = r[0] * r[1]
        c2 = t * (prod - A**-1); r2p = t**2 * (prod - A**-1 + s * e1.sum() / (A**2 * t))
        print(f"  t={t:5.0f}: t(Lambda-A^-1/2) = {c[0]:.5f}, {c[1]:.5f}   t^2*(remainder) = {r2[0]:.4f}, {r2[1]:.4f}   E2: t(prod - A^-1) = {c2:.5f}, t^2 rem = {r2p:.4f}")
