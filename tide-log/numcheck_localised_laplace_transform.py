"""Tide 89 numerical check: the Laplace transform of the localised energy.

Lambda_t(s) := <exp(-s t ell)>_loc(t) = Z_loc((1+s)t)/Z_loc(t)  (exact),  -> (1+s)^(-1/2) with O(1/t) error, for s > -1;
on E2 (d = 2): <exp(-s t L)>_loc = prod_i Lambda_{t,i}(s) -> (1+s)^(-d/2).
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35])
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def Zloc(i, u):
    lim = 14 / np.sqrt(u * lam[i]) + abs(u0[i]) + 2
    return quad(lambda x: np.exp(-u * ell(i, x) - g * (x - u0[i])**2 / 2), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
def Lam_direct(i, t, s):
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    Z = quad(dens, -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
    return quad(lambda x: np.exp(-s * t * ell(i, x)) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
for s in [-0.5, 0.5, 1.0, 3.0]:
    print(f"s = {s}: target (1+s)^-1/2 = {(1+s)**-0.5:.6f}, E2 target (1+s)^-1 = {(1+s)**-1:.6f}")
    for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
        r = [Zloc(i, (1 + s) * t) / Zloc(i, t) for i in range(2)]
        d = [Lam_direct(i, t, s) for i in range(2)]
        err = [t * (r[i] - (1 + s)**-0.5) for i in range(2)]
        print(f"  t={t:5.0f}: Lambda = {r[0]:.6f}, {r[1]:.6f}  (direct {d[0]:.6f}, {d[1]:.6f})   t*(Lambda - target) = {err[0]:.4f}, {err[1]:.4f}   E2 prod = {r[0]*r[1]:.6f}, t*(prod - target) = {t*(r[0]*r[1]-(1+s)**-1):.4f}")
