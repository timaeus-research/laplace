"""Tide 96 numerical check: the anchored Gaussian *variance* gap is governed by 2 C1'.

Tilted Gaussian N(m, P^{-1}), P = tH + gI, m = P^{-1} v, a = U^T v: for Q = 1/2 u^T H u,
  Var(Q) = 1/2 tr((H P^{-1})^2) + m^T H P^{-1} H m,  so
  t^2 Var_anch(Q) = 1/2 sum (t lam_i/(t lam_i+g))^2 + t^2 sum lam_i^2 a_i^2/(t lam_i+g)^3
                  = d/2 + (sum a_i^2/lam_i - g sum 1/lam_i)/t + O(t^-2).
Exact localised anharmonic (tide 87): t^2 Var_loc(L) = d/2 + 2 sum e1_i / t + O(t^-2).
Gap: t^2 Var_loc(L) - t^2 Var_anch(Q) = 2 C1'/t + O(t^-2).
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0
e1 = (a**2 - g) / (2 * lam) - a * alpha / (2 * lam**2) - gamma / (8 * lam**2) + 5 * alpha**2 / (24 * lam**3)
e0 = 5 * alpha**2 / (24 * lam**3) - gamma / (8 * lam**2); C1p = np.sum(e0 - a * alpha / (2 * lam**2)); d = 2
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def moments_loc(i, t):
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    Z = quad(dens, -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
    m1 = quad(lambda x: ell(i, x) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
    m2 = quad(lambda x: ell(i, x)**2 * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
    return m1, m2 - m1**2
def var_gauss_direct(i, t):
    p = t * lam[i] + g; m = a[i] / p; lim = 14 / np.sqrt(p) + abs(m) + 1
    dens = lambda x: np.exp(-p * x**2 / 2 + a[i] * x)
    Z = quad(dens, -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
    q = lambda x: lam[i] * x**2 / 2
    m1 = quad(lambda x: q(x) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
    m2 = quad(lambda x: q(x)**2 * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
    return m2 - m1**2
print(f"C1' = {C1p:.6f}; 2C1' = {2*C1p:.6f}; anchored-variance 1/t coefficient sum a^2/lam - g sum 1/lam = {np.sum(a**2/lam) - np.sum(g/lam):.6f}")
t = 50.0
Vf = 0.5 * np.sum((t * lam / (t * lam + g))**2) + t**2 * np.sum(lam**2 * a**2 / (t * lam + g)**3)
Vd = t**2 * sum(var_gauss_direct(i, t) for i in range(2))
print(f"t={t}: t^2 Var_anch formula = {Vf:.10f}   direct Gaussian integral = {Vd:.10f}")
for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
    Vloc = t**2 * sum(moments_loc(i, t)[1] for i in range(2))
    Vanch = 0.5 * np.sum((t * lam / (t * lam + g))**2) + t**2 * np.sum(lam**2 * a**2 / (t * lam + g)**3)
    print(f"t={t:5.0f}: t^2Var_loc = {Vloc:.6f}  t^2Var_anch = {Vanch:.6f}   t(Var_anch - d/2) = {t*(Vanch - d/2):.5f}   t(Var_loc - Var_anch) = {t*(Vloc - Vanch):.5f}   t^2 rem = {t**2*(Vloc - Vanch - 2*C1p/t):.4f}")
