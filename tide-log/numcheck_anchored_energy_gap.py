"""Tide 95 numerical check: the anchored Gaussian *energy* gap is governed by the same C1'.

E3's anchored Gaussian scaled energy: E^{anch}_t = 1/2 sum t lam_i/(t lam_i + g) + (t/2) sum lam_i a_i^2/(t lam_i + g)^2
  = d/2 + (sum a_i^2/(2 lam_i) - g sum 1/(2 lam_i))/t + O(t^-2).
Exact localised anharmonic scaled energy (tide 73): t <L>_loc = d/2 + sum e1_i / t + O(t^-2).
Gap: t<L>_loc - E^{anch}_t = C1'/t + O(t^-2), C1' = sum (e1_i + g/(2 lam_i) - a_i^2/(2 lam_i)) = sum (e0_i - a_i alpha_i/(2 lam_i^2)).
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0
e1 = (a**2 - g) / (2 * lam) - a * alpha / (2 * lam**2) - gamma / (8 * lam**2) + 5 * alpha**2 / (24 * lam**3)
e0 = 5 * alpha**2 / (24 * lam**3) - gamma / (8 * lam**2); C1p = np.sum(e0 - a * alpha / (2 * lam**2)); d = 2
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def Eloc(i, t):
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    Z = quad(dens, -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
    return quad(lambda x: ell(i, x) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
print(f"C1' = {C1p:.6f}; anchored-energy 1/t coefficient sum a^2/(2lam) - g sum 1/(2lam) = {np.sum(a**2/(2*lam)) - np.sum(g/(2*lam)):.6f}")
for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
    tL = t * sum(Eloc(i, t) for i in range(2))
    Eanch = 0.5 * np.sum(t * lam / (t * lam + g)) + t / 2 * np.sum(lam * a**2 / (t * lam + g)**2)
    print(f"t={t:5.0f}: t<L> = {tL:.6f}  E^anch = {Eanch:.6f}   t(E^anch - d/2) = {t*(Eanch - d/2):.5f}   t(t<L> - E^anch) = {t*(tL - Eanch):.5f}   t^2 rem = {t**2*(tL - Eanch - C1p/t):.4f}")
