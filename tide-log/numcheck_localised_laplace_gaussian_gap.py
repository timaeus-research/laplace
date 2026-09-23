"""Tide 93 numerical check: the transform-level Gaussian-vs-anharmonic discrepancy is governed by C1.

Gaussian (E3) prediction for the localised transform: Lambda^G_t(s) = prod_i sqrt((t lam_i + g)/((1+s) t lam_i + g))
  = (1+s)^(-d/2) (1 + s g sum_i 1/(2 lam_i) / ((1+s) t)) + O(t^-2).
Anharmonic E2 (tide 90): Lambda_t(s) = (1+s)^(-d/2) (1 - s sum e1_i /((1+s) t)) + O(t^-2).
Difference: Lambda - Lambda^G = -(1+s)^(-d/2) s C1 / ((1+s) t) + O(t^-2),  C1 = sum_i (e1_i + g/(2 lam_i))  (tides 85/87's coefficient).
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0
e1 = (a**2 - g) / (2 * lam) - a * alpha / (2 * lam**2) - gamma / (8 * lam**2) + 5 * alpha**2 / (24 * lam**3)
C1 = np.sum(e1 + g / (2 * lam)); d = 2
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def Zloc(i, u):
    lim = 14 / np.sqrt(u * lam[i]) + abs(u0[i]) + 2
    return quad(lambda x: np.exp(-u * ell(i, x) - g * (x - u0[i])**2 / 2), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
print(f"C1 = {C1:.6f}  (sum e1 = {e1.sum():.6f}, g sum 1/(2 lam) = {np.sum(g/(2*lam)):.6f})")
for s in [-0.5, 1.0, 3.0]:
    A = 1 + s
    print(f"s = {s}: predicted t*(Lambda - Lambda^G) -> -s C1/A^(d/2+1) = {-s*C1/A**(d/2+1):.6f};  Gaussian 1/t coeff s g sum 1/(2lam)/A^(d/2+1) = {s*np.sum(g/(2*lam))/A**(d/2+1):.6f}")
    for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
        anh = np.prod([Zloc(i, A * t) / Zloc(i, t) for i in range(2)])
        gau = np.prod(np.sqrt((t * lam + g) / (A * t * lam + g)))
        print(f"  t={t:5.0f}: Lambda = {anh:.6f}  Lambda^G = {gau:.6f}   t(Lambda - Lambda^G) = {t*(anh-gau):.5f}   t(Lambda^G - A^-d/2) = {t*(gau - A**(-d/2)):.5f}   t^2 rem = {t**2*(anh - gau + s*C1/(A**(d/2+1)*t)):.4f}")
