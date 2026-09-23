"""Tide 94 numerical check: the anchored Gaussian prediction and its gap to the exact localised law.

Anchored (E3, tilted) Gaussian: precision Q = tH + gI, tilt v = g u0 (frame coordinates), i.e. N(m, Q^-1) with m_i = a_i/(t lam_i + g), a_i = g u0_i.
Its scaled-energy transform (exact): Lambda^{G,anch}_t(s) = Lambda^G_t(s) * exp( sum_i (a_i^2/2) (1/((1+s) t lam_i + g) - 1/(t lam_i + g)) ).
Expansion: Lambda^{G,anch} = (1+s)^(-d/2) (1 + s (g sum 1/(2lam_i) - sum a_i^2/(2 lam_i)) / ((1+s) t)) + O(t^-2).
Gap to the exact anharmonic law: Lambda - Lambda^{G,anch} = -(1+s)^(-d/2) s C1'/((1+s) t) + O(t^-2),
   C1' = C1 - sum a_i^2/(2 lam_i) = sum_i (e0_i - a_i alpha_i/(2 lam_i^2)),  e0 = 5 alpha^2/(24 lam^3) - gamma/(8 lam^2)  (purely anharmonic).
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0
e1 = (a**2 - g) / (2 * lam) - a * alpha / (2 * lam**2) - gamma / (8 * lam**2) + 5 * alpha**2 / (24 * lam**3)
e0 = 5 * alpha**2 / (24 * lam**3) - gamma / (8 * lam**2)
C1 = np.sum(e1 + g / (2 * lam)); C1p = C1 - np.sum(a**2 / (2 * lam)); d = 2
print(f"C1 = {C1:.6f}, sum a^2/(2lam) = {np.sum(a**2/(2*lam)):.6f}, C1' = {C1p:.6f}, check sum(e0 - a alpha/(2 lam^2)) = {np.sum(e0 - a*alpha/(2*lam**2)):.6f}")
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def Zloc(i, u):
    lim = 14 / np.sqrt(u * lam[i]) + abs(u0[i]) + 2
    return quad(lambda x: np.exp(-u * ell(i, x) - g * (x - u0[i])**2 / 2), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
def Zgauss_anch(i, u):  # exact Gaussian integral with quadratic energy lam x^2/2 and the same localiser
    lim = 14 / np.sqrt(u * lam[i]) + abs(u0[i]) + 2
    return quad(lambda x: np.exp(-u * lam[i] * x**2 / 2 - g * (x - u0[i])**2 / 2), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
for s in [-0.5, 1.0, 3.0]:
    A = 1 + s
    coefG = s * (np.sum(g / (2 * lam)) - np.sum(a**2 / (2 * lam))) / A**(d / 2 + 1)
    print(f"s = {s}: anchored-Gaussian 1/t coeff predicted = {coefG:.6f};  gap coeff -s C1'/A^(d/2+1) = {-s*C1p/A**(d/2+1):.6f}")
    for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
        anh = np.prod([Zloc(i, A * t) / Zloc(i, t) for i in range(2)])
        gau = np.prod(np.sqrt((t * lam + g) / (A * t * lam + g)))
        expf = np.exp(np.sum(a**2 / 2 * (1 / (A * t * lam + g) - 1 / (t * lam + g))))
        anch = gau * expf
        anch_direct = np.prod([Zgauss_anch(i, A * t) / Zgauss_anch(i, t) for i in range(2)])
        print(f"  t={t:5.0f}: anch formula = {anch:.6f} (direct {anch_direct:.6f})   t(anch - A^-d/2) = {t*(anch - A**(-d/2)):.5f}   t(Lambda - anch) = {t*(anh - anch):.5f}   t^2 rem = {t**2*(anh - anch + s*C1p/(A**(d/2+1)*t)):.4f}")
