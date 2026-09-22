"""Tide 82 numerical check: Frobenius discrepancies of E2's exact localised covariance C(t).

(a) t^4 ||C - S||_F^2 -> sum_i (v_i + g/lam_i^2)^2   (S = (tH + gI)^{-1}, the Gaussian-prior resolvent),
(b) t^4 ||C - H^{-1}/t||_F^2 -> sum_i v_i^2          (the localiser's gH^{-2} term drops out),
(c) t^2 ||C - S||_F^2 / ||S||_F^2 -> ||W||_F^2 / ||H^{-1}||_F^2  (the note's relative O(S^2) made quantitative).
"""
import numpy as np
from scipy.integrate import quad

lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8
th = 0.6; Q = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
c = np.array([0.3, -0.2]); w0 = np.array([0.9, 0.4]); u0 = Q.T @ (w0 - c)
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24

def frame_var(i, t):
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    lim = 12 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    Z = quad(dens, -lim, lim, epsabs=1e-15, epsrel=1e-14)[0]
    E = lambda f: quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-15, epsrel=1e-14)[0] / Z
    m1 = E(lambda x: x); return E(lambda x: x**2) - m1**2

c1 = -alpha / (2 * lam**2) + g * u0 / lam
c2p = (5 * alpha**2 / (4 * lam**4) - gamma / (2 * lam**3) - 2 * g * u0 * alpha / lam**3 + (g**2 * u0**2 - g) / lam**2)
v = c2p - c1**2; wcoef = v + g / lam**2
Hinv = Q @ np.diag(1 / lam) @ Q.T
print(f"sum (v_i + g/lam_i^2)^2 = {np.sum(wcoef**2):.8f}   sum v_i^2 = {np.sum(v**2):.8f}   ratio limit = {np.sum(wcoef**2)/np.sum(1/lam**2):.8f}")
for t in [80.0, 160.0, 320.0, 640.0, 1280.0]:
    C = Q @ np.diag([frame_var(i, t) for i in range(2)]) @ Q.T
    S = Q @ np.diag(1 / (t * lam + g)) @ Q.T
    fa = t**4 * np.sum((C - S)**2); fb = t**4 * np.sum((C - Hinv / t)**2); fc = t**2 * np.sum((C - S)**2) / np.sum(S**2)
    print(f"t={t:6.0f}: t^4|C-S|^2 = {fa:.6f} (t*resid {t*(fa-np.sum(wcoef**2)):.4f})   t^4|C-Hinv/t|^2 = {fb:.6f} (t*resid {t*(fb-np.sum(v**2)):.4f})   ratio = {fc:.6f} (t*resid {t*(fc-np.sum(wcoef**2)/np.sum(1/lam**2)):.4f})")
