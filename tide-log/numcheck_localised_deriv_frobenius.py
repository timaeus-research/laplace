"""Tide 83 numerical check: Frobenius discrepancies of the localised covariance's DERIVATIVE.

(a) t^6 ||-dC/dt - H^{-1}/t^2||_F^2 -> 4 sum_i v_i^2         (tide 80: -dC/dt = H^{-1}/t^2 + 2V/t^3 + O(t^-4)),
(b) t^6 ||-dC/dt + dS/dt||_F^2      -> 4 sum_i (v_i + g/lam_i^2)^2   (-dS/dt = Q diag(lam/(t lam + g)^2) Q^T),
(c) the relative form t^2 ||-dC/dt - H^{-1}/t^2||^2 / ||H^{-1}/t^2||^2 -> 4 sum v_i^2 / sum lam_i^-2.
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

def C(t): return Q @ np.diag([frame_var(i, t) for i in range(2)]) @ Q.T
c1 = -alpha / (2 * lam**2) + g * u0 / lam
c2p = (5 * alpha**2 / (4 * lam**4) - gamma / (2 * lam**3) - 2 * g * u0 * alpha / lam**3 + (g**2 * u0**2 - g) / lam**2)
v = c2p - c1**2; wcoef = v + g / lam**2
Hinv = Q @ np.diag(1 / lam) @ Q.T
print(f"4 sum v_i^2 = {4*np.sum(v**2):.8f}   4 sum w_i^2 = {4*np.sum(wcoef**2):.8f}   relative limit = {4*np.sum(v**2)/np.sum(1/lam**2):.8f}")
for t in [80.0, 160.0, 320.0, 640.0]:
    h = t * 1e-3
    dC = -(C(t + h) - C(t - h)) / (2 * h)           # -dC/dt
    dS = Q @ np.diag(lam / (t * lam + g)**2) @ Q.T  # -dS/dt
    fa = t**6 * np.sum((dC - Hinv / t**2)**2); fb = t**6 * np.sum((dC - dS)**2)
    fc = t**2 * np.sum((dC - Hinv / t**2)**2) / np.sum((Hinv / t**2)**2)
    print(f"t={t:5.0f}: t^6|dC-Hinv/t^2|^2 = {fa:.6f} (t*resid {t*(fa-4*np.sum(v**2)):.4f})   t^6|dC-dS|^2 = {fb:.6f} (t*resid {t*(fb-4*np.sum(wcoef**2)):.4f})   rel = {fc:.6f} (t*resid {t*(fc-4*np.sum(v**2)/np.sum(1/lam**2)):.4f})")
