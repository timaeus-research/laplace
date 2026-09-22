"""Tide 84 numerical check: the localised mean's squared discrepancy from the displayed (resolvent) mean, and its derivative.

Per frame coordinate (rotation is Euclidean-invariant): mu_i(t) = <u_i>_loc, P_i(t) = -alpha t/(2(t lam+g)^2) + a/(t lam + g), a = g u0_i,
r_i = meanLocResidual2 = B1 + a alpha^2/lam^4 - a gamma/(2 lam^3) - alpha a^2/(2 lam^3),  B1 = -5 alpha^3/(8 lam^5) + 2 alpha gamma/(3 lam^4).
(a) t^4 sum_i (mu_i - P_i)^2 -> sum_i r_i^2                    (||m - m_disp||^2 = ||r||^2/t^4 + O(t^-5))
(b) -d mu_i/dt = Cov[L, u_i]; c1_i = -alpha/(2 lam^2) + a/lam; c'_i = r_i + alpha g/lam^3 - g a/lam^2 (meanLocCoeff2):
    t^6 sum_i (Cov[L,u_i] - c1_i/t^2)^2 -> 4 sum_i c'_i^2       (||d m/dt + Q c1/t^2||^2 = 4||c'||^2/t^6 + O(t^-7))
"""
import numpy as np
from scipy.integrate import quad

lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8
u0 = np.array([0.55, -0.35]); a = g * u0
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24

def moments(i, t):
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    lim = 12 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    Z = quad(dens, -lim, lim, epsabs=1e-15, epsrel=1e-14)[0]
    E = lambda f: quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-15, epsrel=1e-14)[0] / Z
    m1 = E(lambda x: x); covLx = E(lambda x: ell(i, x) * x) - E(lambda x: ell(i, x)) * m1
    return m1, covLx

B1 = -5 * alpha**3 / (8 * lam**5) + 2 * alpha * gamma / (3 * lam**4)
r = B1 + a * alpha**2 / lam**4 - a * gamma / (2 * lam**3) - alpha * a**2 / (2 * lam**3)
c1 = -alpha / (2 * lam**2) + a / lam
cp = r + alpha * g / lam**3 - g * a / lam**2
print(f"sum r_i^2 = {np.sum(r**2):.8f}    4 sum c'_i^2 = {4*np.sum(cp**2):.8f}")
for t in [80.0, 160.0, 320.0, 640.0, 1280.0]:
    mu = np.array([moments(i, t)[0] for i in range(2)]); cov = np.array([moments(i, t)[1] for i in range(2)])
    P = -alpha * t / (2 * (t * lam + g)**2) + a / (t * lam + g)
    fa = t**4 * np.sum((mu - P)**2); fb = t**6 * np.sum((cov - c1 / t**2)**2)
    print(f"t={t:6.0f}: t^4|mu-P|^2 = {fa:.8f} (t*resid {t*(fa-np.sum(r**2)):.5f})   t^6|Cov[L,u]-c1/t^2|^2 = {fb:.6f} (t*resid {t*(fb-4*np.sum(cp**2)):.4f})")
