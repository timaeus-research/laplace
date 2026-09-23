"""Tide 99 numerical check: the E2-E4 error budget for the ULA-sampled anchored LLC estimate.

E2 frame (2D): exact localised law exp(-t sum ell_i(u_i) - g/2 |u - u0|^2); E3 anchored Gaussian N(m, P^{-1}), P = tH + gI (H = diag lam),
m = P^{-1} g u0; E4 ULA on the anchored Gaussian from x0: x_{k+1} = x_k - hP(x_k - m) + sqrt(2h) xi -> N(m + A^k(x0 - m), Sigma_k).
Statistic: t * 1/2 u^T H u.  Claims:
  t E_k = t/2 sum lam_i sigma_i f_i + t/2 sum lam_i (m_k)_i^2,  sigma_i = 1/(p_i kappa_i), p_i = t lam_i + g, kappa_i = 1 - h p_i/2, f_i = 1 - rho_i^{2k},
  (m_k)_i = g u0_i/p_i + rho_i^k (x0_i - g u0_i/p_i).
  E^anch - t E_k = -(t h/4) sum lam_i/kappa_i + t/2 sum lam_i rho_i^{2k}/(p_i kappa_i) - t/2 sum lam_i [(m_k)_i^2 - (g u0_i/p_i)^2]   (exact)
  t<L>_loc - t E_k = C1'/t + [above] + O(t^-2)
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0
e0 = 5 * alpha**2 / (24 * lam**3) - gamma / (8 * lam**2); C1p = np.sum(e0 - a * alpha / (2 * lam**2)); d = 2
x0 = np.array([0.9, -0.6]); k = 3; eta = 0.3   # step size h = eta/t (beta-scaled)
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def Eloc(i, t):
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    Z = quad(dens, -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
    return quad(lambda x: ell(i, x) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
def budget(t, h):
    p = t * lam + g; kap = 1 - h * p / 2; rho = 1 - h * p; f = 1 - rho**(2 * k); sig = 1 / (p * kap); m = a / p; mk = m + rho**k * (x0 - m)
    tEk = t / 2 * np.sum(lam * sig * f) + t / 2 * np.sum(lam * mk**2)
    Eanch = 0.5 * np.sum(t * lam / p) + t / 2 * np.sum(lam * (a / p)**2)
    disc = -(t * h / 4) * np.sum(lam / kap); burn = t / 2 * np.sum(lam * rho**(2 * k) / (p * kap)) - t / 2 * np.sum(lam * (mk**2 - m**2))
    return tEk, Eanch, disc, burn, kap
# Monte Carlo of ULA on the anchored quadratic model at t = 40
t = 40.0; h = eta / t; p = t * lam + g; m = a / p; rng = np.random.default_rng(5); N = 400000
x = np.tile(x0, (N, 1))
for _ in range(k): x = x - h * (x - m) * p + np.sqrt(2 * h) * rng.normal(size=x.shape)
E_mc = t * 0.5 * np.sum(lam * x**2, axis=1).mean()
tEk, Eanch, disc, burn, kap = budget(t, h)
print(f"t={t}, h=eta/t={h:.4f}: MC t E_k = {E_mc:.5f}  formula {tEk:.5f};  identity check E^anch - tE_k = {Eanch - tEk:.6f} vs disc+burn = {disc + burn:.6f}")
print(f"C1' = {C1p:.6f}; step-size bias (th/4) sum lam/kappa = {-disc:.5f}  (-> (eta/4) sum lam/(1 - eta lam/2) = {eta/4*np.sum(lam/(1-eta*lam/2)):.5f} as t -> inf)")
for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
    h = eta / t; tL = t * sum(Eloc(i, t) for i in range(2)); tEk, Eanch, disc, burn, kap = budget(t, h)
    print(f"t={t:5.0f}: t<L> = {tL:.5f}  tE_k = {tEk:.5f}  t<L> - tE_k = {tL - tEk:.5f}  disc = {disc:.5f}  burn = {burn:.5f}   t(t<L> - tE_k - disc - burn) = {t*(tL - tEk - disc - burn):.5f} vs C1' = {C1p:.5f}")
