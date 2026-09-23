"""Tide 100 numerical check: variance of the k-step ULA anchored statistic and the stationary limits.
Var_k(t 1/2 u^T H u) = t^2/2 sum (lam_i v_i)^2 + t^2 sum v_i (lam_i mu_i)^2,  v_i = f_i/(p_i kappa_i), mu_i = b_i + rho_i^k (z_i - b_i), b_i = a_i/p_i.
Stationary: t E_inf = t/2 sum lam/(p kappa) + t/2 sum lam b^2;  budget_inf = C1'/t - (th/4) sum lam/kappa.
"""
import numpy as np
lam = np.array([1.3, 0.9]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0; x0 = np.array([0.9, -0.6]); t = 40.0; eta = 0.3; h = eta / t; k = 3
p = t * lam + g; kap = 1 - h * p / 2; rho = 1 - h * p; f = 1 - rho**(2 * k); v = f / (p * kap); b = a / p; mu = b + rho**k * (x0 - b)
var_f = t**2 / 2 * np.sum((lam * v)**2) + t**2 * np.sum(v * (lam * mu)**2)
rng = np.random.default_rng(11); N = 400000; x = np.tile(x0, (N, 1))
for _ in range(k): x = x - h * (x - b) * p + np.sqrt(2 * h) * rng.normal(size=x.shape)
E = t * 0.5 * np.sum(lam * x**2, axis=1)
print(f"k={k}: MC mean {E.mean():.5f} var {E.var():.5f};  formula var {var_f:.5f}")
for kk in [1, 3, 10, 30, 100, 300]:
    ff = 1 - rho**(2 * kk); vv = ff / (p * kap); mm = b + rho**kk * (x0 - b)
    Ek = t / 2 * np.sum(lam * vv) + t / 2 * np.sum(lam * mm**2); burn = t / 2 * np.sum(lam * rho**(2 * kk) / (p * kap)) - t / 2 * np.sum(lam * (mm**2 - b**2))
    print(f"k={kk:4d}: tE_k = {Ek:.5f}  burn = {burn:.6f}  var = {t**2/2*np.sum((lam*vv)**2) + t**2*np.sum(vv*(lam*mm)**2):.5f}")
print(f"stationary: tE_inf = {t/2*np.sum(lam/(p*kap)) + t/2*np.sum(lam*b**2):.5f}, var_inf = {t**2/2*np.sum((lam/(p*kap))**2) + t**2*np.sum(lam**2*b**2/(p*kap)):.5f}, disc = {(t*h/4)*np.sum(lam/kap):.5f}")
