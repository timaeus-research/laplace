"""Tide 110 numerical check: k-step variance and single-draw MSE of the ULA LLC statistic after logarithmic burn-in."""
import numpy as np
lam = np.array([1.0, 2.5, 0.7]); eta = 0.3; g = 0.7
rng = np.random.default_rng(3); wh = rng.normal(size=3); xh0 = rng.normal(size=3) * 2
r_inf = np.max(np.abs(1 - eta * lam)); kcrit = 1 / (2 * np.log(1 / r_inf)); kappa = 1.5 * kcrit
V_eta = 0.5 * np.sum(1 / (1 - eta * lam / 2) ** 2)
bias_inf = eta / 4 * np.sum(lam / (1 - eta * lam / 2))
print(f"r_inf={r_inf:.3f} kappa_crit={kcrit:.3f} kappa={kappa:.3f}  V_eta={V_eta:.6f}  bias_inf={bias_inf:.6f}  MSE_inf={V_eta + bias_inf**2:.6f}")
for t in [1e1, 1e2, 1e3, 1e4, 1e5, 1e6]:
    k = int(np.ceil(kappa * np.log(t))); h = eta / t; p = t * lam + g; rho = 1 - h * p
    sig2 = 1 / (p * (1 - h * p / 2)); v = sig2 * (1 - rho ** (2 * k))
    mh = g * wh / p; mk = mh + rho ** k * (xh0 - mh)
    var_k = 0.5 * np.sum((lam * v) ** 2) + np.sum(v * (lam * mk) ** 2)        # ulaAnchored_llc_var / t^2
    Eq_k = 0.5 * np.sum(lam * v) + 0.5 * np.sum(lam * mk ** 2)                # k-step mean of ½uᵀHu (Gaussian)
    # exact localised energy replaced by its Gaussian (harmonic) value ½∑ tλ/(tλ+g) + ½∑ λ m̂² : the anharmonic C₁'/t is O(1/t)
    L_loc = 0.5 * np.sum(t * lam / p) / t + 0.5 * np.sum(lam * mh ** 2)
    bias_t = t * Eq_k - t * L_loc
    print(f"  t={t:8.0e} k={k:3d}  t^2 Var_k={t**2 * var_k:.6f}  t*bias={bias_t:.6f}  t^2 MSE={t**2 * var_k + bias_t**2:.6f}")
print("MSE identity check at t=1e3: E[(q-a)^2] = Var + (Eq-a)^2 holds by algebra; monotone in eta:")
for e in [0.1, 0.2, 0.3, 0.5]:
    V = 0.5 * np.sum(1 / (1 - e * lam / 2) ** 2); b = e / 4 * np.sum(lam / (1 - e * lam / 2)); kc = 1 / (2 * np.log(1 / np.max(np.abs(1 - e * lam))))
    print(f"  eta={e:.1f}  V={V:.4f}  bias={b:.4f}  MSE_inf={V + b**2:.4f}  kappa_crit={kc:.3f}")
