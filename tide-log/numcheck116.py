"""Tide 116: the first-order Hessian-fluctuation LLC correction grows linearly in t at h = η/t; explicit slope."""
import numpy as np
rng = np.random.default_rng(116); d = 3; nS = 4
lam = np.array([1.0, 2.5, 0.7]); eta = 0.3; g = 0.7; m = 2
Qm, _ = np.linalg.qr(rng.normal(size=(d, d))); H = Qm @ np.diag(lam) @ Qm.T
Hs = [H + 0.4 * (lambda M: M @ M.T)(rng.normal(size=(d, d))) for _ in range(nS)]; Hbar = sum(Hs) / nS; D = [Hi - Hbar for Hi in Hs]
Cg = (lambda M: M @ M.T)(rng.normal(size=(d, d))) * 0.3
alpha_c = (1 - m / nS) / (m * (nS - 1)); c = eta**2 * alpha_c
Dh = [Qm.T @ Di @ Qm for Di in D]; Ch = Qm.T @ Cg @ Qm
al = 1 - eta * lam
S_inf = eta**2 * Ch / (1 - np.outer(al, al))
slope1 = 0.5 * c * sum(lam[j] / (eta * lam[j] * (2 - eta * lam[j])) * sum((Dh_i @ S_inf @ Dh_i.T)[j, j] for Dh_i in Dh) for j in range(d))
slope_mb = eta / 4 * sum(Ch[j, j] / (1 - eta * lam[j] / 2) for j in range(d))
print(f"predicted slopes: first-order fluctuation {slope1:.6f}   constant-noise inflation {slope_mb:.6f}   ratio {slope1/slope_mb:.4f}")
for t in [1e1, 1e2, 1e3, 1e4, 1e5]:
    h = eta / t; p = t * lam + g; rho = 1 - h * p
    Sh = (2 * h * np.eye(d) + h**2 * t**2 * Ch) / (1 - np.outer(rho, rho))      # frame Σ^{mb}
    corr1 = t / 2 * c * sum(lam[j] / (1 - rho[j]**2) * sum((Dh_i @ Sh @ Dh_i.T)[j, j] for Dh_i in Dh) for j in range(d))
    llc_mb = t / 2 * sum(lam * (1 + h * t**2 * np.diag(Ch) / 2) / (p * (1 - h * p / 2))); llc_ula = t / 2 * sum(lam / (p * (1 - h * p / 2)))
    print(f"  t={t:8.0e}  corr1/t = {corr1/t:.6f}   (LLC_mb − LLC_ula)/t = {(llc_mb - llc_ula)/t:.6f}")
