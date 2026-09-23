"""Tide 113: growing window n(t) -> inf: n t^2 avgVar(k(t), n(t)) -> L_eta; average bias -> b_eta."""
import numpy as np
lam = np.array([1.0, 2.5, 0.7]); eta = 0.3; g = 0.7; d = 3
rng = np.random.default_rng(13); wh = rng.normal(size=d); xh0 = rng.normal(size=d) * 2
r_inf = np.max(np.abs(1 - eta * lam)); kcrit = 1 / (2 * np.log(1 / r_inf)); kappa = 1.5 * kcrit
alpha = 1 - eta * lam; a = 1 - eta * lam / 2
Leta = np.sum((1 + alpha**2) / (4 * eta * lam * a**3)); beta = eta / 4 * np.sum(lam / a)
def moments(t, s):
    h = eta / t; p = t * lam + g; rho = 1 - h * p; sig2 = 1 / (p * (1 - h * p / 2))
    return rho, sig2 * (1 - rho ** (2 * s)), g * wh / p + rho ** s * (xh0 - g * wh / p), g * wh / p
def autocov(t, s, l):
    rho, v, mu, mh = moments(t, s); _, _, mu2, _ = moments(t, s + l)
    return 0.5 * np.sum(lam**2 * v**2 * rho ** (2 * l)) + np.sum(lam**2 * v * rho**l * mu * mu2)
def avgvar(t, k, n):
    # closed-form double sum using per-lag geometric structure (vectorised over a)
    tot = sum(autocov(t, k + aa, 0) for aa in range(n))
    for j in range(n):
        tot += 2 * sum(autocov(t, k + aa, j + 1) for aa in range(n - (j + 1)))
    return tot / n**2
print(f"L_eta={Leta:.6f}  b_eta={beta:.6f}")
for t, nfun in [(1e2, lambda t: int(np.ceil(np.sqrt(t)))), (1e3, lambda t: int(np.ceil(np.sqrt(t)))), (1e4, lambda t: int(np.ceil(np.sqrt(t)))), (1e5, lambda t: int(np.ceil(np.sqrt(t))))]:
    k = int(np.ceil(kappa * np.log(t))); n = nfun(t)
    av = avgvar(t, k, n)
    biases = []
    for aa in range(n):
        rho, v, mu, mh = moments(t, k + aa); p = t * lam + g
        Eq = 0.5 * np.sum(lam * v) + 0.5 * np.sum(lam * mu**2); L = 0.5 * np.sum(t * lam / p) / t + 0.5 * np.sum(lam * mh**2)
        biases.append(t * (Eq - L))
    print(f"  t={t:8.0e} k={k:3d} n={n:4d}  n t^2 avgVar = {n * t**2 * av:.5f}   t*avgBias = {np.mean(biases):.5f}   t^2 MSE = {t**2 * av + np.mean(biases)**2:.5f} -> b^2 = {beta**2:.5f}")
