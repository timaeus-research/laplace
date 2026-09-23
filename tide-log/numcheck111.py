"""Tide 111: non-stationary autocovariance of q(X_s)=½uᵀHu along ULA from a fixed start, and the fixed-n post-burn-in average."""
import numpy as np
lam = np.array([1.0, 2.5, 0.7]); eta = 0.3; g = 0.7; d = 3
rng = np.random.default_rng(11); wh = rng.normal(size=d); xh0 = rng.normal(size=d) * 2
r_inf = np.max(np.abs(1 - eta * lam)); kcrit = 1 / (2 * np.log(1 / r_inf)); kappa = 1.5 * kcrit
alpha = 1 - eta * lam; a = 1 - eta * lam / 2
def moments(t, s):
    h = eta / t; p = t * lam + g; rho = 1 - h * p; sig2 = 1 / (p * (1 - h * p / 2))
    v = sig2 * (1 - rho ** (2 * s)); mh = g * wh / p; mu = mh + rho ** s * (xh0 - mh)
    return rho, v, mu, mh
def autocov(t, s, l):
    """closed form: ½∑λ²v_s²ρ^{2l} + ∑λ²v_sρ^l μ_s μ_{s+l}"""
    rho, v, mu, mh = moments(t, s); _, _, mu2, _ = moments(t, s + l)
    return 0.5 * np.sum(lam**2 * v**2 * rho ** (2 * l)) + np.sum(lam**2 * v * rho**l * mu * mu2)
def autocov_mc(t, s, l, N=400000):
    """Monte Carlo check of the closed form: simulate the frame chain from x̂₀ for s+l steps."""
    h = eta / t; p = t * lam + g; rho = 1 - h * p; mh = g * wh / p
    X = np.tile(xh0, (N, 1))
    for step in range(s + l):
        X = mh + rho * (X - mh) + np.sqrt(2 * h) * rng.normal(size=X.shape)
        if step == s - 1: Xs = X.copy()
    qs = 0.5 * np.sum(lam * Xs**2, axis=1); ql = 0.5 * np.sum(lam * X**2, axis=1)
    return np.mean(qs * ql) - np.mean(qs) * np.mean(ql)
t = 50.0; s = 6
print("closed form vs Monte Carlo (t=50, s=6): lag  closed   MC")
for l in [0, 1, 2, 4]:
    print(f"   {l}   {autocov(t, s, l):.5f}  {autocov_mc(t, s, l):.5f}")
def Fn(n, z): return (n + 2 * sum((n - (j + 1)) * z ** (j + 1) for j in range(n))) / n**2
n = 5
V = 0.5 * np.sum(a ** -2); b = eta / 4 * np.sum(lam / a)
limit_avg_var = 0.5 * np.sum(a ** -2 * Fn(n, alpha**2))
print(f"limits: c_l^inf = ½∑a⁻²α^{{2l}}: ", [round(0.5 * np.sum(a**-2 * alpha ** (2 * l)), 5) for l in range(4)], f" avg var(n={n}) -> {limit_avg_var:.5f}  MSE -> {b**2 + limit_avg_var:.5f}")
for t in [1e2, 1e3, 1e4, 1e5, 1e6]:
    k = int(np.ceil(kappa * np.log(t)))
    c = [t**2 * autocov(t, k, l) for l in range(4)]
    avgvar = (sum(autocov(t, k + aa, 0) for aa in range(n)) + 2 * sum(autocov(t, k + aa, j + 1) for j in range(n) for aa in range(n - (j + 1)))) / n**2
    # bias of the average
    biases = []
    for aa in range(n):
        rho, v, mu, mh = moments(t, k + aa); p = t * lam + g
        Eq = 0.5 * np.sum(lam * v) + 0.5 * np.sum(lam * mu**2); L = 0.5 * np.sum(t * lam / p) / t + 0.5 * np.sum(lam * mh**2)
        biases.append(t * (Eq - L))
    bavg = np.mean(biases)
    print(f"  t={t:8.0e} k={k:3d}  t^2 c_l = {[round(x, 5) for x in c]}  t^2 avgVar={t**2 * avgvar:.5f}  t*avgBias={bavg:.5f}  t^2 MSE={t**2 * avgvar + bavg**2:.5f}")
