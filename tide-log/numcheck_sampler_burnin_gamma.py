"""Tide 92 numerical check: the burn-in Gamma law of the ULA-sampled LLC statistic.

ULA chain from the mode on the Gaussian target with precision P = tH: x_{k+1} = (I - hP) x_k + sqrt(2h) xi.
Claim: the law at step k is N(0, Sigma_k) with Sigma_k = S (I - A^{2k}), S = (P - (h/2)P^2)^{-1}, A = I - hP, and the Laplace transform of
X = t/2 x^T H x is prod_i (1 + s (1 - rho_i^{2k}) / (1 - h p_i/2))^(-1/2), rho_i = 1 - h p_i, p_i = t lam_i:
a sum of independent Gamma(1/2, rate (1 - h p_i/2)/(1 - rho_i^{2k})); mean 1/2 sum (1 - rho_i^{2k})/(1 - h p_i/2).
Monte Carlo with 10^6 chains, d = 3.
"""
import numpy as np
rng = np.random.default_rng(2)
d, t, h = 3, 2.0, 0.05
A0 = rng.normal(size=(d, d)); H = A0 @ A0.T + 0.5 * np.eye(d); lam = np.linalg.eigvalsh(H); p = t * lam; rho = 1 - h * p
P = t * H; Astep = np.eye(d) - h * P
n = 1_000_000
x = np.zeros((n, d))
def X(x): return 0.5 * t * np.einsum('ni,ij,nj->n', x, H, x)
S = np.linalg.inv(P - h / 2 * P @ P)
print("h p_max =", h * p.max(), " rho =", rho)
for k in range(1, 41):
    x = x @ Astep.T + np.sqrt(2 * h) * rng.normal(size=(n, d))
    if k in (1, 2, 5, 10, 20, 40):
        Sk = S @ (np.eye(d) - np.linalg.matrix_power(Astep, 2 * k))
        v = X(x)
        for s in (1.0, 3.0):
            mc = np.exp(-s * v).mean(); se = np.exp(-s * v).std() / np.sqrt(n)
            pred = np.prod((1 + s * (1 - rho ** (2 * k)) / (1 - h * p / 2)) ** -0.5)
            det = np.sqrt(np.linalg.det(np.linalg.inv(Sk)) / np.linalg.det(np.linalg.inv(Sk) + s * P))
            print(f"k={k:2d} s={s}: MC = {mc:.5f} ± {se:.5f}   product formula = {pred:.5f}   det formula = {det:.5f}")
        print(f"      mean X: MC = {v.mean():.5f}   formula 1/2 sum (1-rho^2k)/(1-hp/2) = {0.5*np.sum((1-rho**(2*k))/(1-h*p/2)):.5f}   stationary ula_llc = {0.5*np.sum(1/(1-h*p/2)):.5f}")
