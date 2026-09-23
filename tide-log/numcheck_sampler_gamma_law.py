"""Tide 91 numerical check: the Laplace transform of the Gaussian LLC statistic under centred Gaussian laws.

Claim (exact): for precision Q (PosDef) and H symmetric with Q + s tH PosDef,
  E_{N(0,Q^-1)}[exp(-s * t/2 * x^T H x)] = sqrt(det Q / det(Q + s t H)).
Localised Gibbs target Q = tH + gamma I: prod_i (1 + s t lam_i/(t lam_i + gamma))^(-1/2); gamma = 0: (1+s)^(-d/2).
ULA law Q = P - (h/2) P^2, P = tH: prod_i (1 + s/(1 - h p_i/2))^(-1/2)  (sum of independent Gamma(1/2, rate 1 - h p_i/2)).
Localised ULA law Q = P_g - (h/2) P_g^2, P_g = tH + gamma I: prod_i (1 + s t lam_i/(a_i (1 - h a_i/2)))^(-1/2), a_i = t lam_i + gamma.
Monte Carlo with 2*10^6 samples in d = 3.
"""
import numpy as np
rng = np.random.default_rng(1)
d, t, gamma, h = 3, 2.0, 0.7, 0.15
A = rng.normal(size=(d, d)); H = A @ A.T + 0.5 * np.eye(d)
lam, U = np.linalg.eigh(H); P = t * H
def mc(Q, s, n=2_000_000):
    L = np.linalg.cholesky(np.linalg.inv(Q)); z = rng.normal(size=(n, d)); x = z @ L.T
    q = 0.5 * np.einsum('ni,ij,nj->n', x, H, x)
    v = np.exp(-s * t * q); return v.mean(), v.std() / np.sqrt(n)
for name, Q, pred in [
    ("Gibbs gamma=0", P, lambda s: (1 + s) ** (-d / 2)),
    ("localised Gibbs", P + gamma * np.eye(d), lambda s: np.prod((1 + s * t * lam / (t * lam + gamma)) ** -0.5)),
    ("ULA law", P - h / 2 * P @ P, lambda s: np.prod((1 + s / (1 - h * t * lam / 2)) ** -0.5)),
    ("localised ULA law", (P + gamma * np.eye(d)) - h / 2 * (P + gamma * np.eye(d)) @ (P + gamma * np.eye(d)),
     lambda s: np.prod((1 + s * t * lam / ((t * lam + gamma) * (1 - h * (t * lam + gamma) / 2))) ** -0.5)),
]:
    print(f"== {name}: eig(Q) = {np.linalg.eigvalsh(Q)}")
    for s in [0.5, 1.0, 3.0]:
        m, se = mc(Q, s); det = np.sqrt(np.linalg.det(Q) / np.linalg.det(Q + s * P))
        print(f"   s={s}: MC = {m:.5f} ± {se:.5f}   det formula = {det:.5f}   product formula = {pred(s):.5f}")
print("h p_max/2 =", h * t * lam.max() / 2, " (stability h p < 2)")
