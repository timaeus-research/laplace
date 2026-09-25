"""Tide 117 (fulllaw-frame): exact full law when the D_i share the Hessian eigenframe, and its anchored-scaling slope."""
import numpy as np
rng = np.random.default_rng(17)
d, n = 3, 2
Q, _ = np.linalg.qr(rng.standard_normal((d, d)))
lam = np.array([1.0, 2.0, 0.5]); eta, g, c = 0.3, 0.5, 0.05
M = rng.standard_normal((d, d)); C = M @ M.T / d
Chat = np.diag(Q.T @ C @ Q)
dv = 0.8 * rng.standard_normal((n, d))                     # D_i = Q diag(dv_i) Q^T
D = [Q @ np.diag(dv[i]) @ Q.T for i in range(n)]
v = (dv ** 2).sum(axis=0)
alpha = 1 - eta * lam; s = 1 - alpha ** 2
q = c * v / s; w = 0.5 * lam * eta ** 2 * Chat / s
assert (q < 1).all(), q
def frame_fixed(t):
    h = eta / t; p = t * lam + g; rho = 1 - h * p
    N = 2 * h * np.eye(d) + h ** 2 * t ** 2 * C
    Nhat = Q.T @ N @ Q
    den = 1 - rho[:, None] * rho[None, :] - c * dv.T @ dv
    return Q @ (Nhat / den) @ Q.T, rho, N
def full_step(X, A, N):
    return A @ X @ A.T + N + c * sum(Di @ X @ Di.T for Di in D)
t = 1e3
S, rho, N = frame_fixed(t)
A = Q @ np.diag(rho) @ Q.T
print("fixed-point residual of the closed form:", np.abs(full_step(S, A, N) - S).max())
X = np.zeros((d, d))
for _ in range(20000): X = full_step(X, A, N)
print("iteration vs closed form:", np.abs(X - S).max())
linf = lambda B: np.abs(B).sum(axis=1).max()
L = linf(A) * linf(A.T) + c * sum(linf(Di) * linf(Di.T) for Di in D)
print("fullLipschitz (ell-infty) at t=1e3:", round(L, 4), "(<1 needed for fullFixed)")
H = Q @ np.diag(lam) @ Q.T
def llc_frame(t):
    S, rho, N = frame_fixed(t); return t / 2 * np.trace(H @ S)
def llc_ula(t):
    h = eta / t; p = t * lam + g; return t / 2 * (lam / (p * (1 - h * p / 2))).sum()
sig_full = (w / (1 - q)).sum(); sig_first = (w * (1 + q)).sum()
sig_mb = eta / 4 * (Chat / (1 - eta * lam / 2)).sum()
sig1 = 0.5 * c * (lam * v * eta ** 2 * Chat / s ** 2).sum()
print(f"sigma_full = sum w/(1-q) = {sig_full:.6f};  sigma_mb + sigma_1 = {sig_mb + sig1:.6f} = sum w(1+q) = {sig_first:.6f}")
print(f"deficit sum w q^2/(1-q) = {(w * q**2 / (1 - q)).sum():.6f}  vs  sigma_full - (sigma_mb+sigma_1) = {sig_full - sig_mb - sig1:.6f}")
print("q =", np.round(q, 4), " w =", np.round(w, 4))
for t in [1e1, 1e2, 1e3, 1e4, 1e5]:
    print(f"  t={t:8.0e}  (LLC_frame - LLC_ula)/t = {(llc_frame(t) - llc_ula(t)) / t:.6f}")
