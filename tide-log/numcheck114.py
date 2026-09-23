"""Tide 114: full law upper bound ‖Σ_full − Σ_mb‖ ≤ c‖B(Σ_mb)‖/(1−L) in the ℓ∞ operator norm, and the LLC two-sided bound."""
import numpy as np
rng = np.random.default_rng(107); d = 3; nS = 5
lam = np.array([1.0, 2.5, 0.7]); t = 20.0; g = 0.7; h = 0.1 / t; m = 2
Qm = np.eye(d); H = np.diag(lam)  # diagonal frame so that the ℓ∞ operator norm of A = I − hP is max(1 − h pᵢ) < 1
P = t * H + g * np.eye(d); A = np.eye(d) - h * P
Hs = [H + 0.15 * (lambda M: M @ M.T)(rng.normal(size=(d, d))) for _ in range(nS)]; Hbar = sum(Hs) / nS
D = [Hi - Hbar for Hi in Hs]
Cg = (lambda M: M @ M.T)(rng.normal(size=(d, d))) * 0.3
N = 2 * h * np.eye(d) + h**2 * t**2 * Cg
c = h**2 * t**2 * (1 - m / nS) / (m * (nS - 1))
opnorm = lambda M: np.max(np.sum(np.abs(M), axis=1))
L = opnorm(A) * opnorm(A.T) + c * sum(opnorm(Di) * opnorm(Di.T) for Di in D)
def cov_step(X): return A @ X @ A.T + N
def full_step(X): return cov_step(X) + c * sum(Di @ X @ Di.T for Di in D)
S = np.zeros((d, d)); F = np.zeros((d, d))
for _ in range(20000): S = cov_step(S); F = full_step(F)
B = sum(Di @ S @ Di.T for Di in D)
lhs = opnorm(F - S); rhs = c * opnorm(B) / (1 - L)
print(f"L = {L:.4f} (<1)  ‖Σ_full − Σ_mb‖ = {lhs:.3e}  ≤  c‖B(Σ_mb)‖/(1−L) = {rhs:.3e}   ratio {lhs/rhs:.3f}")
tr = lambda M: np.trace(M)
lo = t / 2 * (tr(H @ S) + c * tr(H @ B)); hi = t / 2 * (tr(H @ S) + d * opnorm(H) * c * opnorm(B) / (1 - L)); mid = t / 2 * tr(H @ F)
print(f"LLC bounds: lower {lo:.6f} ≤ full {mid:.6f} ≤ upper {hi:.6f}")
