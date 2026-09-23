"""Tide 115: exact resolvent identity Δ = c R(B(Σ_full)), lower bound Δ ⪰ c R(B(Σ_mb)) ⪰ c B(Σ_mb), Neumann bound, O(c²) remainder."""
import numpy as np
rng = np.random.default_rng(107); d = 3; nS = 5
lam = np.array([1.0, 2.5, 0.7]); t = 20.0; g = 0.7; h = 0.1 / t; m = 2
H = np.diag(lam); P = t * H + g * np.eye(d); A = np.eye(d) - h * P
Hs = [H + 0.15 * (lambda M: M @ M.T)(rng.normal(size=(d, d))) for _ in range(nS)]; Hbar = sum(Hs) / nS; D = [Hi - Hbar for Hi in Hs]
Cg = (lambda M: M @ M.T)(rng.normal(size=(d, d))) * 0.3; N = 2 * h * np.eye(d) + h**2 * t**2 * Cg
c = h**2 * t**2 * (1 - m / nS) / (m * (nS - 1))
opnorm = lambda M: np.max(np.sum(np.abs(M), axis=1))
a = opnorm(A) * opnorm(A.T); b = sum(opnorm(Di) * opnorm(Di.T) for Di in D); L = a + c * b
B = lambda X: sum(Di @ X @ Di.T for Di in D)
def R(Y):  # Lyapunov resolvent in the (diagonal) frame: Y_ij / (1 - a_i a_j)
    rho = np.diag(A); return Y / (1 - np.outer(rho, rho))
S = np.zeros((d, d)); F = np.zeros((d, d))
for _ in range(20000): S = A @ S @ A.T + N; F = A @ F @ A.T + N + c * B(F)
Delta = F - S
print(f"a={a:.4f} b={b:.4f} L={L:.4f}")
print("exact identity  ‖Δ − c R(B(F))‖ =", f"{opnorm(Delta - c * R(B(F))):.2e}")
lo1 = c * R(B(S)); lo0 = c * B(S)
print("eigs(Δ − cR(B(S))) =", np.round(np.linalg.eigvalsh(Delta - lo1), 8), " eigs(cR(B(S)) − cB(S)) =", np.round(np.linalg.eigvalsh(lo1 - lo0), 8))
Y = rng.normal(size=(d, d)); Y = Y + Y.T
print(f"Neumann: ‖R(Y)‖ = {opnorm(R(Y)):.4f} ≤ ‖Y‖/(1−a) = {opnorm(Y)/(1-a):.4f}")
rem = opnorm(Delta - c * R(B(S))); bound = c**2 * b * opnorm(B(S)) / ((1 - a) * (1 - L))
print(f"remainder ‖Δ − cR(B(S))‖ = {rem:.3e} ≤ c²b‖B(S)‖/((1−a)(1−L)) = {bound:.3e}   (first-order term c‖R(B(S))‖ = {opnorm(lo1):.3e})")
print(f"LLC: tr(HΔ) = {np.trace(H@Delta):.5e}  ≥ c tr(H R(B(S))) = {np.trace(H@lo1):.5e}  ≥ c tr(H B(S)) = {np.trace(H@lo0):.5e}")
