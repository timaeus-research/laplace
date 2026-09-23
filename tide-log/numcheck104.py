"""Numerical check for tide 104 (minibatch-fluctuation).
Frame U diagonalising P (eigen p) and H (eigen lam); rho = 1 - h p; N = 2h I + h^2 t^2 C (C PSD);
Sigma^mb = lyapunovVia: (U^T Sigma U)_ij = (U^T N U)_ij / (1 - rho_i rho_j).
Claims: (A) x^T diagLyap(N^) x = sum_r (D^r x)^T N^ (D^r x) >= x^T N^ x > 0 (PosDef);
(B) Var_{N(m,Sigma)}(1/2 u^T H u) = 1/2 sum_ij lam_i lam_j S_ij^2 + sum_ij lam_i lam_j mh_i mh_j S_ij  (S = U^T Sigma U);
(C) S_ij = sigma_i^2 [i=j] + E_ij, E_ij = h^2 t^2 Chat_ij/(1 - rho_i rho_j); excess = 1/2 sum_ij lam_i lam_j (2 sigma_i^2 [i=j] E_ij + E_ij^2) + sum_ij lam lam mh mh E;
    first order diag term sum_i lam_i^2 sigma_i^2 E_ii = (h t^2/2) sum_i lam_i^2 sigma_i^4 Chat_ii; Sigma^mb - Sigma^ULA = lyapunovVia(h^2 t^2 C) PSD."""
import numpy as np
rng = np.random.default_rng(4)
d = 3; lam = np.array([1.0, 2.5, 0.7]); t = 20.0; g = 0.7; h = 0.3/t
Qr, _ = np.linalg.qr(rng.standard_normal((d, d))); U = Qr
H = U @ np.diag(lam) @ U.T; P = t*H + g*np.eye(d); p = t*lam + g; rho = 1 - h*p; kap = 1 - h*p/2; s2 = 1/(p*kap)
A = np.eye(d) - h*P
B = rng.standard_normal((d, d)); C = 0.05 * B @ B.T
N = 2*h*np.eye(d) + h**2 * t**2 * C
Nh = U.T @ N @ U; Ch = U.T @ C @ U
S = Nh / (1 - np.outer(rho, rho)); Sigma = U @ S @ U.T
# fixed point check
X = np.zeros((d, d))
for _ in range(20000): X = A @ X @ A.T + N
print("lyapunov fixed point err", np.abs(X - Sigma).max())
# (A) PosDef via series
x = rng.standard_normal(d); xh = U.T @ x
q = sum(((rho**r * xh) @ Nh @ (rho**r * xh)) for r in range(4000))
print("x^T S x", xh @ S @ xh, "series", q, "first term", xh @ Nh @ xh, "eigmin Sigma", np.linalg.eigvalsh(Sigma).min())
# (B) variance
w0 = rng.standard_normal(d); m = np.linalg.solve(P, g*w0); mh = U.T @ m
var_exact = 0.5*np.trace(H @ Sigma @ H @ Sigma) + (H @ m) @ Sigma @ (H @ m)
var_frame = 0.5*np.sum(np.outer(lam, lam) * S**2) + np.sum(np.outer(lam*mh, lam*mh) * S)
Z = rng.multivariate_normal(m, Sigma, size=2_000_000); Y = 0.5*np.einsum('ni,ij,nj->n', Z, H, Z)
print("Var exact", var_exact, "frame formula", var_frame, "MC", Y.var())
# (C) excess
E = h**2 * t**2 * Ch / (1 - np.outer(rho, rho)); print("S - diag(s2) - E", np.abs(S - np.diag(s2) - E).max())
var_ula = 0.5*np.sum(lam**2*s2**2) + np.sum(lam**2*s2*mh**2)
excess = 0.5*np.sum(np.outer(lam, lam)*(2*np.diag(s2)*E + E**2)) + np.sum(np.outer(lam*mh, lam*mh)*E)
first = h*t**2/2*np.sum(lam**2*s2**2*np.diag(Ch))
print("excess", var_frame - var_ula, "formula", excess, "first-order diag term", first, " sum lam^2 s2 E_ii", np.sum(lam**2*s2*np.diag(E)))
Dm = Sigma - U @ np.diag(s2) @ U.T; print("eigmin(Sigma^mb - Sigma^ULA)", np.linalg.eigvalsh(Dm).min(), " = lyapunovVia(h^2t^2 C)?", np.abs(Dm - U @ (h**2*t**2*Ch/(1-np.outer(rho,rho))) @ U.T).max())
