"""Numerical check for tide 105 (minibatch-longrun).
Linear chain x' = m + A(x-m) + xi, xi ~ N(0, N), A = 1 - hP, N = 2hI + h^2 t^2 C.  Sigma = lyapunov fixed point; S = U^T Sigma U (full).
Claims: (A) k-step covariance from a point start = Sigma - A^k Sigma A^k^T, frame entries S_ij (1 - rho_i^k rho_j^k) = N^_ij sum_{r<k} (rho_i rho_j)^r, PD for k>=1;
        (B) energy mean after k steps from x0: 1/2 sum_i lam_i S_ii (1 - rho_i^{2k}) + 1/2 sum_i lam_i (mh_i + rho_i^k (x0h_i - mh_i))^2;
        (C) Cov(Y_0, Y_l) = 1/2 sum_ij lam_i lam_j S_ij^2 rho_j^{2l} + sum_ij lam_i lam_j mh_i mh_j S_ij rho_j^l;
        (D) tau^2 = c0 + 2 sum_{l>=1} c_l = 1/2 sum_ij lam lam S_ij^2 (1+rho_j^2)/(1-rho_j^2) + sum_ij lam lam mh mh S_ij (1+rho_j)/(1-rho_j)."""
import numpy as np
rng = np.random.default_rng(5)
d = 3; lam = np.array([1.0, 2.5, 0.7]); t = 20.0; g = 0.7; h = 0.3/t
Qr, _ = np.linalg.qr(rng.standard_normal((d, d))); U = Qr
H = U @ np.diag(lam) @ U.T; P = t*H + g*np.eye(d); p = t*lam + g; rho = 1 - h*p
A = np.eye(d) - h*P
B = rng.standard_normal((d, d)); C = 0.05 * B @ B.T
N = 2*h*np.eye(d) + h**2*t**2*C; Nh = U.T @ N @ U
S = Nh / (1 - np.outer(rho, rho)); Sigma = U @ S @ U.T
w0 = rng.standard_normal(d); m = np.linalg.solve(P, g*w0); mh = U.T @ m
def Y(x): return 0.5*np.einsum('...i,ij,...j->...', x, H, x)
# (A)
k = 3; Ak = np.linalg.matrix_power(A, k); Sk = Sigma - Ak @ Sigma @ Ak.T
X = np.zeros((d, d))
for _ in range(k): X = A @ X @ A.T + N
print("k-step cov iterate vs Sigma - A^k Sigma A^kT:", np.abs(X - Sk).max())
Skh = U.T @ Sk @ U; print("frame entries S_ij(1-rho_i^k rho_j^k):", np.abs(Skh - S*(1 - np.outer(rho**k, rho**k))).max(), " = Nh sum_{r<k}:", np.abs(Skh - Nh*sum(np.outer(rho**r, rho**r) for r in range(k))).max(), " eigmin", np.linalg.eigvalsh(Sk).min())
# (B)
x0 = rng.standard_normal(d); x0h = U.T @ x0
mk = m + Ak @ (x0 - m)
energy_exact = 0.5*np.trace(H @ Sk) + 0.5*mk @ H @ mk
energy_frame = 0.5*np.sum(lam*np.diag(S)*(1 - rho**(2*k))) + 0.5*np.sum(lam*(mh + rho**k*(x0h - mh))**2)
print("energy after k steps exact", energy_exact, "frame", energy_frame)
# (C) autocovariance: exact via tilted-Gaussian mixed Wick with B_l = A^l H A^l, b_l = A^l H (1-A^l) m
def c_exact(l):
    Al = np.linalg.matrix_power(A, l); Bl = Al.T @ H @ Al; bl = Al.T @ H @ (np.eye(d) - Al) @ m
    return 0.5*np.trace(H @ Sigma @ Bl @ Sigma) + (H @ m) @ Sigma @ (Bl @ m) + (H @ m) @ Sigma @ bl
def c_closed(l):
    return 0.5*np.sum(np.outer(lam, lam)*S**2*(rho**(2*l))[None, :]) + np.sum(np.outer(lam*mh, lam*mh)*S*(rho**l)[None, :])
M = 2_000_000; L = 6
x = rng.multivariate_normal(m, Sigma, size=M); xs = [x]
Lchol = np.linalg.cholesky(N)
for l in range(L):
    x = m + (x - m) @ A.T + rng.standard_normal(x.shape) @ Lchol.T; xs.append(x)
Ys = np.array([Y(z) for z in xs])
print("lag  closed        exact        MC")
for l in range(L+1):
    print(f"{l:3d}  {c_closed(l):.6e} {c_exact(l):.6e} {np.mean((Ys[0]-Ys[0].mean())*(Ys[l]-Ys[l].mean())):.6e}")
# (D)
tau2_series = c_closed(0) + 2*sum(c_closed(l) for l in range(1, 4000))
tau2_closed = 0.5*np.sum(np.outer(lam, lam)*S**2*((1+rho**2)/(1-rho**2))[None, :]) + np.sum(np.outer(lam*mh, lam*mh)*S*((1+rho)/(1-rho))[None, :])
s2 = 1/(p*(1 - h*p/2)); tau2_ula = 0.5*np.sum(lam**2*s2**2*(1+rho**2)/(1-rho**2)) + np.sum(lam**2*s2*mh**2*(1+rho)/(1-rho))
print("tau2 series", tau2_series, "closed", tau2_closed, " ULA tau2", tau2_ula, " ratio", tau2_closed/tau2_ula)
