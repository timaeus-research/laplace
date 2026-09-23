"""Tide 98 numerical check: ULA burn-in from a nonzero start x0 on the Gaussian target N(0, P^{-1}).
x_{k+1} = (I - hP) x_k + sqrt(2h) xi.  Law at step k: N(A^k x0, Sigma_k), Sigma_k = ulaCov (1 - A^{2k}), ulaCov = (P - h/2 P^2)^{-1}.
Eigen (p_i eigenvalues of P, rho = 1 - h p, a = 1 - h p/2, f = 1 - rho^{2k}, b = U^T x0):
  mean energy  E[1/2 u^T P u] = 1/2 sum f/a + 1/2 sum p rho^{2k} b^2
  bias vs stationary 1/2 sum 1/a:  1/2 sum rho^{2k} (p b^2 - 1/a)
  variance  Var(1/2 u^T P u) = 1/2 sum (f/a)^2 + sum p rho^{2k} b^2 f/a
  transform E[exp(-s 1/2 u^T P u)] = exp(-1/2 sum s p a rho^{2k} b^2/(a + s f)) sqrt(prod a/(a + s f))
"""
import numpy as np
rng = np.random.default_rng(3)
M = rng.normal(size=(3, 3)); P = M @ M.T + 0.5 * np.eye(3); h = 0.05; x0 = np.array([1.2, -0.7, 0.4]); k = 4; s = 0.7
p, U = np.linalg.eigh(P); rho = 1 - h * p; a = 1 - h * p / 2; f = 1 - rho**(2 * k); b = U.T @ x0
assert (h * p < 2).all()
A = np.eye(3) - h * P; ulaCov = np.linalg.inv(P - h / 2 * P @ P); Sig = ulaCov @ (np.eye(3) - np.linalg.matrix_power(A, 2 * k)); m = np.linalg.matrix_power(A, k) @ x0
# Monte Carlo of the chain
N = 400000; x = np.tile(x0, (N, 1))
for _ in range(k): x = x @ A.T + np.sqrt(2 * h) * rng.normal(size=x.shape)
E = 0.5 * np.einsum('ni,ij,nj->n', x, P, x)
print(f"chain mean err {np.abs(x.mean(0) - m).max():.4f}, cov err {np.abs(np.cov(x.T) - Sig).max():.4f}")
mean_f = 0.5 * np.sum(f / a) + 0.5 * np.sum(p * rho**(2 * k) * b**2); mean_mat = 0.5 * np.trace(P @ Sig) + 0.5 * m @ P @ m
print(f"mean energy: MC {E.mean():.5f}  matrix {mean_mat:.5f}  eigen {mean_f:.5f};  bias formula {0.5*np.sum(rho**(2*k)*(p*b**2 - 1/a)):.5f} vs {mean_f - 0.5*np.sum(1/a):.5f}")
var_f = 0.5 * np.sum((f / a)**2) + np.sum(p * rho**(2 * k) * b**2 * f / a); var_mat = 0.5 * np.trace(P @ Sig @ P @ Sig) + m @ P @ Sig @ P @ m
print(f"variance: MC {E.var():.5f}  matrix {var_mat:.5f}  eigen {var_f:.5f}")
Q = np.linalg.inv(Sig); v = Q @ m; ms = np.linalg.solve(Q + s * P, v)
tr_mat = np.exp(0.5 * ms @ v - 0.5 * m @ v) * np.sqrt(np.linalg.det(Q) / np.linalg.det(Q + s * P))
tr_f = np.exp(-0.5 * np.sum(s * p * a * rho**(2 * k) * b**2 / (a + s * f))) * np.sqrt(np.prod(a / (a + s * f)))
print(f"transform s={s}: MC {np.mean(np.exp(-s*E)):.5f}  matrix {tr_mat:.5f}  eigen {tr_f:.5f}")
for kk in [1, 2, 4, 8, 16, 32]:
    ff = 1 - rho**(2 * kk); print(f"k={kk:2d}: mean {0.5*np.sum(ff/a) + 0.5*np.sum(p*rho**(2*kk)*b**2):.5f}  transient {0.5*np.sum(p*rho**(2*kk)*b**2):.5f}  stationary {0.5*np.sum(1/a):.5f}")
