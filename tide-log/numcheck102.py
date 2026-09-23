"""Numerical check for tide 102 (ula-autocovariance).

Stationary ULA chain on the anchored Gaussian N(m, P^{-1}), P = tH + gI, step h, A = 1 - hP,
noise covariance 2h I.  Y_k = 1/2 x_k^T H x_k.  Claims:
  (A) Cov(Y_0, Y_l) = 1/2 sum_i lam_i^2 s_i^4 rho_i^{2l} + sum_i lam_i^2 s_i^2 mhat_i^2 rho_i^l,
      with s_i^2 = 1/(p_i kappa_i), rho_i = 1 - h p_i, kappa_i = 1 - h p_i/2, mhat = U^T m;
      and Cov(Y_0, Y_l) = Cov_{N(m,Sigma)}(Y(u), E[Y_l | x_0 = u]) with the conditional mean a
      quadratic-plus-linear probe  1/2 u^T B u + b.u + c,  B = (A^l)^T H A^l, b = (A^l)^T H (1-A^l) m.
  (B) long-run variance tau^2 = c_0 + 2 sum_{l>=1} c_l
        = 1/2 sum lam^2 s^4 (1+rho^2)/(1-rho^2) + sum lam^2 s^2 mhat^2 (1+rho)/(1-rho).
  (C) Var(mean of Y_0..Y_{n-1}) = (1/n^2)(n c_0 + 2 sum_{l=1}^{n-1} (n-l) c_l), with
        sum_{l=1}^{n-1} (n-l) r^l = r (n(1-r) - (1-r^n)) / (1-r)^2.
"""
import numpy as np
rng = np.random.default_rng(3)
d = 2
lam = np.array([1.0, 2.5]); t = 20.0; g = 0.7; h = 0.3 / t
th = 0.4; U = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
H = U @ np.diag(lam) @ U.T
P = t * H + g * np.eye(d)
p = t * lam + g; rho = 1 - h * p; kap = 1 - h * p / 2; s2 = 1 / (p * kap)
w0 = np.array([0.8, -0.5]); m = np.linalg.solve(P, g * w0); mhat = U.T @ m
A = np.eye(d) - h * P
Sigma = U @ np.diag(s2) @ U.T
def Y(x): return 0.5 * np.einsum('...i,ij,...j->...', x, H, x)
def c_closed(l): return 0.5 * np.sum(lam**2 * s2**2 * rho**(2*l)) + np.sum(lam**2 * s2 * mhat**2 * rho**l)
# exact Gaussian covariance of Y(u) with the conditional-mean probe, via the tilted-Gaussian formula
def c_exact(l):
    Al = np.linalg.matrix_power(A, l); B = Al.T @ H @ Al; b = Al.T @ H @ (np.eye(d) - Al) @ m
    return 0.5 * np.trace(H @ Sigma @ B @ Sigma) + (H @ m) @ Sigma @ (B @ m) + (H @ m) @ Sigma @ b
# Monte Carlo on the stationary chain
N = 4_000_000; L = 8
x = rng.multivariate_normal(m, Sigma, size=N)
xs = [x]
for l in range(L):
    x = m + (x - m) @ A.T + np.sqrt(2*h) * rng.standard_normal(x.shape)
    xs.append(x)
Ys = np.array([Y(z) for z in xs])
print("lag  closed        exact-Gauss   MC")
for l in range(0, L+1):
    mc = np.mean((Ys[0]-Ys[0].mean())*(Ys[l]-Ys[l].mean()))
    print(f"{l:3d}  {c_closed(l):.6e}  {c_exact(l):.6e}  {mc:.6e}")
# conditional mean check: E[Y_l | x0] vs probe + c at a random x0
x0 = rng.standard_normal(d); l = 3; Al = np.linalg.matrix_power(A, l)
Sl = Sigma - Al @ Sigma @ Al.T   # burn-in covariance after l steps
cond = 0.5 * (m + Al @ (x0-m)) @ H @ (m + Al @ (x0-m)) + 0.5*np.trace(H @ Sl)
B = Al.T @ H @ Al; b = Al.T @ H @ (np.eye(d) - Al) @ m
c = 0.5 * ((np.eye(d)-Al) @ m) @ H @ ((np.eye(d)-Al) @ m) + 0.5*np.trace(H @ Sl)
print("cond mean", cond, "probe+c", 0.5*x0@B@x0 + b@x0 + c)
# frame form of the burn-in energy (tide 99): 1/2 sum lam s2 (1-rho^{2l}) + 1/2 sum lam (mhat + rho^l (x0hat-mhat))^2
x0h = U.T @ x0
print("tide99 form", 0.5*np.sum(lam*s2*(1-rho**(2*l))) + 0.5*np.sum(lam*(mhat + rho**l*(x0h-mhat))**2))
# (B) long-run variance
tau2_series = c_closed(0) + 2*sum(c_closed(l) for l in range(1, 4000))
tau2_closed = 0.5*np.sum(lam**2*s2**2*(1+rho**2)/(1-rho**2)) + np.sum(lam**2*s2*mhat**2*(1+rho)/(1-rho))
print("tau2 series", tau2_series, "closed", tau2_closed)
print("integrated autocorr times (quad, lin):", (1+rho**2)/(1-rho**2), (1+rho)/(1-rho), " 1/(hp), 2/(hp):", 1/(h*p), 2/(h*p))
# (C) finite-n variance of the chain average
n = 25
def G(r, n): return r*(n*(1-r) - (1-r**n))/(1-r)**2
var_n_lag = (n*c_closed(0) + 2*sum((n-l)*c_closed(l) for l in range(1, n)))/n**2
var_n_closed = sum(0.5*lam[i]**2*s2[i]**2*(n + 2*G(rho[i]**2, n)) + lam[i]**2*s2[i]*mhat[i]**2*(n + 2*G(rho[i], n)) for i in range(d))/n**2
# MC: long chain segments
M = 400_000
x = rng.multivariate_normal(m, Sigma, size=M); acc = np.zeros(M)
for k in range(n):
    acc += Y(x); x = m + (x - m) @ A.T + np.sqrt(2*h) * rng.standard_normal(x.shape)
print(f"Var(mean_n) lag-sum {var_n_lag:.6e} closed {var_n_closed:.6e} MC {np.var(acc/n):.6e}  tau2/n {tau2_closed/n:.6e}")
