"""Tide 101 numerical check: minibatch (constant gradient-noise covariance C) stationary covariance of SGLD on the anchored quadratic
model, x' = x - hP(x - m) + noise, Cov(noise) = 2h I + h^2 t^2 C.  Stationary Sigma solves Sigma = A Sigma A^T + N (Lyapunov).
Claims (frame of P, H diagonal, Chat = U^T C U): (U^T Sigma U)_ij = (2h [i=j] + h^2 t^2 Chat_ij)/(1 - rho_i rho_j);
  diag: (1 + h t^2 Chat_ii/2)/(p_i kappa_i);  t/2 tr(H Sigma) = t/2 sum lam_i (1 + h t^2 Chat_ii/2)/(p_i kappa_i)
  extended stationary budget: t<L> - (t/2 tr(H Sigma) + t/2 sum lam b^2) = C1'/t - (th/4) sum lam/kappa - (h t^3/4) sum lam Chat_ii/(p kappa) + O(t^-2).
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0
e0 = 5 * alpha**2 / (24 * lam**3) - gamma / (8 * lam**2); C1p = np.sum(e0 - a * alpha / (2 * lam**2))
rng = np.random.default_rng(7); M = rng.normal(size=(2, 2)); C = 0.02 * (M @ M.T)   # gradient-noise covariance (per unit t^2)
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def Eloc(i, t):
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    Z = quad(dens, -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
    return quad(lambda x: ell(i, x) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
eta = 0.3
for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
    h = eta / t; p = t * lam + g; kap = 1 - h * p / 2; rho = 1 - h * p; H = np.diag(lam); P = np.diag(p); A = np.eye(2) - h * P; N = 2 * h * np.eye(2) + h**2 * t**2 * C
    Sig = np.zeros((2, 2))
    for _ in range(20000): Sig = A @ Sig @ A.T + N
    Sig_f = np.array([[N[i, j] / (1 - rho[i] * rho[j]) for j in range(2)] for i in range(2)])
    diag_f = (1 + h * t**2 * np.diag(C) / 2) / (p * kap)
    trHS = t / 2 * np.trace(H @ Sig); trHS_f = t / 2 * np.sum(lam * diag_f)
    tL = t * sum(Eloc(i, t) for i in range(2)); b = a / p
    stationary = trHS_f + t / 2 * np.sum(lam * b**2)
    disc = (t * h / 4) * np.sum(lam / kap); mb = (h * t**3 / 4) * np.sum(lam * np.diag(C) / (p * kap))
    print(f"t={t:5.0f}: Lyapunov err {np.abs(Sig - Sig_f).max():.2e}  diag err {np.abs(np.diag(Sig) - diag_f).max():.2e}  t/2 tr(HΣ) {trHS:.5f} vs {trHS_f:.5f};  t(t<L> - stationary + disc + mb) = {t*(tL - stationary + disc + mb):.5f} vs C1' = {C1p:.5f};  disc {disc:.4f} mb {mb:.4f}")
