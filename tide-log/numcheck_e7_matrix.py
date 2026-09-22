"""Tide e7-matrix: numerical check.

(1) oneLoopCov(t, H, T, Q4) with H = Q diag(lam) Q^T, T_ijk = sum_l alpha_l Q_il Q_jl Q_kl,
    Q4_ijkl = sum_l gamma_l Q_il Q_jl Q_kl Q_ml equals Q diag(1/(lam t) + C/t^2) Q^T, C = alpha^2/lam^4 - gamma/(2 lam^3);
    in particular bubble = tadpoleLine = Q diag(alpha^2/(lam t)^2) Q^T and contractQ = Q diag(gamma/(lam t)) Q^T.
(2) exact Cov_w = Q diag(Var_i) Q^T (quadrature per coordinate); t^2 * ||Cov - oneLoop||_F / ||S||_F bounded,
    t * ||Cov - S||_F / ||S||_F -> |a^2 - 1/2|.
"""
import numpy as np
from scipy.integrate import quad
from math import sqrt

rng = np.random.default_rng(0)
d = 3; a = 0.5
lam = np.array([1.0, 2.0, 5.0]); alpha = a * lam**1.5; gamma = lam**2
M = rng.normal(size=(d, d)); Q, _ = np.linalg.qr(M)

H = Q @ np.diag(lam) @ Q.T
T = np.einsum('l,il,jl,kl->ijk', alpha, Q, Q, Q)
Q4 = np.einsum('l,il,jl,kl,ml->ijkm', gamma, Q, Q, Q, Q)

def oneLoop(t):
    S = np.linalg.inv(t * H)
    cQ = np.einsum('ijkl,kl->ij', Q4, S)
    bub = np.einsum('ikl,km,ln,jmn->ij', T, S, S, T)
    TS = np.einsum('lmn,mn->l', T, S)
    tad = np.einsum('ijk,kl,l->ij', T, S, TS)
    Pi = -(t / 2) * cQ + (t**2 / 2) * bub + (t**2 / 2) * tad
    return S + S @ Pi @ S, S, cQ, bub, tad

C = alpha**2 / lam**4 - gamma / (2 * lam**3)
t0 = 7.0
OL, S, cQ, bub, tad = oneLoop(t0)
pred = Q @ np.diag(1 / (lam * t0) + C / t0**2) @ Q.T
print("(1) ||oneLoop - Q diag(1/(lam t)+C/t^2) Q^T||_F =", np.linalg.norm(OL - pred))
print("    ||contractQ - Q diag(gamma/(lam t)) Q^T|| =", np.linalg.norm(cQ - Q @ np.diag(gamma / (lam * t0)) @ Q.T))
print("    ||bubble - Q diag(alpha^2/(lam t)^2) Q^T|| =", np.linalg.norm(bub - Q @ np.diag(alpha**2 / (lam * t0)**2) @ Q.T))
print("    ||tadpole - bubble|| =", np.linalg.norm(tad - bub))

def ell(l, al, g, x): return l * x**2 / 2 + al * x**3 / 6 + g * x**4 / 24
def var(l, al, g, t):
    w = lambda x: np.exp(-t * ell(l, al, g, x)); R = 12 / sqrt(l * t)
    Z = quad(w, -R, R, limit=400, epsabs=1e-14, epsrel=1e-13)[0]
    m1 = quad(lambda x: x * w(x), -R, R, limit=400, epsabs=1e-14, epsrel=1e-13)[0] / Z
    m2 = quad(lambda x: x**2 * w(x), -R, R, limit=400, epsabs=1e-14, epsrel=1e-13)[0] / Z
    return m2 - m1**2

print("(2) t : t^2*||Cov-oneLoop||/||S||, t*||Cov-S||/||S|| (target |a^2-1/2| = %.3f)" % abs(a**2 - 0.5))
for t in [20, 40, 80, 160, 320]:
    V = np.array([var(lam[i], alpha[i], gamma[i], t) for i in range(d)])
    Cov = Q @ np.diag(V) @ Q.T
    OL, S, *_ = oneLoop(t)
    nS = np.linalg.norm(S)
    print("  t=%4d  %.4f  %.4f" % (t, t**2 * np.linalg.norm(Cov - OL) / nS, t * np.linalg.norm(Cov - S) / nS))
