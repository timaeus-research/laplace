"""Tide e2-matrix: numerical check of eq:mean and eq:covK in matrix form for the rotated oscillator.

(1) meanShift(t) = -(t/2) S (T:S) with S = (tH)^{-1} equals Q (-alpha/(2 lam^2 t)); exact t(<w>-c) -> Q(-alpha/(2 lam^2)).
(2) covKMatrix(t; B, b) = 1/2 tr(H S B S) + 1/2 (Sb).(T:S) - (t/2) b.(S H S (T:S)) - (t/2) (Sb).(T:(S H S))
    equals (1/t^2) sum_i [ (Q^T B Q)_ii/(2 lam_i) - (Q^T b)_i alpha_i/(2 lam_i^2) ]; and t^2 Cov[L, psi] -> t^2 covKMatrix,
    psi(w) = 1/2 (w-c)^T B (w-c) + b^T (w-c).
"""
import numpy as np
from scipy.integrate import quad
from math import sqrt

rng = np.random.default_rng(1)
d = 3; a = 0.5
lam = np.array([1.0, 2.0, 5.0]); alpha = a * lam**1.5; gamma = lam**2
M = rng.normal(size=(d, d)); Q, _ = np.linalg.qr(M)
c = rng.normal(size=d)
Bs = rng.normal(size=(d, d)); B = Bs + Bs.T; b = rng.normal(size=d)

H = Q @ np.diag(lam) @ Q.T
T = np.einsum('l,il,jl,kl->ijk', alpha, Q, Q, Q)

def S_of(t): return np.linalg.inv(t * H)
def TS(S): return np.einsum('lmn,mn->l', T, S)

t0 = 9.0; S = S_of(t0)
mean_shift = -(t0 / 2) * S @ TS(S)
print("(1) ||meanShift - Q(-alpha/(2 lam^2 t))|| =", np.linalg.norm(mean_shift - Q @ (-alpha / (2 * lam**2 * t0))))

def covK_matrix(t):
    S = S_of(t); SHS = S @ H @ S
    return 0.5 * np.trace(H @ S @ B @ S) + 0.5 * (S @ b) @ TS(S) - (t / 2) * b @ (SHS @ TS(S)) - (t / 2) * (S @ b) @ np.einsum('lmn,mn->l', T, SHS)
Bp = Q.T @ B @ Q; bp = Q.T @ b
pred = sum(Bp[i, i] / (2 * lam[i]) - bp[i] * alpha[i] / (2 * lam[i]**2) for i in range(d))
print("(2) t^2 covKMatrix(t) =", t0**2 * covK_matrix(t0), " diagonal formula =", pred)

# exact: separable coordinates; Cov_L[L, psi] with psi = 1/2 u^T Bp u + bp^T u (u = Q^T (w-c))
def ell(l, al, g, x): return l * x**2 / 2 + al * x**3 / 6 + g * x**4 / 24
def moments(i, t):
    l, al, g = lam[i], alpha[i], gamma[i]
    w = lambda x: np.exp(-t * ell(l, al, g, x)); R = 12 / sqrt(l * t)
    Z = quad(w, -R, R, limit=400, epsabs=1e-14, epsrel=1e-13)[0]
    E = lambda f: quad(lambda x: f(x) * w(x), -R, R, limit=400, epsabs=1e-14, epsrel=1e-13)[0] / Z
    return {'x': E(lambda x: x), 'x2': E(lambda x: x**2), 'l': E(lambda x: ell(l, al, g, x)),
            'lx': E(lambda x: ell(l, al, g, x) * x), 'lx2': E(lambda x: ell(l, al, g, x) * x**2)}
for t in [50, 200, 800]:
    m = [moments(i, t) for i in range(d)]
    # Cov[L, psi] = sum_i Cov_i[l_i, Bp_ii/2 x^2 + bp_i x] + sum_{i != j} Bp_ij Cov[L, u_i u_j]  (off-diagonal: <x>_j Cov_i[l_i,x] + <x>_i Cov_j[l_j,x])
    cov = 0.0
    for i in range(d):
        cov_l_x2 = m[i]['lx2'] - m[i]['l'] * m[i]['x2']; cov_l_x = m[i]['lx'] - m[i]['l'] * m[i]['x']
        cov += Bp[i, i] / 2 * cov_l_x2 + bp[i] * cov_l_x
        for j in range(d):
            if j != i:
                cov_j_x = m[j]['lx'] - m[j]['l'] * m[j]['x']
                cov += Bp[i, j] / 2 * (m[j]['x'] * cov_l_x + m[i]['x'] * cov_j_x)
    mean_exact = np.array([m[i]['x'] for i in range(d)])
    print("  t=%4d  t^2 Cov[L,psi]=%.5f  t^2 covKMatrix=%.5f  | t*||Q<u> - Q(-alpha/(2lam^2))||=%.2e" % (
        t, t**2 * cov, t**2 * covK_matrix(t), t * np.linalg.norm(Q @ mean_exact - Q @ (-alpha / (2 * lam**2 * t)))))
