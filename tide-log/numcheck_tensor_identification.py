"""Tide tensor-identification: finite-difference check that the coordinate partial derivatives of L∘A at c are
H = Q diag(lam) Q^T, T_ijk = sum_l alpha_l Q_il Q_jl Q_kl, Q4_ijkm = sum_l gamma_l Q_il Q_jl Q_kl Q_ml, and grad = 0, value = 0."""
import numpy as np
rng = np.random.default_rng(5); d = 3
lam = np.array([1.0, 2.0, 5.0]); alpha = 0.5 * lam**1.5; gamma = lam**2
Q, _ = np.linalg.qr(rng.normal(size=(d, d))); c = rng.normal(size=d)
def ell(l, al, g, x): return l * x**2 / 2 + al * x**3 / 6 + g * x**4 / 24
def F(w): u = Q.T @ (w - c); return sum(ell(lam[l], alpha[l], gamma[l], u[l]) for l in range(d))
h = 1e-2
def e(i): v = np.zeros(d); v[i] = 1; return v
def d1(f, i): return lambda w: (f(w + h * e(i)) - f(w - h * e(i))) / (2 * h)
print("F(c) =", F(c), " grad:", [d1(F, i)(c) for i in range(d)])
H = Q @ np.diag(lam) @ Q.T
T = np.einsum('l,il,jl,kl->ijk', alpha, Q, Q, Q)
Q4 = np.einsum('l,il,jl,kl,ml->ijkm', gamma, Q, Q, Q, Q)
errH = max(abs(d1(d1(F, i), j)(c) - H[i, j]) for i in range(d) for j in range(d))
errT = max(abs(d1(d1(d1(F, i), j), k)(c) - T[i, j, k]) for i in range(d) for j in range(d) for k in range(d))
errQ = max(abs(d1(d1(d1(d1(F, i), j), k), m)(c) - Q4[i, j, k, m]) for i in range(d) for j in range(d) for k in range(d) for m in range(d))
print("max |FD - H| = %.2e, max |FD - T| = %.2e, max |FD - Q4| = %.2e (h = %g; O(h^2) errors expected)" % (errH, errT, errQ, h))
