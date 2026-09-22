"""Tide covK-derivative.
(A) Formula level: covKFormula t H T B b = -d/ds [ 1/2 tr(B (sH)^{-1}) + b . meanShift s H T ] at s = t, for any invertible H (gamma = 0);
    the 2nd and 4th terms of eq:covK cancel at S = (tH)^{-1} because SHS = S/t.
(B) Exact level (1D anharmonic): Cov_t[l, x^k] = -d/dt <x^k>_t (central differences vs quadrature)."""
import numpy as np
from scipy.integrate import quad
rng = np.random.default_rng(11); d = 4; t = 3.0
A = rng.normal(size=(d, d)); H = A @ A.T + d*np.eye(d); T = rng.normal(size=(d,d,d)); B = rng.normal(size=(d,d)); b = rng.normal(size=d)
def contractT(T, S): return np.einsum('lmn,mn->l', T, S)
def covK(s):
    S = np.linalg.inv(s*H); TS = contractT(T, S); SHS = S @ H @ S
    return 0.5*np.trace(H@S@B@S) + 0.5*(S@b)@TS - s/2*b@(SHS@TS) - s/2*(S@b)@contractT(T, SHS)
def F(s):
    S = np.linalg.inv(s*H); return 0.5*np.trace(B@S) + b @ (-0.5*S@(s*contractT(T, S)))
h = 1e-5; dF = (F(t+h) - F(t-h))/(2*h)
print("A: covKFormula(t) = %.10f   -dF/ds = %.10f   diff %.2e" % (covK(t), -dF, covK(t)+dF))
S = np.linalg.inv(t*H); TS = contractT(T, S); SHS = S@H@S
print("   terms 2+4 = %.2e (cancel at gamma = 0)" % (0.5*(S@b)@TS - t/2*(S@b)@contractT(T, SHS)))
lam, alpha, gamma = 1.3, 0.7, 1.1
def ell(x): return lam*x**2/2 + alpha*x**3/6 + gamma*x**4/24
def mom(f, s):
    Z = quad(lambda x: np.exp(-s*ell(x)), -12, 12, epsabs=1e-14, epsrel=1e-13, limit=400)[0]
    return quad(lambda x: f(x)*np.exp(-s*ell(x)), -12, 12, epsabs=1e-14, epsrel=1e-13, limit=400)[0]/Z
for k in [1, 2, 3]:
    for tt in [2.0, 8.0]:
        cov = mom(lambda x: ell(x)*x**k, tt) - mom(ell, tt)*mom(lambda x: x**k, tt)
        dm = (mom(lambda x: x**k, tt+1e-4) - mom(lambda x: x**k, tt-1e-4))/2e-4
        print("B: k=%d t=%g: Cov[l,x^k] = %.8f   -d<x^k>/dt = %.8f   diff %.1e" % (k, tt, cov, -dm, cov+dm))
