"""Tide covK-derivative-multi: for the separable anharmonic measure in d = 2 and a quadratic probe psi(u) = 1/2 u.Bu + b.u,
Cov_t[L, psi] = -d<psi>_t/dt exactly (quadrature), and this equals the eq:covK prediction to O(1/t^3) (tide covK-separable)."""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.0, 2.5]); a = 0.5; alpha = a*lam**1.5; gamma = lam**2
def ell(i, x): return lam[i]*x**2/2 + alpha[i]*x**3/6 + gamma[i]*x**4/24
def m1(i, f, t):
    R = 12/np.sqrt(lam[i]*t)
    Z = quad(lambda x: np.exp(-t*ell(i,x)), -R, R, epsabs=1e-14, epsrel=1e-13, limit=400)[0]
    return quad(lambda x: f(x)*np.exp(-t*ell(i,x)), -R, R, epsabs=1e-14, epsrel=1e-13, limit=400)[0]/Z
B = np.array([[0.8, -0.3], [-0.3, 1.7]]); b = np.array([0.4, -1.1])
def psi_mean(t):  # <1/2 sum B_ij u_i u_j + sum b_i u_i> = 1/2 (B00 <u0^2> + 2 B01 <u0><u1> + B11 <u1^2>) + b . <u>
    u0, u1 = m1(0, lambda x: x, t), m1(1, lambda x: x, t)
    return 0.5*(B[0,0]*m1(0, lambda x: x**2, t) + 2*B[0,1]*u0*u1 + B[1,1]*m1(1, lambda x: x**2, t)) + b[0]*u0 + b[1]*u1
def cov_L_psi(t):  # Cov[L, psi] with L = l0(u0) + l1(u1): sum over terms using independence
    c = 0.0
    E = [lambda x, i=i: ell(i, x) for i in range(2)]
    for i in range(2):
        Li = m1(i, E[i], t)
        # Cov[l_i, 1/2 B_ii u_i^2] + Cov[l_i, b_i u_i]
        c += 0.5*B[i,i]*(m1(i, lambda x, i=i: ell(i,x)*x**2, t) - Li*m1(i, lambda x: x**2, t))
        c += b[i]*(m1(i, lambda x, i=i: ell(i,x)*x, t) - Li*m1(i, lambda x: x, t))
        # Cov[l_i, B_01 u_0 u_1] = B_01 <u_j> Cov_i[l_i, u_i]
        j = 1 - i
        c += B[0,1]*m1(j, lambda x: x, t)*(m1(i, lambda x, i=i: ell(i,x)*x, t) - Li*m1(i, lambda x: x, t))
    return c
for t in [3.0, 10.0]:
    h = 1e-4; d = (psi_mean(t+h) - psi_mean(t-h))/(2*h)
    print("t=%g: Cov[L,psi] = %.9f  -d<psi>/dt = %.9f  diff %.1e" % (t, cov_L_psi(t), -d, cov_L_psi(t)+d))
