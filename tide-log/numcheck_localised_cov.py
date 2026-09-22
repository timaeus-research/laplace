"""Localised covariance (eq:cov with S = (tH + gI)^{-1}) on the exact localised anharmonic measure.
1D: Var_loc vs 1/(lam t) and vs 1/(t lam + g): claims |t Var - 1/lam| <= K/t and |Var - 1/(t lam+g)| <= K/t^2.
d=2: Cov_loc[w] vs S = Q diag(1/(t lam_i + g)) Q^T entrywise, t^2-scaled error."""
import numpy as np
from scipy.integrate import quad, dblquad
lam, alpha, gam = 1.3, 0.7, 1.1; g, x0 = 0.8, 0.6
def ell(x): return lam*x**2/2 + alpha*x**3/6 + gam*x**4/24
def mom(t, k):
    w = lambda x: np.exp(-t*ell(x) - g/2*(x-x0)**2); R = 12/np.sqrt(lam*t) + abs(x0)
    Z = quad(w, -R, R, epsabs=1e-15, epsrel=1e-14, limit=800)[0]
    return quad(lambda x: x**k*w(x), -R, R, epsabs=1e-15, epsrel=1e-14, limit=800)[0]/Z
print("1D:")
for t in [10.0, 40.0, 160.0, 640.0]:
    m1, m2 = mom(t,1), mom(t,2); V = m2 - m1**2
    print(f"  t={t:g}: tVar={t*V:.6f} 1/lam={1/lam:.6f} t(tVar-1/lam)={t*(t*V-1/lam):.4f}  t^2(Var-1/(t lam+g))={t**2*(V-1/(t*lam+g)):.4f}")
th = 0.6; Q = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
lam2 = np.array([1.3, 0.7]); al2 = np.array([0.7, -0.4]); ga2 = np.array([1.1, 0.9]); c = np.array([0.3, -0.2]); w0 = np.array([0.5, 0.9])
u0 = Q.T @ (w0 - c)
def ell2(u): return np.sum(lam2*u**2/2 + al2*u**3/6 + ga2*u**4/24)
print("d=2:")
for t in [10.0, 40.0, 160.0]:
    R = 12/np.sqrt(min(lam2)*t) + 2*max(abs(u0))
    dens = lambda u1, u2: np.exp(-t*ell2(np.array([u1,u2])) - g/2*((u1-u0[0])**2 + (u2-u0[1])**2))
    Z = dblquad(lambda y, x: dens(x, y), -R, R, -R, R, epsabs=1e-13, epsrel=1e-12)[0]
    E = lambda f: dblquad(lambda y, x: f(x, y)*dens(x, y), -R, R, -R, R, epsabs=1e-13, epsrel=1e-12)[0]/Z
    m = np.array([E(lambda x,y: x), E(lambda x,y: y)])
    C = np.array([[E(lambda x,y: x*x), E(lambda x,y: x*y)],[E(lambda x,y: x*y), E(lambda x,y: y*y)]]) - np.outer(m, m)
    Cw = Q @ C @ Q.T   # ambient covariance
    S = np.linalg.inv(t*Q@np.diag(lam2)@Q.T + g*np.eye(2))
    print(f"  t={t:g}: |Cov_u offdiag|={abs(C[0,1]):.1e}  t^2*max|Cov_w - S|={t**2*np.max(np.abs(Cw-S)):.4f}  t*max|Cov_w - S|={t*np.max(np.abs(Cw-S)):.4f}")
