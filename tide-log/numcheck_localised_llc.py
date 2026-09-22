"""E3's localised LLC on the exact anharmonic localised measure: t<l>_loc vs (1/2) t lam/(t lam + g) (1D) and
t<L∘A>_loc vs (1/2) sum_i t lam_i/(t lam_i + g) = (1/2) tr(tH (tH+gI)^{-1}) (d=2). Claim: error O(1/t)."""
import numpy as np
from scipy.integrate import quad, dblquad
lam, alpha, gam = 1.3, 0.7, 1.1; g, x0 = 0.8, 0.6
def ell(x): return lam*x**2/2 + alpha*x**3/6 + gam*x**4/24
def E_loc(t, f):
    w = lambda x: np.exp(-t*ell(x) - g/2*(x-x0)**2); R = 12/np.sqrt(lam*t) + abs(x0)
    Z = quad(w, -R, R, epsabs=1e-15, epsrel=1e-14, limit=800)[0]
    return quad(lambda x: f(x)*w(x), -R, R, epsabs=1e-15, epsrel=1e-14, limit=800)[0]/Z
print("1D:")
for t in [10.0, 40.0, 160.0, 640.0]:
    e = t*E_loc(t, ell); pred = 0.5*t*lam/(t*lam+g)
    print(f"  t={t:g}: t<l>_loc={e:.6f} pred={pred:.6f} t*(diff)={t*(e-pred):.4f}   t<x^3>_loc*t={t*t*E_loc(t, lambda x: x**3):.4f}")
th = 0.6; Q = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
lam2 = np.array([1.3, 0.7]); al2 = np.array([0.7, -0.4]); ga2 = np.array([1.1, 0.9]); c = np.array([0.3, -0.2]); w0 = np.array([0.5, 0.9])
u0 = Q.T @ (w0 - c)
def ell2(u): return np.sum(lam2*u**2/2 + al2*u**3/6 + ga2*u**4/24)
print("d=2:")
for t in [10.0, 40.0, 160.0]:
    R = 12/np.sqrt(min(lam2)*t) + 2*max(abs(u0))
    dens = lambda u1, u2: np.exp(-t*ell2(np.array([u1,u2])) - g/2*((u1-u0[0])**2 + (u2-u0[1])**2))
    Z = dblquad(lambda y, x: dens(x, y), -R, R, -R, R, epsabs=1e-13, epsrel=1e-12)[0]
    EL = dblquad(lambda y, x: ell2(np.array([x,y]))*dens(x, y), -R, R, -R, R, epsabs=1e-13, epsrel=1e-12)[0]/Z
    H = Q@np.diag(lam2)@Q.T; S = np.linalg.inv(t*H + g*np.eye(2)); pred = 0.5*np.trace(t*H@S)
    print(f"  t={t:g}: t<L∘A>_loc={t*EL:.6f} pred=(1/2)tr(tH S)={pred:.6f} t*(diff)={t*(t*EL-pred):.4f}")
