"""Numerical check for tide 108 (burnin-log). Anchored model P_t = tH+g, m_t = P_t^{-1} g w0 (c = 0), h = eta/t, start x0 fixed.
Burn(t,k) = t/2 sum lam rho^{2k} sigma^2 - t/2 sum lam [(mh + rho^k (x0h - mh))^2 - mh^2]  (tide 99's burn-in term).
Claims: (A) Burn(t,k(t)) -> 0 whenever k(t) -> inf and t r^{2k(t)} -> 0 (r = uniform stability bound);
(B) k(t) = ceil(kappa log t) gives t r^{2k} -> 0 iff kappa > 1/(2 log(1/r)) with r = max|1 - eta lam|;
(C) below the threshold the burn-in does not vanish."""
import numpy as np
lam = np.array([1.0, 2.5, 0.7]); g = 0.7; eta = 0.3; w0 = np.array([0.8, -0.5, 0.3]); x0h = np.array([1.5, -1.0, 0.4])
r = np.max(np.abs(1 - eta*lam)); kcrit = 1/(2*np.log(1/r)); print("r_inf", r, " kappa_crit = 1/(2 log(1/r)) =", kcrit)
def burn(t, k):
    h = eta/t; p = t*lam + g; rho = 1 - h*p; kap = 1 - h*p/2; s2 = 1/(p*kap); mh = g*w0/p
    return t/2*np.sum(lam*rho**(2*k)*s2) - t/2*np.sum(lam*((mh + rho**k*(x0h - mh))**2 - mh**2))
for kappa in [1.5*kcrit, 0.7*kcrit]:
    print(f"kappa = {kappa:.3f} ({'above' if kappa > kcrit else 'below'} threshold)")
    for t in [10, 100, 1000, 1e4, 1e5, 1e6]:
        k = int(np.ceil(kappa*np.log(t))); print(f"  t={t:8.0f} k={k:3d} Burn={burn(t,k):.3e}  t r^(2k)={t*r**(2*k):.3e}")
