"""Tide 76: E3's localised eq:covK at leading order (1D quadrature), plus the t^-3 coefficients vs the derivative reading."""
import numpy as np
from scipy.integrate import quad
lam, al, ga, g, x0 = 1.3, 0.7, 1.1, 0.8, 0.6
a = g*x0; c = -al/(2*lam**2) + a/lam
B1 = -5*al**3/(8*lam**5) + 2*al*ga/(3*lam**4); B2 = 5*al**2/(4*lam**4) - ga/(2*lam**3)
cp = B1 + a*al**2/lam**4 - a*ga/(2*lam**3) + al*g/lam**3 - al*a**2/(2*lam**3) - a*g/lam**2      # tide 72 c'
c3 = -5*al/(2*lam**3); p3 = (a**2-g)/2; d1 = -a*al/(2*lam**2) + p3/lam; n2 = B2 + a*c3 + 3*p3/lam**2; c2p = n2 - d1/lam   # tide 73 c2'
print(f"predicted leading: t^2 Cov_loc[l,x] -> c = {c:.6f};  t^2 Cov_loc[l,x^2] -> 1/lam = {1/lam:.6f}")
print(f"derivative-reading predictions for the 1/t coefficients: 2c' = {2*cp:.6f}, 2c2' = {2*c2p:.6f}")
L = lambda x: lam/2*x**2 + al/6*x**3 + ga/24*x**4
def E(t, f):
    w = lambda x: np.exp(-t*L(x) + a*x - g/2*x**2); Z = quad(w, -3, 3, points=[0], limit=400)[0]
    return quad(lambda x: f(x)*w(x), -3, 3, points=[0], limit=400)[0]/Z
for t in [10, 40, 160, 640]:
    m1, m2, ml = E(t, lambda x: x), E(t, lambda x: x*x), E(t, L)
    cov1 = E(t, lambda x: L(x)*x) - ml*m1; cov2 = E(t, lambda x: L(x)*x*x) - ml*m2
    print(f"t={t:5d}: t^2Cov[l,x]={t*t*cov1:.6f} t(t^2Cov-c)={t*(t*t*cov1-c):.5f} | t^2Cov[l,x^2]={t*t*cov2:.6f} t(t^2Cov-1/lam)={t*(t*t*cov2-1/lam):.5f}")
