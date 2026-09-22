"""Tide 80: the centred covariance derivative on the localised measure: -d/dt Var_loc = Cov[l,x^2] - 2 m1 Cov[l,x] (exact), second order 2 v'."""
import numpy as np
from scipy.integrate import quad
lam, al, ga, g, x0 = 1.3, 0.7, 1.1, 0.8, 0.6
a = g*x0; c = -al/(2*lam**2) + a/lam
B2 = 5*al**2/(4*lam**4) - ga/(2*lam**3); c3 = -5*al/(2*lam**3); p3 = (a**2-g)/2; d1 = -a*al/(2*lam**2) + p3/lam
n2 = B2 + a*c3 + 3*p3/lam**2; c2p = n2 - d1/lam; vp = c2p - c**2
print(f"v' = c2' - c^2 = {vp:.6f}; predicted t^2(-dVar/dt) -> 1/lam + 2v'/t, 2v' = {2*vp:.6f}")
L = lambda x: lam/2*x**2 + al/6*x**3 + ga/24*x**4
def E(t, f):
    w = lambda x: np.exp(-t*L(x) + a*x - g/2*x**2); Z = quad(w, -3, 3, points=[0], limit=400)[0]
    return quad(lambda x: f(x)*w(x), -3, 3, points=[0], limit=400)[0]/Z
def var(t): return E(t, lambda x: x*x) - E(t, lambda x: x)**2
for t in [10.0, 40.0, 160.0, 640.0]:
    h = 1e-3*t; dV = (var(t+h) - var(t-h))/(2*h)
    m1 = E(t, lambda x: x); El = E(t, L)
    cov2 = E(t, lambda x: L(x)*x*x) - El*E(t, lambda x: x*x); cov1 = E(t, lambda x: L(x)*x) - El*m1
    exact = cov2 - 2*m1*cov1
    print(f"t={t:5.0f}: -dVar/dt = {-dV:.8f}  Cov[l,x^2]-2m1Cov[l,x] = {exact:.8f}  diff = {-dV-exact:.1e} | t(t^2(-dVar/dt) - 1/lam) = {t*(t*t*exact - 1/lam):.5f} (2v' {2*vp:.5f})")
