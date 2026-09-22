"""Tide 77: the exact derivative identity d/dt <psi>_loc = -Cov_loc[l, psi] on the localised measure (1D numerical check)."""
import numpy as np
from scipy.integrate import quad
lam, al, ga, g, x0 = 1.3, 0.7, 1.1, 0.8, 0.6
L = lambda x: lam/2*x**2 + al/6*x**3 + ga/24*x**4
def E(t, f):
    w = lambda x: np.exp(-t*L(x) + g*x0*x - g/2*x**2); Z = quad(w, -3, 3, points=[0], limit=400)[0]
    return quad(lambda x: f(x)*w(x), -3, 3, points=[0], limit=400)[0]/Z
for psi, name in [(lambda x: x, "x"), (lambda x: x*x, "x^2"), (lambda x: 0.7*x*x/2 - 0.3*x, "0.35x^2-0.3x")]:
    for t in [5.0, 20.0, 80.0]:
        h = 1e-3*t
        d = (E(t+h, psi) - E(t-h, psi))/(2*h)
        cov = E(t, lambda x: L(x)*psi(x)) - E(t, L)*E(t, psi)
        print(f"psi={name:12s} t={t:5.0f}: d/dt<psi>_loc = {d:.8f}   -Cov_loc[l,psi] = {-cov:.8f}   diff = {d+cov:.2e}")
