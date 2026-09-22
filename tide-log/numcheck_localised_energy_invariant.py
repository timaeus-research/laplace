"""Tide 85 numerical check: the localised energy — invariant anchor correction and the derivative reading of the LLC.

(a) invariant form of tide 73's coefficient: sum_i (e1_i + g/(2 lam_i)) = E1 + (g^2/2) (w0-c)^T H^{-1} (w0-c) + g (w0-c).m1,
    E1 = sum_i energyCoeff1_i, m1 = Q (-alpha/(2 lam^2)) the unlocalised first-order mean shift;
(b) exact: -d/dt <L∘A>_loc = Var_loc(L∘A)  (central differences vs direct variance);
(c) t^2 Var_loc(L∘A) -> d/2 = sum_i 1/2, per coordinate t^2 Var_loc(ell_i) -> 1/2, with O(1/t) residual (coefficient?).
"""
import numpy as np
from scipy.integrate import quad

lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8
th = 0.6; Q = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
c = np.array([0.3, -0.2]); w0 = np.array([0.9, 0.4]); u0 = Q.T @ (w0 - c); a = g * u0
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24

def stats(i, t):
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    lim = 12 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    Z = quad(dens, -lim, lim, epsabs=1e-15, epsrel=1e-14)[0]
    E = lambda f: quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-15, epsrel=1e-14)[0] / Z
    m = E(lambda x: ell(i, x)); v = E(lambda x: ell(i, x)**2) - m**2
    return m, v

# (a)
e1 = (a**2 - g) / (2 * lam) - a * alpha / (2 * lam**2) - gamma / (8 * lam**2) + 5 * alpha**2 / (24 * lam**3)
E1 = np.sum(-gamma / (8 * lam**2) + 5 * alpha**2 / (24 * lam**3))
Hinv = Q @ np.diag(1 / lam) @ Q.T; m1 = Q @ (-alpha / (2 * lam**2))
lhs = np.sum(e1 + g / (2 * lam)); rhs = E1 + g**2 / 2 * (w0 - c) @ Hinv @ (w0 - c) + g * (w0 - c) @ m1
print(f"(a) sum(e1 + g/2lam) = {lhs:.10f}   E1 + g^2/2 <w0-c,Hinv(w0-c)> + g<w0-c,m1> = {rhs:.10f}")
# (b),(c)
for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
    h = t * 1e-3
    mL = lambda tt: sum(stats(i, tt)[0] for i in range(2))
    dL = -(mL(t + h) - mL(t - h)) / (2 * h)
    var = sum(stats(i, t)[1] for i in range(2))
    per = [t**2 * stats(i, t)[1] for i in range(2)]
    print(f"t={t:5.0f}: -d<L>/dt = {dL:.10e}  Var_loc(L) = {var:.10e}   t^2 Var = {t**2*var:.6f} (t*resid {t*(t**2*var-1.0):.4f})   per coord: {per[0]:.5f}, {per[1]:.5f}")
