"""Tide 87 numerical check: the second-order localised energy variance and the normalised derivative discrepancy.

Per frame coordinate: t^2 Var_loc(ell) = 1/2 + 2 e1/t + O(t^-2), e1 = energyLocCoeff1 = (a^2-g)/(2lam) - a alpha/(2lam^2) - gamma/(8lam^2) + 5alpha^2/(24lam^3);
 via the Stein-covariance reduction: t^2 Cov(ell,x^3) = C3'/t + O(t^-2), C3' = (3/2)c3 - 5alpha/(4lam^3) + 3a/(2lam^2);  t^2 Cov(ell,x^4) = 6/(lam^2 t) + O(t^-2).
E2: t^2 Var_loc(L) = d/2 + 2 sum e1_i / t + O(t^-2);  with P(t) = (1/2) tr(H S(t)) = (1/2) sum lam_i/(t lam_i + g):
    t^3 (Var_loc(L) + P'(t)) -> 2 C1 = 2 sum_i (e1_i + g/(2 lam_i)).
"""
import numpy as np, sympy as sp
from scipy.integrate import quad

lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8
u0 = np.array([0.55, -0.35]); a = g * u0
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24

def E1(i, t, f):
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    Z = quad(dens, -lim, lim, epsabs=1e-15, epsrel=1e-14)[0]
    return quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-15, epsrel=1e-14)[0] / Z

e1 = (a**2 - g) / (2 * lam) - a * alpha / (2 * lam**2) - gamma / (8 * lam**2) + 5 * alpha**2 / (24 * lam**3)
c3 = -5 * alpha / (2 * lam**3) + 3 * a / lam**2
C3p = 1.5 * c3 - 5 * alpha / (4 * lam**3) + 3 * a / (2 * lam**2)
print(f"2 e1 = {2*e1}   C3' = {C3p}   6/lam^2 = {6/lam**2}")
for t in [80.0, 160.0, 320.0, 640.0, 1280.0]:
    row = []
    for i in range(2):
        m = lambda f: E1(i, t, f)
        var = m(lambda x: ell(i, x)**2) - m(lambda x: ell(i, x))**2
        cov3 = m(lambda x: ell(i, x) * x**3) - m(lambda x: ell(i, x)) * m(lambda x: x**3)
        cov4 = m(lambda x: ell(i, x) * x**4) - m(lambda x: ell(i, x)) * m(lambda x: x**4)
        row.append((t * (t**2 * var - 0.5), t**3 * cov3, t**3 * cov4))
    print(f"t={t:5.0f}: t(t^2 Var - 1/2) = {row[0][0]:.5f}, {row[1][0]:.5f}   t^3 Cov(ell,x^3) = {row[0][1]:.5f}, {row[1][1]:.5f}   t^3 Cov(ell,x^4) = {row[0][2]:.5f}, {row[1][2]:.5f}")
# E2 derivative discrepancy against the trace prediction's derivative
C1 = np.sum(e1 + g / (2 * lam))
print(f"2 C1 = {2*C1:.6f}")
for t in [80.0, 160.0, 320.0, 640.0]:
    var = sum(E1(i, t, lambda x: ell(i, x)**2) - E1(i, t, lambda x: ell(i, x))**2 for i in range(2))
    Pp = -0.5 * np.sum(lam**2 / (t * lam + g)**2)
    print(f"t={t:5.0f}: t^3 (Var_loc(L) + P'(t)) = {t**3*(var+Pp):.6f}")
# symbolic: v2 = lam c2' + (alpha/6) C3' + gamma/(4 lam^2) == 2 e1
L_, A_, G_, a_, g_ = sp.symbols('lam alpha gamma a g', positive=True)
c2p = 5*A_**2/(4*L_**4) - 2*a_*A_/L_**3 + (a_**2 - g_)/L_**2 - G_/(2*L_**3)
c3s = -5*A_/(2*L_**3) + 3*a_/L_**2
C3s = sp.Rational(3,2)*c3s - 5*A_/(4*L_**3) + 3*a_/(2*L_**2)
v2 = L_*c2p + A_/6*C3s + G_/(4*L_**2)
e1s = (a_**2 - g_)/(2*L_) - a_*A_/(2*L_**2) - G_/(8*L_**2) + 5*A_**2/(24*L_**3)
print("symbolic v2 - 2 e1 =", sp.simplify(v2 - 2*e1s))
