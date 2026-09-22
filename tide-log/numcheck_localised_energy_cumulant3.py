"""Tide 86 numerical check: the third cumulant of the localised energy on E2 (the LLC governs the second temperature derivative).

Per frame coordinate i (1D localised measure with anchor a_i = g u0_i):
 (a) t^4 <x^7>_loc bounded (signed seventh moment O(t^-4)); Stein consistency at leading order:
     4 c3 + 3 a/lam^2 - lam c5 - (alpha/2)(15/lam^3) = 0  with c3 = locThirdCoeff, c5 = locFifthCoeff (leading localised 3rd/5th);
 (b) t^3 <ell^3>_loc -> 15/8,  t^3 kappa3_loc(ell) -> 1  (kappa3 = <ell^3> - 3<ell^2><ell> + 2<ell>^3);
E2 (d = 2):
 (c) -d/dt Var_loc(L) (central differences) = sum_i kappa3_i = direct kappa3(L) (2D quadrature at t = 40);
 (d) t^3 d^2/dt^2 <L>_loc -> d = 2.
"""
import numpy as np
from scipy.integrate import quad, dblquad

lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8
u0 = np.array([0.55, -0.35]); a = g * u0
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24

def E1(i, t, f):
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    Z = quad(dens, -lim, lim, epsabs=1e-15, epsrel=1e-14)[0]
    return quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-15, epsrel=1e-14)[0] / Z

def kappa3_1d(i, t):
    m1 = E1(i, t, lambda x: ell(i, x)); m2 = E1(i, t, lambda x: ell(i, x)**2); m3 = E1(i, t, lambda x: ell(i, x)**3)
    return m3 - 3 * m2 * m1 + 2 * m1**3, m3, m2, m1

# (a) Stein consistency with the seabed's leading coefficients (c3 = -5 alpha/(2 lam^3) + 3a/lam^2? -- computed from moments instead)
for i in range(2):
    c3 = [t**2 * E1(i, t, lambda x: x**3) for t in [320.0, 640.0]]
    c5 = [t**3 * E1(i, t, lambda x: x**5) for t in [320.0, 640.0]]
    m7 = [t**4 * E1(i, t, lambda x: x**7) for t in [80.0, 160.0, 320.0, 640.0]]
    print(f"coord {i}: t^2 m3 -> {c3[0]:.6f}, {c3[1]:.6f}   t^3 m5 -> {c5[0]:.6f}, {c5[1]:.6f}   t^4 m7 = {m7[0]:.5f}, {m7[1]:.5f}, {m7[2]:.5f}, {m7[3]:.5f}")
    c3l, c5l = c3[1], c5[1]
    print(f"   Stein leading consistency 4c3 + 3a/lam^2 - lam c5 - (alpha/2)(15/lam^3) = {4*c3l + 3*a[i]/lam[i]**2 - lam[i]*c5l - alpha[i]/2*15/lam[i]**3:.5f} (-> 0)")
# (b)
for t in [80.0, 160.0, 320.0, 640.0]:
    k = [kappa3_1d(i, t) for i in range(2)]
    print(f"t={t:5.0f}: t^3<ell^3>_loc = {t**3*k[0][1]:.5f}, {t**3*k[1][1]:.5f} (->1.875)   t^3 kappa3 = {t**3*k[0][0]:.5f}, {t**3*k[1][0]:.5f} (->1)   sum t^3 kappa3 = {t**3*(k[0][0]+k[1][0]):.5f} (->2)")
# (c),(d)
def meanL(t): return sum(E1(i, t, lambda x: ell(i, x)) for i in range(2))
def varL(t): return sum(E1(i, t, lambda x: ell(i, x)**2) - E1(i, t, lambda x: ell(i, x))**2 for i in range(2))
t = 40.0; h = t * 1e-3
dVar = -(varL(t + h) - varL(t - h)) / (2 * h)
d2mean = (meanL(t + h) - 2 * meanL(t) + meanL(t - h)) / h**2
k3sum = sum(kappa3_1d(i, t)[0] for i in range(2))
Lsep = lambda x, y: ell(0, x) + ell(1, y)
dens2 = lambda y, x: np.exp(-t * Lsep(x, y) - g * ((x - u0[0])**2 + (y - u0[1])**2) / 2)
lim = [10 / np.sqrt(t * lam[i]) + abs(u0[i]) + 1.5 for i in range(2)]
I = lambda f: dblquad(lambda y, x: f(x, y) * dens2(y, x), -lim[0], lim[0], -lim[1], lim[1], epsabs=1e-13, epsrel=1e-12)[0]
Z = I(lambda x, y: 1.0); M1 = I(Lsep) / Z; M2 = I(lambda x, y: Lsep(x, y)**2) / Z; M3 = I(lambda x, y: Lsep(x, y)**3) / Z
k3direct = M3 - 3 * M2 * M1 + 2 * M1**3
print(f"(c) t={t}: -dVar/dt = {dVar:.9e}   sum kappa3_i = {k3sum:.9e}   direct kappa3(L) (2D) = {k3direct:.9e}   d2<L>/dt2 = {d2mean:.9e}")
for t in [80.0, 160.0, 320.0, 640.0]:
    h = t * 2e-3
    d2 = (meanL(t + h) - 2 * meanL(t) + meanL(t - h)) / h**2
    print(f"(d) t={t:5.0f}: t^3 d2<L>/dt2 = {t**3*d2:.5f} (-> 2)")
