"""Tide 88 numerical check: the fourth cumulant of the localised energy and the third derivative of the mean energy.

1D localised anharmonic measure  exp(-t ell(x) - g (x - x0)^2 / 2),  ell = lam x^2/2 + alpha x^3/6 + gamma x^4/24.
Claims:  t^4 <x^8>_loc -> 105/lam^4  (rate 1/t);  t^5 <x^9>_loc bounded (signed ninth moment O(t^-5));
         t^4 <ell^4>_loc -> 105/16;   t^4 kappa_4(ell) -> 3   (Gamma(1/2, t): kappa_n = (n-1)!/(2 t^n));
         exactly d^3/dt^3 <L o A>_loc = - sum_i kappa_4(ell_i),  so  t^4 d^3/dt^3 <L>_loc -> -3 d;
         excess kurtosis kappa_4 / kappa_2^2 -> 12/d.
"""
import numpy as np
from scipy.integrate import quad

lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8
u0 = np.array([0.55, -0.35])
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24

def E1(i, t, f):
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    Z = quad(dens, -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
    return quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z

def cumulants(i, t):
    m = [E1(i, t, lambda x, n=n: ell(i, x)**n) for n in range(1, 5)]
    m1, m2, m3, m4 = m
    k2 = m2 - m1**2
    k3 = m3 - 3 * m2 * m1 + 2 * m1**3
    k4 = m4 - 4 * m3 * m1 - 3 * m2**2 + 12 * m2 * m1**2 - 6 * m1**4
    return m1, k2, k3, k4

print("105/lam^4 =", 105 / lam**4)
for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
    r = []
    for i in range(2):
        m8 = E1(i, t, lambda x: x**8); m9 = E1(i, t, lambda x: x**9); l4 = E1(i, t, lambda x: ell(i, x)**4)
        _, k2, k3, k4 = cumulants(i, t)
        r.append((t**4 * m8, t**5 * m9, t**4 * l4, t**4 * k4, k4 / k2**2))
    print(f"t={t:5.0f}: t^4 m8 = {r[0][0]:.4f}, {r[1][0]:.4f}   t^5 m9 = {r[0][1]:.4f}, {r[1][1]:.4f}   "
          f"t^4 <ell^4> = {r[0][2]:.5f}, {r[1][2]:.5f}   t^4 k4 = {r[0][3]:.5f}, {r[1][3]:.5f}   k4/k2^2 = {r[0][4]:.4f}, {r[1][4]:.4f}")
print("targets: t^4 <ell^4> -> 105/16 =", 105 / 16, "  t^4 k4 -> 3   k4/k2^2 -> 12 (1D)")

# third derivative of the mean energy (E2, d = 2): finite differences vs. -sum kappa_4
def meanL(t):
    return sum(E1(i, t, lambda x: ell(i, x)) for i in range(2))
for t in [40.0, 80.0, 160.0]:
    h = 0.02 * t
    d3 = (meanL(t + 1.5 * h) - 3 * meanL(t + 0.5 * h) + 3 * meanL(t - 0.5 * h) - meanL(t - 1.5 * h)) / h**3
    k4s = sum(cumulants(i, t)[3] for i in range(2))
    k2s = sum(cumulants(i, t)[1] for i in range(2))
    print(f"t={t:5.0f}: d^3<L>/dt^3 (FD) = {d3:.6e}   -sum k4 = {-k4s:.6e}   t^4 d^3<L> = {t**4*d3:.4f} (-> -3d = -6)   k4(L)/k2(L)^2 = {sum(cumulants(i,t)[3] for i in range(2))/k2s**2:.4f} (-> 12/d = 6)")
