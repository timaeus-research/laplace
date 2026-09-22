"""1D localised anharmonic mean: sharp rates. c = -alpha/(2 lam^2) + g x0/lam, P_t = -alpha t/(2(t lam+g)^2) + g x0/(t lam+g).
Claims: t(t m - c) -> const (so |t m - c| <= K/t), t^2 (m - P_t) -> const (eq:mean's O(S^2) remainder)."""
import numpy as np
from scipy.integrate import quad
lam, alpha, gam = 1.3, 0.7, 1.1; g, x0 = 0.8, 0.6
def ell(x): return lam*x**2/2 + alpha*x**3/6 + gam*x**4/24
def mean_loc(t):
    w = lambda x: np.exp(-t*ell(x) - g/2*(x-x0)**2); R = 12/np.sqrt(lam*t) + abs(x0)
    Z = quad(w, -R, R, epsabs=1e-15, epsrel=1e-14, limit=800)[0]
    return quad(lambda x: x*w(x), -R, R, epsabs=1e-15, epsrel=1e-14, limit=800)[0]/Z
c = -alpha/(2*lam**2) + g*x0/lam
# predicted second-order coefficient of t*m: t m = c + c2/t + ..., from the expansion (numerator/denominator to O(1/t^2))
# moments: <x> = a1/t + ..., <x^2> = 1/(lam t) + b2/t^2, <x^3> = -5 alpha/(2 lam^3 t^2); a1 = -alpha/(2 lam^2)
for t in [10.0, 40.0, 160.0, 640.0, 2560.0]:
    m = mean_loc(t); P = -alpha*t/(2*(t*lam+g)**2) + g*x0/(t*lam+g)
    print(f"t={t:g}: t*m={t*m:.8f} c={c:.8f} t(tm-c)={t*(t*m-c):.5f}  t^2(m-P_t)={t**2*(m-P):.5f}")
