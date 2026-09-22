"""Integration by parts for the anharmonic Gibbs measure: <l'(x)> = 0 i.e. lam<x> + (alpha/2)<x^2> + (gamma/6)<x^3> = 0,
and the second-order mean t^2(<x> + alpha/(2 lam^2 t)) -> B1 = -5 alpha^3/(8 lam^5) + 2 alpha gamma/(3 lam^4).
Also the general Stein identity k<x^{k-1}> = t<x^k l'(x)> for k = 2,3."""
import numpy as np
from scipy.integrate import quad
lam, alpha, gam = 1.3, 0.7, 1.1
def ell(x): return lam*x**2/2 + alpha*x**3/6 + gam*x**4/24
def dell(x): return lam*x + alpha*x**2/2 + gam*x**3/6
def mom(t, f):
    w = lambda x: np.exp(-t*ell(x)); R = 12/np.sqrt(lam*t) + 2
    Z = quad(w, -R, R, epsabs=1e-16, epsrel=1e-15, limit=800)[0]
    return quad(lambda x: f(x)*w(x), -R, R, epsabs=1e-16, epsrel=1e-15, limit=800)[0]/Z
B1 = -5*alpha**3/(8*lam**5) + 2*alpha*gam/(3*lam**4)
print("B1 predicted =", B1)
for t in [10.0, 40.0, 160.0, 640.0]:
    ibp0 = mom(t, dell); ibp2 = 2*mom(t, lambda x: x) - t*mom(t, lambda x: x**2*dell(x)); ibp3 = 3*mom(t, lambda x: x**2) - t*mom(t, lambda x: x**3*dell(x))
    m1 = mom(t, lambda x: x)
    print(f"t={t:g}: <l'>={ibp0:.2e}  2<x>-t<x^2 l'>={ibp2:.2e}  3<x^2>-t<x^3 l'>={ibp3:.2e}   t^2(<x>+alpha/(2lam^2 t))={t**2*(m1+alpha/(2*lam**2*t)):.6f}")
