import numpy as np
from scipy.integrate import quad
a = 0.5
for lam in [1.0, 3.0]:
    alpha = a * lam**1.5; g = lam**2
    A = alpha / (6 * lam * np.sqrt(lam)); B = g / (24 * lam**2)
    C2 = (45 * A**2 - 12 * B) / lam
    Cvar = C2 - (alpha / (2 * lam**2))**2
    print("lam=%g: C_var = C2 - m0^2 = %.6f ; alpha^2/lam^4 - g/(2 lam^3) = %.6f ; lam*C_var = %.4f (a^2-1/2 = %.4f)" % (lam, Cvar, alpha**2 / lam**4 - g / (2 * lam**3), lam * Cvar, a**2 - 0.5))
    l = lambda x: lam * x**2 / 2 + alpha * x**3 / 6 + g * x**4 / 24
    for t in [10.0, 100.0, 1000.0, 10000.0]:
        w = lambda x: np.exp(-t * l(x))
        Z = quad(w, -np.inf, np.inf, epsabs=1e-14, epsrel=1e-13)[0]
        m1 = quad(lambda x: x * w(x), -np.inf, np.inf, epsabs=1e-14, epsrel=1e-13)[0] / Z
        m2 = quad(lambda x: x**2 * w(x), -np.inf, np.inf, epsabs=1e-14, epsrel=1e-13)[0] / Z
        var = m2 - m1**2
        rel = t * (lam * t * var - 1) - (a**2 - 0.5)
        print("   t=%6g: |t(lam t Var - 1) - (a^2-1/2)| = %.2e ; times sqrt t = %.2e ; times t = %.2e" % (t, abs(rel), abs(rel) * np.sqrt(t), abs(rel) * t))
