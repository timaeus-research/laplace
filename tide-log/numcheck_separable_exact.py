import numpy as np
from scipy.integrate import quad
# separable anharmonic oscillator in the note's parametrisation: l_i(x) = lam_i x^2/2 + alpha_i x^3/6 + g_i x^4/24,
# alpha_i^2 = a^2 lam_i^3, g_i = lam_i^2
def moments(lam, alpha, g, t):
    l = lambda x: lam * x**2 / 2 + alpha * x**3 / 6 + g * x**4 / 24
    w = lambda x: np.exp(-t * l(x))
    Z = quad(w, -np.inf, np.inf)[0]
    m1 = quad(lambda x: x * w(x), -np.inf, np.inf)[0] / Z
    m2 = quad(lambda x: x**2 * w(x), -np.inf, np.inf)[0] / Z
    mL = quad(lambda x: l(x) * w(x), -np.inf, np.inf)[0] / Z
    return Z, m1, m2 - m1**2, mL
a = 0.5
lams = np.array([1.0, 3.0, 10.0])
for t in [10.0, 100.0, 1000.0]:
    rel = []
    for lam in lams:
        alpha = a * lam ** 1.5; g = lam ** 2
        Z, m1, var, mL = moments(lam, alpha, g, t)
        rel.append(t * (lam * t * var - 1))
        # mean: t*m1 -> -alpha/(2 lam^2)
        mean_lim = -alpha / (2 * lam**2)
        tl = t * mL
        if t == 1000.0:
            print("lam=%g: t*<x> = %.5f vs -alpha/(2lam^2) = %.5f ; t<l> = %.5f (-> 1/2)" % (lam, t * m1, mean_lim, tl))
    print("t=%g: t*(lam t Var - 1) per coordinate =" % t, np.round(rel, 4), " predicted a^2-1/2 =", a**2 - 0.5)
# product structure: cross covariance vanishes and Z factorises (2D check by nested quadrature)
lam1, lam2 = 1.0, 3.0; t = 20.0
l = lambda x, lam: lam * x**2 / 2 + a * lam**1.5 * x**3 / 6 + lam**2 * x**4 / 24
from scipy.integrate import dblquad
w2 = lambda y, x: np.exp(-t * (l(x, lam1) + l(y, lam2)))
Z2 = dblquad(w2, -3, 3, -3, 3)[0]
Z1a = quad(lambda x: np.exp(-t * l(x, lam1)), -3, 3)[0]; Z1b = quad(lambda x: np.exp(-t * l(x, lam2)), -3, 3)[0]
print("Z factorises:", abs(Z2 - Z1a * Z1b) / Z2)
mxy = dblquad(lambda y, x: x * y * w2(y, x), -3, 3, -3, 3)[0] / Z2
mx = dblquad(lambda y, x: x * w2(y, x), -3, 3, -3, 3)[0] / Z2
my = dblquad(lambda y, x: y * w2(y, x), -3, 3, -3, 3)[0] / Z2
print("cross covariance:", mxy - mx * my)
