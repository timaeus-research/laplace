import numpy as np
from scipy.integrate import quad
lam, a = 2.0, 0.5; alpha = a * lam**1.5; g = lam**2
l = lambda x: lam * x**2 / 2 + alpha * x**3 / 6 + g * x**4 / 24
def E(f, t):
    w = lambda x: np.exp(-t * l(x)); Z = quad(w, -np.inf, np.inf, epsabs=1e-16, epsrel=1e-13)[0]
    return quad(lambda x: f(x) * w(x), -np.inf, np.inf, epsabs=1e-16, epsrel=1e-13)[0] / Z
B, b = 3.0, 1.5
for t in [100.0, 1000.0, 10000.0]:
    psi = lambda x: B / 2 * x**2 + b * x
    cov = E(lambda x: l(x) * psi(x), t) - E(l, t) * E(psi, t)
    cov2 = E(lambda x: l(x) * x**2, t) - E(l, t) * E(lambda x: x**2, t)
    cov1 = E(lambda x: l(x) * x, t) - E(l, t) * E(lambda x: x, t)
    print("t=%g: t^2 Cov[l,x^2] = %.5f (-> 1/lam = %.4f); t^2 Cov[l,x] = %.5f (-> -alpha/(2lam^2) = %.4f); t^2 Cov[l,psi] = %.5f (covK: B/(2lam) - b alpha/(2 lam^2) = %.4f)" % (t, t**2 * cov2, 1 / lam, t**2 * cov1, -alpha / (2 * lam**2), t**2 * cov, B / (2 * lam) - b * alpha / (2 * lam**2)))
# eq:covK's four terms, 1D: H=lam, S=1/(lam t), T=alpha, Q-independent
t = 1.0
S = 1 / (lam * t)
terms = [0.5 * lam * S * B * S, 0.5 * (S * b) * (alpha * S), -(t / 2) * b * S * lam * S * (alpha * S), -(t / 2) * (S * b) * (alpha * (S * lam * S))]
print("eq:covK terms at t=1:", np.round(terms, 5), " sum =", sum(terms), " vs B/(2lam) - b alpha/(2lam^2) =", B / (2 * lam) - b * alpha / (2 * lam**2))
