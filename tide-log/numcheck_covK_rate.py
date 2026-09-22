"""Tide covK-rate: numerical check that eq:covK has relative error O(1/t) (E2).

1D: lam=2, a=1/2; psi = (B/2) x^2 + b x; C = B/(2 lam) - b alpha/(2 lam^2).  t * (t^2 Cov[l, psi] - C) should converge.
Pair covariances: t * (t^2 Cov[x^m, x^n] - c_mn) bounded for (m,n) in {(2,2),(3,2),(4,2),(2,1),(3,1),(4,1)}.
d=2 rotated: psi(w) = 1/2 (w-c)^T B (w-c) + b^T (w-c); t * (t^2 Cov[L, psi] - C_d) should converge.
"""
import numpy as np
from scipy.integrate import quad
from math import sqrt

def moments_1d(lam, alpha, gamma, t, nmax=6):
    ell = lambda x: lam * x**2 / 2 + alpha * x**3 / 6 + gamma * x**4 / 24
    w = lambda x: np.exp(-t * ell(x)); R = 14 / sqrt(lam * t)
    Z = quad(w, -R, R, limit=500, epsabs=1e-15, epsrel=1e-14)[0]
    E = lambda f: quad(lambda x: f(x) * w(x), -R, R, limit=500, epsabs=1e-15, epsrel=1e-14)[0] / Z
    m = {n: E(lambda x: x**n) for n in range(0, nmax + 1)}
    m['l'] = E(ell); m['lx'] = E(lambda x: ell(x) * x); m['lx2'] = E(lambda x: ell(x) * x**2)
    return m

lam = 2.0; a = 0.5; alpha = a * lam**1.5; gamma = lam**2
B = 3.0; b = 1.5
C = B / (2 * lam) - b * alpha / (2 * lam**2)
print("1D: t * (t^2 Cov[l, psi] - C), C = %.5f" % C)
pairs = {(2,2): 2/lam**2, (3,2): 0.0, (4,2): 0.0, (2,1): -2*alpha/lam**3, (3,1): 3/lam**2, (4,1): 0.0}
for t in [50, 100, 200, 400, 800]:
    m = moments_1d(lam, alpha, gamma, t)
    cov = B / 2 * (m['lx2'] - m['l'] * m[2]) + b * (m['lx'] - m['l'] * m[1])
    pc = ["(%d,%d):%.3f" % (mm, nn, t * (t**2 * (m[mm + nn] - m[mm] * m[nn]) - c)) for (mm, nn), c in pairs.items()]
    print("  t=%4d  %.4f  | pairs t*(t^2Cov - c):" % (t, t * (t**2 * cov - C)), " ".join(pc))

# d = 2 rotated full quadratic probe
rng = np.random.default_rng(3); d = 2
lam2 = np.array([1.0, 3.0]); alpha2 = a * lam2**1.5; gamma2 = lam2**2
Q, _ = np.linalg.qr(rng.normal(size=(d, d))); c = rng.normal(size=d)
Bs = rng.normal(size=(d, d)); Bm = Bs + Bs.T; bv = rng.normal(size=d)
Bp = Q.T @ Bm @ Q; bp = Q.T @ bv
Cd = sum(Bp[i, i] / (2 * lam2[i]) - bp[i] * alpha2[i] / (2 * lam2[i]**2) for i in range(d))
print("d=2 rotated: t * (t^2 Cov[L, psi] - C_d), C_d = %.5f" % Cd)
for t in [50, 100, 200, 400, 800]:
    ms = [moments_1d(lam2[i], alpha2[i], gamma2[i], t, 4) for i in range(d)]
    cov = 0.0
    for i in range(d):
        cov += Bp[i, i] / 2 * (ms[i]['lx2'] - ms[i]['l'] * ms[i][2]) + bp[i] * (ms[i]['lx'] - ms[i]['l'] * ms[i][1])
        for j in range(d):
            if j != i:
                cov += Bp[i, j] / 2 * (ms[j][1] * (ms[i]['lx'] - ms[i]['l'] * ms[i][1]) + ms[i][1] * (ms[j]['lx'] - ms[j]['l'] * ms[j][1]))
    print("  t=%4d  %.4f" % (t, t * (t**2 * cov - Cd)))
