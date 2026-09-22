import numpy as np
from scipy.integrate import quad, dblquad
a = 0.5; lam = np.array([1.0, 3.0]); alpha = a * lam**1.5; g = lam**2
l = lambda x, i: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + g[i] * x**4 / 24
L = lambda x, y: l(x, 0) + l(y, 1)
B = np.array([[2.0, 0.7], [0.7, 1.5]]); b = np.array([0.8, -0.4])
psi = lambda x, y: 0.5 * (B[0, 0] * x * x + 2 * B[0, 1] * x * y + B[1, 1] * y * y) + b[0] * x + b[1] * y
psid = lambda x, y: 0.5 * (B[0, 0] * x * x + B[1, 1] * y * y) + b[0] * x + b[1] * y
for t in [50.0, 200.0, 800.0]:
    R = 4.0 / np.sqrt(t)
    w = lambda y, x: np.exp(-t * L(x, y))
    Z = dblquad(w, -R, R, -R, R)[0]
    E = lambda f: dblquad(lambda y, x: f(x, y) * w(y, x), -R, R, -R, R)[0] / Z
    cov = E(lambda x, y: L(x, y) * psi(x, y)) - E(L) * E(psi)
    covd = E(lambda x, y: L(x, y) * psid(x, y)) - E(L) * E(psid)
    covoff = E(lambda x, y: L(x, y) * x * y) - E(L) * E(lambda x, y: x * y)
    pred = (B[0, 0] / (2 * lam[0]) + B[1, 1] / (2 * lam[1])) - (b[0] * alpha[0] / (2 * lam[0]**2) + b[1] * alpha[1] / (2 * lam[1]**2))
    print("t=%g: t^2 Cov[L,psi] = %.5f ; diagonal-probe %.5f ; off-diagonal t^2 Cov[L, u1 u2] = %.2e ; eq:covK (eigenframe) = %.5f" % (t, t**2 * cov, t**2 * covd, t**2 * covoff, pred))
