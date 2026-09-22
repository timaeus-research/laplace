import numpy as np
from scipy.integrate import quad
# E2 in Frobenius form: for the exact separable oscillator, t * ||Cov - S||_F / ||S||_F -> |a^2 - 1/2|, S = diag(1/(lam t))
a = 0.5; lams = np.array([1.0, 2.0, 5.0, 10.0])
def var1d(lam, t):
    alpha = a * lam**1.5; g = lam**2
    l = lambda x: lam * x**2 / 2 + alpha * x**3 / 6 + g * x**4 / 24
    w = lambda x: np.exp(-t * l(x))
    Z = quad(w, -np.inf, np.inf, epsabs=1e-14, epsrel=1e-13)[0]
    m1 = quad(lambda x: x * w(x), -np.inf, np.inf, epsabs=1e-14, epsrel=1e-13)[0] / Z
    m2 = quad(lambda x: x**2 * w(x), -np.inf, np.inf, epsabs=1e-14, epsrel=1e-13)[0] / Z
    return m1, m2 - m1**2
for t in [10.0, 100.0, 1000.0]:
    V = np.array([var1d(l, t)[1] for l in lams]); S = 1 / (lams * t)
    frob_rel = np.sqrt(((V - S)**2).sum() / (S**2).sum())
    print("t=%g: t * Frob_rel = %.5f (-> |a^2-1/2| = %.3f)" % (t, t * frob_rel, abs(a**2 - 0.5)))
# ambient mean and covariance under rotation (d=4, random Q): Cov_w = Q diag(V) Q^T, <w> - c = Q <u>
rng = np.random.default_rng(5); Qm, _ = np.linalg.qr(rng.normal(size=(4, 4))); c = rng.normal(size=4); t = 100.0
m = np.array([var1d(l, t)[0] for l in lams]); V = np.array([var1d(l, t)[1] for l in lams])
Cw = Qm @ np.diag(V) @ Qm.T; Sw = Qm @ np.diag(1 / (lams * t)) @ Qm.T
print("t * ||Cov_w - S_w||_F/||S_w||_F =", t * np.sqrt(((Cw - Sw)**2).sum() / (Sw**2).sum()))
print("t (<w> - c) = Q (t <u>) =", np.round(Qm @ (t * m), 5), " limit -Q alpha/(2 lam^2) =", np.round(-Qm @ (a * lams**1.5 / (2 * lams**2)), 5))
