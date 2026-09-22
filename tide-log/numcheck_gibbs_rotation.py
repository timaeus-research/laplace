import numpy as np
from scipy.integrate import dblquad
# rotated separable anharmonic in d=2: L(w) = sum_i l_i(u_i), u = Q^T (w - w*), Q random orthogonal
rng = np.random.default_rng(3)
a = 0.5; lam = np.array([1.0, 4.0]); alpha = a * lam**1.5 * np.array([1, -1]); g = lam**2
th = 0.7; Q = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]]); wstar = np.array([0.3, -0.2]); t = 15.0
l = lambda u, i: lam[i] * u**2 / 2 + alpha[i] * u**3 / 6 + g[i] * u**4 / 24
def Lw(w1, w2):
    u = Q.T @ (np.array([w1, w2]) - wstar)
    return l(u[0], 0) + l(u[1], 1)
def Lu(u1, u2): return l(u1, 0) + l(u2, 1)
R = 2.5
Zw = dblquad(lambda y, x: np.exp(-t * Lw(x, y)), wstar[0] - R, wstar[0] + R, wstar[1] - R, wstar[1] + R)[0]
Zu = dblquad(lambda y, x: np.exp(-t * Lu(x, y)), -R, R, -R, R)[0]
print("Z invariant under the affine isometry:", abs(Zw - Zu) / Zu)
def Ew(f): return dblquad(lambda y, x: f(x, y) * np.exp(-t * Lw(x, y)), wstar[0] - R, wstar[0] + R, wstar[1] - R, wstar[1] + R)[0] / Zw
def Eu(f): return dblquad(lambda y, x: f(x, y) * np.exp(-t * Lu(x, y)), -R, R, -R, R)[0] / Zu
mw = np.array([Ew(lambda x, y: x), Ew(lambda x, y: y)])
mu = np.array([Eu(lambda x, y: x), Eu(lambda x, y: y)])
print("mean rotates: ", np.abs(mw - (wstar + Q @ mu)).max())
Cw = np.array([[Ew(lambda x, y: x * x), Ew(lambda x, y: x * y)], [Ew(lambda x, y: x * y), Ew(lambda x, y: y * y)]]) - np.outer(mw, mw)
Cu = np.array([[Eu(lambda x, y: x * x), Eu(lambda x, y: x * y)], [Eu(lambda x, y: x * y), Eu(lambda x, y: y * y)]]) - np.outer(mu, mu)
print("Cov rotates: ", np.abs(Cw - Q @ Cu @ Q.T).max(), " (off-diagonal Cu =", Cu[0, 1], ")")
print("projected variances Q_i^T Cw Q_i = Var_u_i:", np.abs(np.diag(Q.T @ Cw @ Q) - np.diag(Cu)).max())
print("LLC invariant: t<L>_w = %.5f  t<L>_u = %.5f" % (t * Ew(Lw), t * Eu(Lu)))
