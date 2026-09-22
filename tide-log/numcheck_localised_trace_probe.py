"""Tide 81 numerical check: the invariant centred quadratic probe on E2's exact localised measure.

(a) exact bridge (2D quadrature, moderate t): -d/dt tr(B C(t)) = Cov_loc(L, (w - m(t))^T B (w - m(t)));
(b) second order (frame reduction, 1D quadratures, large t):
    t^2 (-d/dt tr(B C(t))) = tr(B H^{-1}) + 2 tr(B V)/t + O(t^-2),  V = Q diag(v_i) Q^T, v_i = c2'_i - c_i^2.
"""
import numpy as np
from scipy.integrate import quad, dblquad

lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8
th = 0.6; Q = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
c = np.array([0.3, -0.2]); w0 = np.array([0.9, 0.4]); u0 = Q.T @ (w0 - c)
B = np.array([[1.0, 0.4], [0.4, 2.0]])
Bt = Q.T @ B @ Q
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
Lsep = lambda u: ell(0, u[0]) + ell(1, u[1])

def frame_moments(i, t):
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    lim = 12 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    Z = quad(dens, -lim, lim, epsabs=1e-14, epsrel=1e-13)[0]
    E = lambda f: quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-14, epsrel=1e-13)[0] / Z
    m1 = E(lambda x: x); m2 = E(lambda x: x**2)
    covLx = E(lambda x: ell(i, x) * x) - E(lambda x: ell(i, x)) * m1
    covLx2 = E(lambda x: ell(i, x) * x**2) - E(lambda x: ell(i, x)) * m2
    return m1, m2 - m1**2, covLx, covLx2

def trBC(t):
    return sum(Bt[i, i] * frame_moments(i, t)[1] for i in range(2))

def bridge_frame(t):
    # sum_i Bt_ii (Cov[L,u_i^2] - 2 mu_i Cov[L,u_i]) where Cov[L,·] uses the full L = sum ell_i (cross terms vanish)
    return sum(Bt[i, i] * (fm[3] - 2 * fm[0] * fm[2]) for i in range(2) for fm in [frame_moments(i, t)])

def bridge_2d(t):
    # direct 2D quadrature of Cov_loc(L, (w-m)^T B (w-m)) in frame coordinates: w - m = Q (u - mu)
    mu = np.array([frame_moments(i, t)[0] for i in range(2)])
    dens = lambda y, x: np.exp(-t * Lsep((x, y)) - g * ((x - u0[0])**2 + (y - u0[1])**2) / 2)
    lim = [10 / np.sqrt(t * lam[i]) + abs(u0[i]) + 1.5 for i in range(2)]
    I = lambda f: dblquad(lambda y, x: f(x, y) * dens(y, x), -lim[0], lim[0], -lim[1], lim[1], epsabs=1e-12, epsrel=1e-11)[0]
    Z = I(lambda x, y: 1.0)
    probe = lambda x, y: (np.array([x, y]) - mu) @ Bt @ (np.array([x, y]) - mu)
    EL = I(lambda x, y: Lsep((x, y))) / Z
    Ep = I(probe) / Z
    ELp = I(lambda x, y: Lsep((x, y)) * probe(x, y)) / Z
    return ELp - EL * Ep

t = 40.0; h = 1e-3
fd = -(trBC(t + h) - trBC(t - h)) / (2 * h)
print(f"(a) t={t}: -d/dt tr(BC) (central diff) = {fd:.10f}")
print(f"    bridge via frame reduction        = {bridge_frame(t):.10f}")
print(f"    bridge via 2D quadrature          = {bridge_2d(t):.10f}")

Hinv = Q @ np.diag(1 / lam) @ Q.T
c1 = -alpha / (2 * lam**2) + g * u0 / lam
c2p = (5 * alpha**2 / (4 * lam**4) - gamma / (2 * lam**3) - 2 * g * u0 * alpha / lam**3 + (g**2 * u0**2 - g) / lam**2)
v = c2p - c1**2
V = Q @ np.diag(v) @ Q.T
print(f"(b) tr(B H^-1) = {np.trace(B @ Hinv):.8f}  (= sum Bt_ii/lam_i = {sum(Bt[i,i]/lam[i] for i in range(2)):.8f})")
print(f"    2 tr(B V)  = {2*np.trace(B @ V):.8f}")
for t in [80.0, 160.0, 320.0, 640.0]:
    val = bridge_frame(t)
    resid1 = t**2 * val - np.trace(B @ Hinv)
    resid2 = t * (resid1 - 2 * np.trace(B @ V) / t)
    print(f"    t={t:6.0f}: t(t^2(-d/dt trBC) - trBH^-1) = {t*resid1:.6f}   t^2*(... - 2trBV/t) = {t*resid2:.5f}")
