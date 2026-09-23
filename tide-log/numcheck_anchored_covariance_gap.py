"""Tide 97 numerical check: the anchored Gaussian *covariance* (susceptibility) gap for quadratic + linear probes.

Frame probe psi(u) = 1/2 sum_ij B_ij u_i u_j + sum_i b_i u_i.  Exact localised: t^2 Cov_loc(L, psi) = sum_i (B_ii/(2 lam_i) + b_i c_i) + C'_loc/t + O(t^-2),
  c_i = -alpha_i/(2 lam_i^2) + a_i/lam_i,  C'_loc = sum_i (B_ii c2'_i + 2 b_i m2_i) + sum_{i!=j} B_ij c_i c_j.
Anchored Gaussian N(m, Sigma), p_i = t lam_i + g, m_i = a_i/p_i:  Cov(1/2 u^T H u, psi) = 1/2 tr(H Sigma B Sigma) + (Hm)^T Sigma (B m) + b^T Sigma (H m), so
  t^2 Cov_anch = 1/2 sum_i B_ii (t lam_i/p_i)^2/lam_i + t^2 sum_ij lam_i a_i B_ij a_j/(p_i^2 p_j) + t^2 sum_i b_i lam_i a_i/p_i^2
               = sum_i (B_ii/(2 lam_i) + b_i a_i/lam_i) + [-g sum B_ii/lam_i^2 + sum_ij B_ij a_i a_j/(lam_i lam_j) - 2 g sum b_i a_i/lam_i^2]/t + O(t^-2).
Gap: leading  -sum_i b_i alpha_i/(2 lam_i^2);  1/t: sum_i B_ii Gam_ii + sum_{i!=j} B_ij (c_i c_j - a_i a_j/(lam_i lam_j)) + 2 sum_i b_i (m2_i + g a_i/lam_i^2),
  Gam_ii = 5 alpha^2/(4 lam^4) - 2 a alpha/lam^3 - gamma/(2 lam^3).
"""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); alpha = np.array([0.7, -0.4]); gamma = np.array([1.1, 0.8]); g = 0.8; u0 = np.array([0.55, -0.35]); a = g * u0
B = np.array([[0.9, 0.4], [0.4, 1.6]]); b = np.array([0.3, -0.5])
c = -alpha / (2 * lam**2) + a / lam
c2p = 5 * alpha**2 / (4 * lam**4) - 2 * a * alpha / lam**3 - gamma / (2 * lam**3) + (a**2 - g) / lam**2
meanCoeff2 = -5 * alpha**3 / (8 * lam**5) + 2 * alpha * gamma / (3 * lam**4)
m2 = meanCoeff2 + a * alpha**2 / lam**4 - a * gamma / (2 * lam**3) + alpha * g / lam**3 - alpha * a**2 / (2 * lam**3) - a * g / lam**2
Gam = 5 * alpha**2 / (4 * lam**4) - 2 * a * alpha / lam**3 - gamma / (2 * lam**3)
lead_gap = -np.sum(b * alpha / (2 * lam**2))
off = B[0, 1] * (c[0] * c[1] - a[0] * a[1] / (lam[0] * lam[1])) * 2
gap1 = np.sum(np.diag(B) * Gam) + off + 2 * np.sum(b * (m2 + g * a / lam**2))
ell = lambda i, x: lam[i] * x**2 / 2 + alpha[i] * x**3 / 6 + gamma[i] * x**4 / 24
def mom(i, t):
    lim = 14 / np.sqrt(t * lam[i]) + abs(u0[i]) + 2
    dens = lambda x: np.exp(-t * ell(i, x) - g * (x - u0[i])**2 / 2)
    I = lambda f: quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
    Z = I(lambda x: 1.0)
    E = lambda f: I(f) / Z
    m1, mL = E(lambda x: x), E(lambda x: ell(i, x))
    return dict(m1=m1, m2=E(lambda x: x**2), covL1=E(lambda x: ell(i, x) * x) - mL * m1, covL2=E(lambda x: ell(i, x) * x**2) - mL * E(lambda x: x**2))
def cov_loc(t):
    M = [mom(i, t) for i in range(2)]
    return (0.5 * B[0, 0] * M[0]['covL2'] + 0.5 * B[1, 1] * M[1]['covL2'] + B[0, 1] * (M[0]['covL1'] * M[1]['m1'] + M[0]['m1'] * M[1]['covL1'])
            + b[0] * M[0]['covL1'] + b[1] * M[1]['covL1'])
def cov_anch(t):
    p = t * lam + g
    return (0.5 * np.sum(np.diag(B) * (t * lam / p)**2 / lam) + t**2 * sum(lam[i] * a[i] * B[i, j] * a[j] / (p[i]**2 * p[j]) for i in range(2) for j in range(2))
            + t**2 * np.sum(b * lam * a / p**2))
def cov_anch_direct(t):
    p = t * lam + g; m = a / p
    def E1(i, f):
        lim = 14 / np.sqrt(p[i]) + abs(m[i]) + 1
        dens = lambda x: np.exp(-p[i] * x**2 / 2 + a[i] * x)
        Z = quad(dens, -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0]
        return quad(lambda x: f(x) * dens(x), -lim, lim, epsabs=1e-16, epsrel=1e-14, limit=200)[0] / Z
    q = lambda i: (lambda x: lam[i] * x**2 / 2)
    covQ1 = [E1(i, lambda x: q(i)(x) * x) - E1(i, q(i)) * E1(i, lambda x: x) for i in range(2)]
    covQ2 = [E1(i, lambda x: q(i)(x) * x**2) - E1(i, q(i)) * E1(i, lambda x: x**2) for i in range(2)]
    m1 = [E1(i, lambda x: x) for i in range(2)]
    return t**2 * (0.5 * B[0, 0] * covQ2[0] + 0.5 * B[1, 1] * covQ2[1] + B[0, 1] * (covQ1[0] * m1[1] + m1[0] * covQ1[1]) + b[0] * covQ1[0] + b[1] * covQ1[1])
lead_loc = np.sum(np.diag(B) / (2 * lam) + b * c); lead_anch = np.sum(np.diag(B) / (2 * lam) + b * a / lam)
C1_anch = -g * np.sum(np.diag(B) / lam**2) + sum(B[i, j] * a[i] * a[j] / (lam[i] * lam[j]) for i in range(2) for j in range(2)) - 2 * g * np.sum(b * a / lam**2)
print(f"leading: loc {lead_loc:.6f}  anch {lead_anch:.6f}  gap {lead_loc - lead_anch:.6f}  predicted -sum b alpha/(2 lam^2) = {lead_gap:.6f}")
print(f"1/t: anch coefficient {C1_anch:.6f}; predicted 1/t gap coefficient = {gap1:.6f}")
t = 50.0; print(f"t={t}: t^2 Cov_anch formula {cov_anch(t):.10f}  direct {cov_anch_direct(t):.10f}")
# 1D check of m2 closed form: t (t<x> - c) -> m2
for i in range(2):
    tt = 640.0; M = mom(i, tt); print(f"coord {i}: t(t<x>-c) = {tt*(tt*M['m1'] - c[i]):.5f} vs m2 = {m2[i]:.5f};  t(t<x^2> - 1/lam) = {tt*(tt*M['m2'] - 1/lam[i]):.5f} vs c2' = {c2p[i]:.5f}")
for t in [40.0, 80.0, 160.0, 320.0, 640.0]:
    Vl, Va = t**2 * cov_loc(t), cov_anch(t)
    print(f"t={t:5.0f}: t^2Cov_loc = {Vl:.6f}  t^2Cov_anch = {Va:.6f}  gap = {Vl - Va:.6f}  t(gap - lead) = {t*(Vl - Va - lead_gap):.5f} vs {gap1:.5f}   t^2 rem = {t**2*(Vl - Va - lead_gap - gap1/t):.3f}")
