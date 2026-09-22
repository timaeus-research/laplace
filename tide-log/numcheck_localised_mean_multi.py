"""E2's rotated anharmonic oscillator with an isotropic Gaussian localiser, d = 2:
measure e^{-t L(A w) - (g/2)|w - w0|^2}, A w = Q^T (w - c). Check
 (A) t <(Aw)_i>_loc -> v_i = -alpha_i/(2 lam_i^2) + g u0_i/lam_i, u0 = A w0   (error ~ t^{-1/2} proved, t^{-1} numerically)
 (B) <w>_loc - c ~ Q v / t = meanShift + g (tH)^{-1}(w0 - c)
 (C) <w>_loc - c vs meanShiftLoc + g S (w0 - c), S = (tH + g I)^{-1}  (error ~ t^{-3/2} proved, t^{-2} numerically)"""
import numpy as np
from scipy.integrate import dblquad
th = 0.6; Q = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
lam = np.array([1.3, 0.7]); alpha = np.array([0.7, -0.4]); gam = np.array([1.1, 0.9])
c = np.array([0.3, -0.2]); w0 = np.array([0.5, 0.9]); g = 0.8
u0 = Q.T @ (w0 - c)
H = Q @ np.diag(lam) @ Q.T
def ell(u): return np.sum(lam*u**2/2 + alpha*u**3/6 + gam*u**4/24)
def mean_loc(t):
    R = 12/np.sqrt(min(lam)*t) + 2*max(abs(u0))
    def dens(u1, u2):
        u = np.array([u1, u2]); return np.exp(-t*ell(u) - g/2*np.sum((u - u0)**2))
    Z = dblquad(lambda y, x: dens(x, y), -R, R, -R, R, epsabs=1e-13, epsrel=1e-12)[0]
    m = np.array([dblquad(lambda y, x: np.array([x, y])[i]*dens(x, y), -R, R, -R, R, epsabs=1e-13, epsrel=1e-12)[0]/Z for i in range(2)])
    return c + Q @ m   # <w>_loc = c + Q <u>_loc  (isotropic localiser is frame invariant)
v = -alpha/(2*lam**2) + g*u0/lam
for t in [10.0, 40.0, 160.0]:
    m = mean_loc(t)
    S = np.linalg.inv(t*H + g*np.eye(2)); S0 = np.linalg.inv(t*H)
    # meanShiftLoc = -1/2 S (t T:S), T_{ijk} = sum_p alpha_p Q_ip Q_jp Q_kp  ->  (T:S)_i = sum_p alpha_p Q_ip (Q^T S Q)_pp
    TS = Q @ (alpha * np.diag(Q.T @ S @ Q)); TS0 = Q @ (alpha * np.diag(Q.T @ S0 @ Q))
    predC = -0.5*S @ (t*TS) + g*S @ (w0 - c)
    predB = -0.5*S0 @ (t*TS0) + g*S0 @ (w0 - c)
    print(f"t={t:g}: t(<w>-c)={t*(m-c)}  Qv={Q@v}  |t(m-c)-Qv|*t^0.5={np.linalg.norm(t*(m-c)-Q@v)*t**0.5:.4f} *t={np.linalg.norm(t*(m-c)-Q@v)*t:.4f}")
    print(f"        predB check: |Qv/t - predB|={np.linalg.norm(Q@v/t-predB):.2e};  C: |m-c-predC|*t^1.5={np.linalg.norm(m-c-predC)*t**1.5:.4f} *t^2={np.linalg.norm(m-c-predC)*t**2:.4f}")
