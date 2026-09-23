"""Numerical check for tide 106 (minibatch-scaled). Anchored model P_t = tH + g, m_t = P_t^{-1} g w0, h = eta/t.
S_ij(t) = (2h [i=j] + h^2 t^2 Chat_ij)/(1 - rho_i rho_j), tau2_mb(t) = 1/2 sum lam lam S^2 w2_j + sum lam lam mh mh S w1_j.
(A) fixed C: S_ij -> eta Chat_ij/(lam_i+lam_j - eta lam_i lam_j); tau2_mb(t) -> Linf = 1/2 sum lam lam Sinf^2 w2inf_j (mean part -> 0); t^2 tau2 -> inf.
(B) C = C0/t: t S_ij -> (2 eta [i=j] + eta^2 C0hat_ij)/(eta(lam_i+lam_j - eta lam_i lam_j)); t^2 tau2_mb -> Llin = 1/2 sum lam lam (tS)^2 w2inf_j; C0 = 0 recovers L_eta."""
import numpy as np
rng = np.random.default_rng(6)
d = 3; lam = np.array([1.0, 2.5, 0.7]); g = 0.7; eta = 0.3
Q, _ = np.linalg.qr(rng.standard_normal((d, d))); U = Q; H = U @ np.diag(lam) @ U.T
B = rng.standard_normal((d, d)); C0 = 0.05 * B @ B.T; C0h = U.T @ C0 @ U
w0 = rng.standard_normal(d)
x = eta*lam; rinf = 1 - x
w2inf = (1 + rinf**2)/(1 - rinf**2); w1inf = (1 + rinf)/(1 - rinf)
Sinf = eta*C0h/(lam[:, None] + lam[None, :] - eta*np.outer(lam, lam))
Linf = 0.5*np.sum(np.outer(lam, lam)*Sinf**2*w2inf[None, :])
tSlin = (2*eta*np.eye(d) + eta**2*C0h)/(eta*(lam[:, None] + lam[None, :] - eta*np.outer(lam, lam)))
Llin = 0.5*np.sum(np.outer(lam, lam)*tSlin**2*w2inf[None, :])
Leta = np.sum((1 + (1-x)**2)/(4*eta*lam*(1 - x/2)**3))
tS0 = (2*eta*np.eye(d))/(eta*(lam[:, None] + lam[None, :] - eta*np.outer(lam, lam))); L0 = 0.5*np.sum(np.outer(lam, lam)*tS0**2*w2inf[None, :])
print("Linf", Linf, " Llin", Llin, " L_eta (ULA)", Leta, " Llin with C0=0", L0)
def tau2(t, C):
    h = eta/t; p = t*lam + g; rho = 1 - h*p; Ch = U.T @ C @ U
    S = (2*h*np.eye(d) + h**2*t**2*Ch)/(1 - np.outer(rho, rho))
    m = np.linalg.solve(t*H + g*np.eye(d), g*w0); mh = U.T @ m
    w2 = (1+rho**2)/(1-rho**2); w1 = (1+rho)/(1-rho)
    return 0.5*np.sum(np.outer(lam, lam)*S**2*w2[None, :]) + np.sum(np.outer(lam*mh, lam*mh)*S*w1[None, :]), np.sum(np.outer(lam*mh, lam*mh)*S*w1[None, :])
for t in [10, 40, 160, 640, 2560, 10240]:
    a, am = tau2(t, C0); b, bm = tau2(t, C0/t)
    print(f"t={t:6d} fixed C: tau2={a:.6f} (mean part {am:.2e}) t^2 tau2={t**2*a:.3e} | C0/t: t^2 tau2={t**2*b:.6f} (mean part {t**2*bm:.2e})")
