"""Tide 109 numerical check: the general scaled-noise regime t*Chat_t -> B for the minibatch long-run variance."""
import numpy as np
rng = np.random.default_rng(9)
lam = np.array([1.0, 2.5, 0.7]); d = 3; eta = 0.3; g = 0.7
A = rng.normal(size=(d, d)); Q, _ = np.linalg.qr(A)           # orthogonal frame
def psd(): M = rng.normal(size=(d, d)); return M @ M.T
Bmat = psd(); Dmat = psd(); Cg = psd()
w0 = rng.normal(size=d); c = rng.normal(size=d); wh = Q.T @ (w0 - c)

def tau2(t, C):
    """tide 105 long-run variance on the anchored model (frame formula of mbAnchored_longRunVar)."""
    h = eta / t; p = t * lam + g; rho = 1 - h * p
    Ch = Q.T @ C @ Q
    S = (2 * h * np.eye(d) + h**2 * t**2 * Ch) / (1 - np.outer(rho, rho))
    mh = g * wh / p
    w2 = (1 + rho**2) / (1 - rho**2); w1 = (1 + rho) / (1 - rho)
    L = lam[:, None] * lam[None, :]
    return 0.5 * np.sum(L * S**2 * w2[None, :]) + np.sum(L * np.outer(mh, mh) * S * w1[None, :])

def LB(Bh):
    rho = 1 - eta * lam; D = 1 - np.outer(rho, rho)
    E = (2 * eta * np.eye(d) + eta**2 * Bh) / D
    w2 = (1 + rho**2) / (eta * lam * (2 - eta * lam))
    L = lam[:, None] * lam[None, :]
    return 0.5 * np.sum(L * E**2 * w2[None, :])

Leta = np.sum((1 + (1 - eta * lam)**2) / (4 * eta * lam * (1 - eta * lam / 2)**3))
print("L_eta =", Leta, " LB(0) =", LB(np.zeros((d, d))))
print("regime t*C_t -> B  (C_t = B/t + D/t^1.5):  target LB =", LB(Q.T @ Bmat @ Q))
for t in [1e2, 1e3, 1e4, 1e5, 1e6]:
    print(f"  t={t:8.0e}  t^2 tau2 = {t**2 * tau2(t, Bmat / t + Dmat / t**1.5):.6f}")
print("regime C_t = C0/t^2 (superlinear batch): target L_eta =", Leta)
for t in [1e2, 1e3, 1e4, 1e5, 1e6]:
    print(f"  t={t:8.0e}  t^2 tau2 = {t**2 * tau2(t, Bmat / t**2):.6f}")
nu = 3.0
print("batch n_t = nu t + 5 sqrt t, C_t = Cg/n_t:  target LB(Chat_g/nu) =", LB(Q.T @ Cg @ Q / nu))
for t in [1e2, 1e3, 1e4, 1e5, 1e6]:
    n = nu * t + 5 * np.sqrt(t)
    print(f"  t={t:8.0e}  t^2 tau2 = {t**2 * tau2(t, Cg / n):.6f}")
print("strictness: LB(B) - L_eta =", LB(Q.T @ Bmat @ Q) - Leta, " (>0);  LB(Cg/1) - LB(Cg/3) =", LB(Q.T @ Cg @ Q) - LB(Q.T @ Cg @ Q / 3), " (>0, monotone in 1/nu)")

print("--- v2 additions ---")
print("sublinear n_t = sqrt(t) (n_t -> inf, n_t/t -> 0): t^2 tau2 should diverge")
for t in [1e2, 1e3, 1e4, 1e5, 1e6]:
    print(f"  t={t:8.0e}  t^2 tau2 = {t**2 * tau2(t, Cg / np.sqrt(t)):.4e}")
def meanpart(t, C):
    h = eta / t; p = t * lam + g; rho = 1 - h * p
    Ch = Q.T @ C @ Q
    S = (2 * h * np.eye(d) + h**2 * t**2 * Ch) / (1 - np.outer(rho, rho))
    mh = g * wh / p; w1 = (1 + rho) / (1 - rho)
    L = lam[:, None] * lam[None, :]
    return np.sum(L * np.outer(mh, mh) * S * w1[None, :])
Bh = Q.T @ Bmat @ Q; rho_inf = 1 - eta * lam; Dm = 1 - np.outer(rho_inf, rho_inf)
Amean = np.sum(lam[:, None] * lam[None, :] * np.outer(g * wh / lam, g * wh / lam) * (2 * eta * np.eye(d) + eta**2 * Bh) / Dm * ((2 - eta * lam) / (eta * lam))[None, :])
print("mean coefficient: t^3 * meanpart(C_t = B/t + D/t^1.5) -> A_mean =", Amean)
for t in [1e2, 1e3, 1e4, 1e5, 1e6]:
    print(f"  t={t:8.0e}  t^3 mean = {t**3 * meanpart(t, Bmat / t + Dmat / t**1.5):.6f}")
