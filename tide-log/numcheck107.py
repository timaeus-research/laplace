"""Numerical check for tide 107 (fulllaw-llc). Per-sample Hessians H_i (i<n) with mean H, D_i = H_i - H; P = tH+g, A = 1-hP,
N = 2hI + h^2 t^2 C_g, c = h^2 t^2 (1-m/n)/(m(n-1)). Full law Sigma = A Sigma A^T + N + c sum_i D_i Sigma D_i^T (iterate).
Claims: tr(H Sigma_full) >= tr(H Sigma_mb) + c tr(H sum D_i Sigma_mb D_i^T) >= tr(H Sigma_mb) >= tr(H Sigma_ULA);
frame formula tr(H sum_i D_i S D_i^T) = sum_i sum_j lam_j sum_kl Dhat_i[j,k] Shat[k,l] Dhat_i[j,l]."""
import numpy as np
rng = np.random.default_rng(7)
d = 3; nsamp = 5; m = 2; t = 20.0; g = 0.7; h = 0.1/t
Hs = []
for _ in range(nsamp):
    B = rng.standard_normal((d, d)); Hs.append(0.4*B @ B.T)
H = sum(Hs)/nsamp; lam, U = np.linalg.eigh(H); Ds = [Hi - H for Hi in Hs]
P = t*H + g*np.eye(d); A = np.eye(d) - h*P
B = rng.standard_normal((d, d)); Cg = 0.05*B @ B.T
N = 2*h*np.eye(d) + h**2*t**2*Cg; c = h**2*t**2*(1 - m/nsamp)/(m*(nsamp-1))
lip = np.linalg.norm(A, np.inf)*np.linalg.norm(A.T, np.inf) + c*sum(np.linalg.norm(D, np.inf)*np.linalg.norm(D.T, np.inf) for D in Ds)
print("Lipschitz constant", lip, "(need < 1)")
def mb(X): return A @ X @ A.T + N
def full(X): return mb(X) + c*sum(D @ X @ D.T for D in Ds)
Smb = np.zeros((d, d)); Sf = np.zeros((d, d))
for _ in range(20000): Smb = mb(Smb); Sf = full(Sf)
print("fixed point residuals", np.abs(mb(Smb)-Smb).max(), np.abs(full(Sf)-Sf).max())
p = t*lam + g; rho = 1 - h*p; kap = 1 - h*p/2; Ch = U.T @ Cg @ U
Sula = U @ np.diag(1/(p*kap)) @ U.T
first = c*sum(D @ Smb @ D.T for D in Ds)
print("eigmin(Sf - Smb)", np.linalg.eigvalsh(Sf - Smb).min(), " eigmin(Sf - Smb - first)", np.linalg.eigvalsh(Sf - Smb - first).min())
trF, trM, trU = np.trace(H @ Sf), np.trace(H @ Smb), np.trace(H @ Sula)
print(f"tr(H Sf)={trF:.6f} >= tr(H Smb)+c tr(H stateTerm)={trM + np.trace(H @ first):.6f} >= tr(H Smb)={trM:.6f} >= tr(H Sula)={trU:.6f}")
print("tide101 closed form tr(H Smb) =", np.sum(lam*(1 + h*t**2*np.diag(Ch)/2)/(p*kap)))
Sh = U.T @ Smb @ U
frame = sum(sum(lam[j]*sum((U.T @ D @ U)[j, k]*Sh[k, l]*(U.T @ D @ U)[j, l] for k in range(d) for l in range(d)) for j in range(d)) for D in Ds)
print("first-order trace tr(H sum D Smb D^T) =", np.trace(H @ sum(D @ Smb @ D.T for D in Ds)), " frame formula", frame)
