import numpy as np
rng = np.random.default_rng(0)
d = 3
A = rng.normal(size=(d, d)); Q = A @ A.T + d * np.eye(d)
p, U = np.linalg.eigh(Q)
h = 0.4 / p.max()
rho = 1 - h * p
s2 = 2 * h / (1 - rho**2)
# (a) Sigma_ULA = (Q - h/2 Q^2)^{-1} = U diag(s2) U^T, and s2 = 1/(p(1-hp/2))
Sig = np.linalg.inv(Q - (h / 2) * Q @ Q)
print("ulaCov = U diag(s2) U^T:", np.abs(Sig - U @ np.diag(s2) @ U.T).max())
print("s2 = 1/(p(1-hp/2)):", np.abs(s2 - 1 / (p * (1 - h * p / 2))).max())
print("s2 - 1/p = h/(2-hp):", np.abs(s2 - 1 / p - h / (2 - h * p)).max())
# (b) zero-start mean: E Sig_raw = U diag(s2 (1 - a)) U^T, a = (1/N) sum_{k<N} rho^{2(b+1+k)}
N, b, C, M = 5, 2, 4, 40000
a = np.array([np.mean([r ** (2 * (b + 1 + k)) for k in range(N)]) for r in rho])
a_closed = rho ** (2 * (b + 1)) * (1 - rho ** (2 * N)) / (N * (1 - rho**2))
print("a closed form:", np.abs(a - a_closed).max())
acc = np.zeros((d, d)); acc2 = 0.0
target = U @ np.diag(s2 * (1 - a)) @ U.T
for m in range(M):
    S = np.zeros((d, d))
    for c in range(C):
        x = np.zeros(d)
        for k in range(1, b + N + 1):
            x = x - h * Q @ x + np.sqrt(2 * h) * rng.normal(size=d)
            if k >= b + 1:
                S += np.outer(x, x)
    S /= C * N
    acc += S; acc2 += ((S - target) ** 2).sum()
mean = acc / M
print("E Sig_raw vs U diag(s2(1-a)) U^T (MC, M=%d):" % M, np.abs(mean - target).max(), " scale", np.abs(target).max(), " se~", np.sqrt(acc2 / M) / np.sqrt(M))
# (c) bias terms
print("bias vs Sig_ULA  = sum (s2 a)^2      :", (s2 * a).__pow__(2).sum())
print("bias vs Q^{-1}   = sum (s2(1-a)-1/p)^2:", ((s2 * (1 - a) - 1 / p) ** 2).sum())
print("  = sum (h/(2-hp) - s2 a)^2          :", ((h / (2 - h * p) - s2 * a) ** 2).sum())
print("a <= rho^{2(b+1)}:", np.all(a <= rho ** (2 * (b + 1)) + 1e-15))
