import numpy as np
rng = np.random.default_rng(1)
d = 6
A = rng.normal(size=(d, d)); P = A @ A.T + 0.3 * np.eye(d)
p, U = np.linalg.eigh(P)
S = np.linalg.inv(P)
# A: directional one-loop variance: s^T (S + S Pi S) s = 1/p_s + Pi_ss / p_s^2 for a unit eigenvector s, any symmetric Pi
Pi = rng.normal(size=(d, d)); Pi = Pi + Pi.T
for i in range(d):
    s = U[:, i]
    lhs = s @ (S + S @ Pi @ S) @ s
    rhs = 1 / p[i] + (s @ Pi @ s) / p[i] ** 2
    assert abs(lhs - rhs) < 1e-12, (lhs, rhs)
print("A directional one-loop: ok")
# B/C: perturbation Sigma' = P^{-1} + U diag(delta) U^T
delta = rng.normal(size=d)
Sp = S + U @ np.diag(delta) @ U.T
frob_rel2 = ((Sp - S) ** 2).sum() / (S ** 2).sum()
print("Frob_rel^2 = sum delta^2 / sum 1/p^2:", abs(frob_rel2 - (delta ** 2).sum() / (1 / p ** 2).sum()))
llc_shift = 0.5 * np.trace(P @ Sp) - d / 2
print("LLC shift = 1/2 sum p delta:", abs(llc_shift - 0.5 * (p * delta).sum()))
# stiff-direction perturbation
imax = np.argmax(p); imin = np.argmin(p); kappa = p[imax] / p[imin]
dl = 0.3
frob_rel = dl / np.sqrt((1 / p ** 2).sum()); llc_rel = dl * p[imax] / d
print("stiff: Frob_rel <= delta*pmin:", frob_rel <= dl * p[imin] + 1e-15, " LLC_rel/Frob_rel = %.2f >= kappa/d = %.2f" % (llc_rel / frob_rel, kappa / d))
# flat-direction perturbation
frob_rel_f = dl / np.sqrt((1 / p ** 2).sum()); llc_rel_f = dl * p[imin] / d
print("flat: Frob_rel >= delta*pmin/sqrt(d):", frob_rel_f >= dl * p[imin] / np.sqrt(d) - 1e-15, " Frob_rel/LLC_rel = %.2f >= sqrt(d) = %.2f" % (frob_rel_f / llc_rel_f, np.sqrt(d)))
