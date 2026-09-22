"""Tide llc-two-loop: the energy to two loops in tensor form.
twoLoopEnergy = 1/2 tr(H S) + (t/12) theta(S) + (t/8) dumbbell(S) - (1/8) q(S),  S = (tH)^{-1},
theta = sum T_ijk T_lmn S_il S_jm S_kn = sum_ij S_ij bubble_ij,  dumbbell = (T:S) . (S (T:S)),  q = sum_ijkl Q4_ijkl S_ij S_kl.
Check: on rotated tensors it equals d/(2t) + sum_i (5 alpha_i^2/(24 lam_i^3) - gamma_i/(8 lam_i^2))/t^2 (exact identity), and
t * twoLoopEnergy approximates the exact t<L> with O(1/t^2) error; E2's a=1/2, d=10, t=3 gives 4.757."""
import numpy as np
from scipy.integrate import quad
from math import sqrt
rng = np.random.default_rng(7); d = 3
lam = np.array([1.0, 2.0, 5.0]); a = 0.5; alpha = a * lam**1.5; gamma = lam**2
Q, _ = np.linalg.qr(rng.normal(size=(d, d)))
H = Q @ np.diag(lam) @ Q.T
T = np.einsum('l,il,jl,kl->ijk', alpha, Q, Q, Q); Q4 = np.einsum('l,il,jl,kl,ml->ijkm', gamma, Q, Q, Q, Q)
def twoloop(t):
    S = np.linalg.inv(t * H)
    theta = np.einsum('ijk,lmn,il,jm,kn->', T, T, S, S, S)
    TS = np.einsum('lmn,mn->l', T, S); dumb = TS @ (S @ TS)
    q = np.einsum('ijkl,ij,kl->', Q4, S, S)
    return 0.5 * np.trace(H @ S) + t / 12 * theta + t / 8 * dumb - q / 8
c = sum(5 * alpha[i]**2 / (24 * lam[i]**3) - gamma[i] / (8 * lam[i]**2) for i in range(d))
for t in [5.0, 50.0]:
    print("t=%g  twoLoop=%.10f  closed form d/(2t)+c/t^2=%.10f" % (t, twoloop(t), d / (2 * t) + c / t**2))
def ell(l, al, g, x): return l * x**2 / 2 + al * x**3 / 6 + g * x**4 / 24
def energy(l, al, g, t):
    w = lambda x: np.exp(-t * ell(l, al, g, x)); R = 14 / sqrt(l * t)
    Z = quad(w, -R, R, limit=500, epsabs=1e-14, epsrel=1e-13)[0]
    return quad(lambda x: ell(l, al, g, x) * w(x), -R, R, limit=500, epsabs=1e-14, epsrel=1e-13)[0] / Z
print("t^2 * (t<L> - t*twoLoop):", ["%.4f" % (t**2 * (t * sum(energy(lam[i], alpha[i], gamma[i], t) for i in range(d)) - t * twoloop(t))) for t in [20, 50, 100, 200, 400]])
# E2: a = 1/2, d = 10, t = 3, note's parametrisation: c per coordinate = 5a^2/24 - 1/8
print("E2 d=10 a=1/2 t=3: two-loop prediction t<L> =", 10 * (0.5 + (5 * 0.25 / 24 - 1 / 8) / 3))
# GPT-6 Astra's regression test outside the separable family: H = I_2, T_112 = T_121 = T_211 = 1 (1-indexed),
# S = (1/t) I; theta = 3/t^3 (three cross-edge pairings), dumbbell = 1/t^3: distinguishes the two contractions.
T2 = np.zeros((2, 2, 2)); T2[0, 0, 1] = T2[0, 1, 0] = T2[1, 0, 0] = 1.0
for t in [2.0, 7.0]:
    S = np.eye(2) / t
    theta = np.einsum('ijk,lmn,il,jm,kn->', T2, T2, S, S, S); TS = np.einsum('lmn,mn->l', T2, S); dumb = TS @ (S @ TS)
    print("regression t=%g: theta=%.10f (3/t^3=%.10f)  dumbbell=%.10f (1/t^3=%.10f)" % (t, theta, 3 / t**3, dumb, 1 / t**3))
print("E2 exact fraction: 685/144 =", 685 / 144)
