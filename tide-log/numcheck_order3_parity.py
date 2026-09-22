"""Tide order3-parity: numerical check of the parity-aware fourth-order expansion.

lam = 2, a = 1/2 (alpha^2 = a^2 lam^3), gamma = lam^2.  Checks:
 (1) even n: t^2 * (J_n - [m_n - (B/t) m_{n+4} + (A^2/(2t)) m_{n+6}]) stays bounded;
 (2) odd n:  t^2 * (J_n - [-(A/sqrt t) m_{n+3} + (A B m_{n+7} - A^3 m_{n+9}/6)/(t sqrt t)]) stays bounded;
 (3) t * ( t (lam t Var - 1) - (a^2 - 1/2) ) converges (E7's t^-2 relative rate);
 (4) t^2 * ( t <l> - 1/2 - (5a^2/24 - 1/8)/t ) converges (energy at O(t^-2));
 (5) t * ( t^2 <x^3> + 5 alpha/(2 lam^3) ) converges.
"""
import numpy as np
from scipy.integrate import quad
from math import sqrt, pi, factorial

lam = 2.0; a = 0.5; alpha = a * lam**1.5; gamma = lam**2
A = alpha / (6 * lam * sqrt(lam)); B = gamma / (24 * lam**2)

def dfact(k):  # (k)!! for odd k>=-1
    return 1 if k <= 0 else k * dfact(k - 2)

def m(k):  # int u^k e^{-u^2/2}
    return 0.0 if k % 2 else sqrt(2 * pi) * dfact(k - 1)

def J(n, t):
    f = lambda u: u**n * np.exp(-u**2 / 2 - A * u**3 / sqrt(t) - B * u**4 / t)
    return quad(f, -40, 40, limit=400, epsabs=1e-13, epsrel=1e-13)[0]

def ell(x): return lam * x**2 / 2 + alpha * x**3 / 6 + gamma * x**4 / 24

def gibbs(t, obs):
    w = lambda x: np.exp(-t * ell(x))
    R = 12 / sqrt(lam * t)
    Z = quad(w, -R, R, limit=400, epsabs=1e-14, epsrel=1e-13)[0]
    return quad(lambda x: obs(x) * w(x), -R, R, limit=400, epsabs=1e-14, epsrel=1e-13)[0] / Z

ts = [25, 50, 100, 200, 400, 800]
print("(1) even n: t^2 * (J_n - 3-term)")
for n in (0, 2, 4):
    print(" n=%d:" % n, ["%.4f" % (t**2 * (J(n, t) - (m(n) - B / t * m(n + 4) + A**2 / (2 * t) * m(n + 6)))) for t in ts])
print("(2) odd n: t^2 * (J_n - 2-term)")
for n in (1, 3):
    print(" n=%d:" % n, ["%.4f" % (t**2 * (J(n, t) - (-A / sqrt(t) * m(n + 3) + (A * B * m(n + 7) - A**3 * m(n + 9) / 6) / (t * sqrt(t))))) for t in ts])
print("(3) t * (t(lam t Var - 1) - (a^2 - 1/2))")
for t in ts:
    M1 = gibbs(t, lambda x: x); M2 = gibbs(t, lambda x: x**2); V = M2 - M1**2
    print("  t=%4d  %.5f" % (t, t * (t * (lam * t * V - 1) - (a**2 - 0.5))))
print("(4) t^2 * (t<l> - 1/2 - (5a^2/24 - 1/8)/t)")
for t in ts:
    E = gibbs(t, ell)
    print("  t=%4d  %.5f" % (t, t**2 * (t * E - 0.5 - (5 * a**2 / 24 - 1 / 8) / t)))
print("(5) t * (t^2 <x^3> + 5 alpha/(2 lam^3))")
for t in ts:
    M3 = gibbs(t, lambda x: x**3)
    print("  t=%4d  %.5f" % (t, t * (t**2 * M3 + 5 * alpha / (2 * lam**3))))
