import numpy as np
from scipy.optimize import brentq
def a_fac(h, p, N, b):
    r = 1 - h * p
    return np.mean([r ** (2 * (b + 1 + k)) for k in range(N)])
def s2(h, p): return 1 / (p * (1 - h * p / 2))
for (p, N, b) in [(1.0, 20, 5), (3.0, 50, 0), (0.5, 7, 3)]:
    hs = np.linspace(1e-6, 1 / p, 400)
    bias_ula = np.array([s2(h, p) * a_fac(h, p, N, b) for h in hs])
    rel = np.array([a_fac(h, p, N, b) for h in hs])
    print(f"p={p} N={N} b={b}: s2*a antitone in h:", np.all(np.diff(bias_ula) <= 1e-12), " a antitone:", np.all(np.diff(rel) <= 1e-12))
    f = lambda h: h / (2 - h * p) - s2(h, p) * a_fac(h, p, N, b)
    print("   f(0+)=%.4f (expect -1/p=%.4f)  f(1/p)=%.4f (expect 1/p)" % (f(1e-9), -1 / p, f(1 / p)))
    hstar = brentq(f, 1e-9, 1 / p)
    print("   interior zero h* = %.5f (h*p = %.4f); bias vs P^{-1} there: %.2e" % (hstar, hstar * p, f(hstar) ** 2))
# per-term monotonicity identity used in the proof: (1-u')^{2m}(1-u/2) <= (1-u)^{2m}(1-u'/2) for 0<=u<=u'<=1, m>=1
ok = True
for m in range(1, 8):
    for u in np.linspace(0, 1, 21):
        for up in np.linspace(u, 1, 11):
            ok &= (1 - up) ** (2 * m) * (1 - u / 2) <= (1 - u) ** (2 * m) * (1 - up / 2) + 1e-15
print("per-term inequality:", ok)
# E1 numerics
for hp in [1.0, 1.5, 1.9]:
    print("hp=%.1f inflation 1/(1-hp/2)=%.3f  LLC(d=10,kappa=1)=%.1f" % (hp, 1 / (1 - hp / 2), 5 / (1 - hp / 2)))
