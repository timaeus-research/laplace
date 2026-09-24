"""Numerical check of the three-coordinate degenerate-face example (Astra, round 6).

I(t) = int_{(0,1)^3} 1_{xyz > t^-2} z^2 exp(-t^3 x y z^2) dx dy dz, predicted t^4 I(t)/log t -> 1.
Collapse xy = s with density -log s, then integrate in log coordinates.
"""
import numpy as np
from scipy import integrate


def inner(z, t):
    # integral over s in (t^-2 / z, 1) of (-log s) exp(-t^3 s z^2) ds, in u = log s
    lo = -2 * np.log(t) - np.log(z)
    if lo >= 0:
        return 0.0
    f = lambda u: (-u) * np.exp(u) * np.exp(-(t**3) * np.exp(u) * z**2)
    val, _ = integrate.quad(f, lo, 0.0, limit=400)
    return val


def I(t):
    g = lambda w: np.exp(w) ** 3 * inner(np.exp(w), t)  # z = e^w, dz = e^w dw, z^2 factor
    val, _ = integrate.quad(g, -2 * np.log(t) - 1, 0.0, limit=400, points=[-np.log(t)])
    return val


for t in [1e2, 1e3, 1e4, 1e5]:
    val = I(t)
    print(f"t={t:.0e}  t^4 I/log t = {t**4 * val / np.log(t):.4f}")
