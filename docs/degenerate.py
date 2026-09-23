"""Degenerate Newton edge: F = x^2 (x^2 - s)^2 + x^10, rescaled to u = x t^{1/6}:
t F = u^2 (u^2 - sigma)^2 + t^{-2/3} u^10 with sigma = s t^{1/3}.
Newton polygon lower edge (6,0)-(2,2) through (4,1): weights (1/6,1/3); edge form E = u^2 (u^2 - sigma)^2 has zeros ON
the divisor at u = ±sqrt(sigma) (Kouchnirenko-degenerate). Prediction: layer 1 at sigma ~ 1 (1/6 -> 1/2, three Morse
wells, side-well mass 1/2); a SECOND layer, not a Newton edge, at s ~ t^{-1/5} where the side wells (F = s^5 there) are
switched off by t s^5: bump in tE[F] above 1/2, side-well mass 1/2 -> 0."""
import numpy as np
from scipy.integrate import quad
def stats(t, sigma):
    eps = t**(-2/3)
    V = lambda u: u**2*(u**2 - sigma)**2 + eps*u**10
    w = lambda u: np.exp(-V(u))
    r = np.sqrt(sigma); wid = 1/max(sigma,1.0)
    L = max(3.0, r + 8*wid)
    pts = [0.0, r, -r]
    kw = dict(points=pts, limit=2000)
    Z = quad(w, -L, L, **kw)[0]
    E = quad(lambda u: V(u)*w(u), -L, L, **kw)[0]/Z
    side = 2*quad(w, r/2, L, points=[r], limit=2000)[0]/Z
    return E, side
for t in [1e12, 1e24, 1e36]:
    print(f"t={t:.0e}: layer1 sigma = s t^(1/3) ~ 1; layer2 at s t^(1/5) ~ 1 i.e. sigma ~ t^(2/15) = {t**(2/15):.1f}")
    print("   s*t^(1/3)   s*t^(1/5)   tE[F]   side-well mass   t s^5")
    for ls in list(np.linspace(-1, 1.2, 12)) + list(np.log10(t**(2/15)) + np.linspace(-1, 0.6, 9)):
        sigma = 10**ls
        E, side = stats(t, sigma)
        s = sigma*t**(-1/3)
        print(f"   {sigma:9.3f}   {s*t**(1/5):9.4f}   {E:.4f}   {side:.3f}   {t*s**5:.3g}")
    print()
