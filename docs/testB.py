"""Astra Test A: F = x^2((x-s)^2 + s^4): hump H -> 1/2 + z/(1+e^z), z = t s^6 on s = sigma t^{-1/6}.
Astra Test B: F = x^2((x-s)^4 + s^6): 1/6 -> 1/4 (sigma = s t^{1/6}), plateau 1/4 for t^{-1/6} << s << t^{-1/8},
then H ~ 1/4 + z (z = t s^8) with Q = Z_s/Z_0 ~ C t^{1/16} z^{3/16} e^{-z}, exchange at z* = (1/16) log t + (3/16) log log t + O(1),
energy of order log t during the exchange, then 1/2.  Per-well integration in local coordinates."""
import numpy as np
from scipy.integrate import quad
from math import gamma, sqrt, pi, log
def H(t, s, F, wells):
    Z = 0.0; N = 0.0
    for (c, w) in wells:            # centre, width
        f = lambda y: np.exp(-t*F(c + y, s))
        g = lambda y: t*F(c + y, s)*np.exp(-t*F(c + y, s))
        L = 12*w
        Z += quad(f, -L, L, points=[0.0], limit=2000)[0]; N += quad(g, -L, L, points=[0.0], limit=2000)[0]
    return N/Z
print("Test A: F = x^2((x-s)^2+s^4), z = t s^6")
FA = lambda x, s: x**2*((x-s)**2 + s**4)
for t in [1e12, 1e24]:
    row=[]
    for z in [0.1, 0.5, 1.0, 2.0, 4.0]:
        s = (z/t)**(1/6); w0 = 1/(sqrt(2*t)*s)
        h = H(t, s, FA, [(0.0, w0), (s, w0)])
        row.append(f"z={z}: {h:.4f} (pred {0.5 + z/(1+np.exp(z)):.4f})")
    print(f"  t={t:.0e}: " + "; ".join(row))
print("\nTest B: F = x^2((x-s)^4+s^6), z = t s^8")
FB = lambda x, s: x**2*((x-s)**4 + s**6)
C = gamma(0.25)/(2*sqrt(pi))
for t in [1e12, 1e24, 1e48]:
    zs = log(t)/16 + 3*log(log(t))/16
    print(f"  t={t:.0e}: predicted exchange z* ~ {zs:.2f}  (log t /16 = {log(t)/16:.2f})")
    for z in [0.5, 1.0, 2.0] + [zs-2, zs-1, zs-0.5, zs, zs+0.5, zs+1, zs+2, zs+4]:
        s = (z/t)**(1/8); w0 = 1/(sqrt(2*t)*s**2); ws = (t*s**2)**(-0.25)
        h = H(t, s, FB, [(0.0, w0), (s, ws)])
        Q = C*t**(1/16)*z**(3/16)*np.exp(-z)
        pred = (0.5 + (z + 0.25)*Q)/(1 + Q)
        print(f"     z={z:6.2f}  s t^(1/8)={s*t**(1/8):.3f}   H={h:8.4f}   pred={pred:8.4f}   Q={Q:.3g}")
