"""Exponent LP for several truth variables (Astra item E):
F = x^2 s1^2 + x^4 s2 + x^6 (d=1 loss variable, m=2 truths), density dx (h=0).
Along s_j = sigma_j t^{-gamma_j}: lambda(gamma) = min { a : a >= 0, A a + B gamma >= 1 } with rows
(2,2,0),(4,0,1),(6,0,0): 2a + 2g1 >= 1, 4a + g2 >= 1, 6a >= 1.  Compare with -log Z / log t."""
import numpy as np
from scipy.optimize import linprog
from scipy.integrate import quad
def lam_lp(g1, g2):
    # minimise a subject to a >= (1-2g1)/2, a >= (1-g2)/4, a >= 1/6, a >= 0
    return max((1-2*g1)/2, (1-g2)/4, 1/6, 0.0)
def logZ(t, g1, g2, sig=(1.0, 1.0)):
    s1 = sig[0]*t**(-g1); s2 = sig[1]*t**(-g2)
    F = lambda x: x**2*s1**2 + x**4*s2 + x**6
    scales = [t**(-1/6)] + ([(t*s1**2)**(-0.5)] if s1 > 0 else []) + ([(t*s2)**(-0.25)] if s2 > 0 else [])
    L = 12*min(scales)
    Z = quad(lambda x: np.exp(-t*F(x)), -L, L, points=[0.0], limit=2000)[0]
    return -np.log(Z)/np.log(t)
print("gamma=(g1,g2)   LP lambda   -logZ/log t at t=1e12, 1e24 (expect slow 1/log t drift from constants)")
for g in [(0.0,0.0),(0.1,0.0),(0.3,0.0),(0.5,0.0),(0.0,0.3),(0.0,0.5),(0.0,1.0),(0.2,0.5),(0.4,0.8),(0.45,0.9)]:
    print(f"  {g}: {lam_lp(*g):.4f}   {logZ(1e12,*g):.4f}  {logZ(1e24,*g):.4f}")
print("\nregions of linearity (chambers of rate space): a=(1-2g1)/2 when g1<=1/3 and 2g1>= g2/2 ... vertices:")
print("  wall type 1/2 (x^2 s1^2 dominates) for g1 small; 1/4 (x^4 s2) for intermediate; 1/6 (x^6) when g1>=1/3 and g2>=1/3")
