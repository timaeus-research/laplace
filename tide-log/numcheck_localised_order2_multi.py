"""Tide 74: localised variance to second order + eq:mean/eq:cov O(S^2) coefficients. sympy + quadrature."""
import sympy as sp, numpy as np
from scipy.integrate import quad
lam, al, ga, g, x0, eps, u = sp.symbols('lambda alpha gamma g x0 epsilon u', positive=True)
a = g*x0; b = g/2
pert = sp.series(sp.exp(eps*(-al*u**3/6 + a*u) + eps**2*(-ga*u**4/24 - b*u**2)), eps, 0, 5).removeO()
def gmom(n): return 0 if n % 2 else sp.factorial2(n-1)/lam**(n//2)
def gexp(expr):
    poly = sp.Poly(sp.expand(expr), u); return sum(c*gmom(m[0]) for m, c in zip(poly.monoms(), poly.coeffs()))
den = gexp(pert)
m1 = sp.series(gexp(sp.expand(u*pert))/den, eps, 0, 4).removeO()      # <u>_loc = sqrt t <x>_loc
m2 = sp.series(gexp(sp.expand(u**2*pert))/den, eps, 0, 4).removeO()   # <u^2>_loc = t <x^2>_loc
var = sp.expand(m2 - m1**2)                                            # t Var_loc
v0 = sp.simplify(var.coeff(eps, 0)); v1 = sp.simplify(var.coeff(eps, 1)); vp = sp.simplify(var.coeff(eps, 2))
# predicted: v' = c2' - c^2
B2 = 5*al**2/(4*lam**4) - ga/(2*lam**3); c3 = -5*al/(2*lam**3); p3 = (a**2-g)/2
d1 = -a*al/(2*lam**2) + p3/lam; n2 = B2 + a*c3 + 3*p3/lam**2; c2p = n2 - d1/lam
c = -al/(2*lam**2) + a/lam
vp_pred = c2p - c**2
print("t Var_loc: v0 =", v0, " v1 =", v1); print("v' =", sp.factor(vp)); print("v' - (c2' - c^2) =", sp.simplify(vp - vp_pred))
print("v' + g/lam^2 (coefficient of eq:cov's O(S^2) term) =", sp.factor(sp.simplify(vp + g/lam**2)))
# mean: c' and c'_S
B1 = -5*al**3/(8*lam**5) + 2*al*ga/(3*lam**4)
cp = B1 + a*al**2/lam**4 - a*ga/(2*lam**3) + al*g/lam**3 - al*a**2/(2*lam**3) - a*g/lam**2
cpS = al*g/lam**3 - a*g/lam**2
t = sp.symbols('t', positive=True)
locLeading = -al*t/(2*(t*lam+g)**2) + a/(t*lam+g)
print("locLeading t^-2 coeff - c'_S =", sp.simplify(sp.series(locLeading, t, sp.oo, 4).removeO().coeff(t, -2) - cpS))
r = sp.simplify(cp - cpS); print("r = c' - c'_S =", sp.factor(r))
P = {lam:1.3, al:0.7, ga:1.1, g:0.8, x0:0.6}
vpn = float(vp_pred.subs(P)); vSn = float((vp_pred + g/lam**2).subs(P)); rn = float(r.subs(P))
print(f"v' = {vpn:.6f}, v' + g/lam^2 = {vSn:.6f}, r = {rn:.6f}")
Pn = dict(lam=1.3, al=0.7, ga=1.1, g=0.8, x0=0.6)
L = lambda x: Pn['lam']/2*x**2 + Pn['al']/6*x**3 + Pn['ga']/24*x**4
for tt in [10, 40, 160, 640, 2560]:
    w = lambda x: np.exp(-tt*L(x) + Pn['g']*Pn['x0']*x - Pn['g']/2*x**2)
    Z = quad(w, -3, 3, points=[0], limit=400)[0]
    M1 = quad(lambda x: x*w(x), -3, 3, points=[0], limit=400)[0]/Z; M2 = quad(lambda x: x*x*w(x), -3, 3, points=[0], limit=400)[0]/Z
    V = M2 - M1**2; S = 1/(tt*Pn['lam'] + Pn['g']); PL = -Pn['al']*tt/(2*(tt*Pn['lam']+Pn['g'])**2) + Pn['g']*Pn['x0']/(tt*Pn['lam']+Pn['g'])
    print(f"t={tt:5d}: t(tVar-1/lam)={tt*(tt*V-1/Pn['lam']):.5f} (v' {vpn:.5f})  t^2(Var-S)={tt**2*(V-S):.5f} (pred {vSn:.5f})  t^2(<x>_loc-P_t)={tt**2*(M1-PL):.5f} (r {rn:.5f})")
