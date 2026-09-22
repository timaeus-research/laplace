"""Tide 73: the localised anharmonic energy to second order. sympy expansion + quadrature."""
import sympy as sp, numpy as np
from scipy.integrate import quad
lam, al, ga, g, x0, eps, u = sp.symbols('lambda alpha gamma g x0 epsilon u', positive=True)
a = g*x0; b = g/2
# x = eps u, eps = 1/sqrt t: -t l = -lam u^2/2 - eps al u^3/6 - eps^2 ga u^4/24 ; localiser exponent eps a u - eps^2 b u^2
pert = sp.series(sp.exp(eps*(-al*u**3/6 + a*u) + eps**2*(-ga*u**4/24 - b*u**2)), eps, 0, 5).removeO()
def gmom(n):  # <u^n> under N(0, 1/lam)
    return 0 if n % 2 else sp.factorial2(n-1)/lam**(n//2)
def gexp(expr):
    poly = sp.Poly(sp.expand(expr), u)
    return sum(c*gmom(m[0]) for m, c in zip(poly.monoms(), poly.coeffs()))
tl = lam*u**2/2 + eps*al*u**3/6 + eps**2*ga*u**4/24   # t*l(eps u)
num = gexp(sp.expand(tl*pert)); den = gexp(pert)
ratio = sp.series(num/den, eps, 0, 3).removeO()
c0 = sp.simplify(ratio.coeff(eps, 0)); c1 = sp.simplify(ratio.coeff(eps, 1)); e1 = sp.simplify(ratio.coeff(eps, 2))
e1_pred = (a**2 - g)/(2*lam) - a*al/(2*lam**2) - ga/(8*lam**2) + 5*al**2/(24*lam**3)
print("c0 =", c0, " c1 =", c1); print("e1 =", sp.factor(e1)); print("e1 - predicted =", sp.simplify(e1 - e1_pred))
# also via the moment route: n2 = B2 + a c3 + 3 p3/lam^2, d1 = -a al/(2 lam^2) + p3/lam
B2 = 5*al**2/(4*lam**4) - ga/(2*lam**3); c3 = -5*al/(2*lam**3); p3 = (a**2-g)/2; d1 = -a*al/(2*lam**2) + p3/lam
n2 = B2 + a*c3 + 3*p3/lam**2; e1_moment = lam/2*(n2 - d1/lam) + al/6*(c3 + 3*a/lam**2) + ga/24*(3/lam**2)
print("e1 - moment-route =", sp.simplify(e1 - e1_moment))
P = dict(lam=1.3, al=0.7, ga=1.1, g=0.8, x0=0.6); e1n = float(e1_pred.subs({lam:P['lam'], al:P['al'], ga:P['ga'], g:P['g'], x0:P['x0']}))
e0n = float((-ga/(8*lam**2) + 5*al**2/(24*lam**3)).subs({lam:P['lam'], al:P['al'], ga:P['ga']}))
print(f"e1 = {e1n:.6f}, unlocalised e0 = {e0n:.6f}, e1 - e0 = {e1n-e0n:.6f} (pred (a^2-g)/(2lam) - a al/(2 lam^2) = {((0.48**2-0.8)/2.6 - 0.48*0.7/(2*1.69)):.6f}), e1 + g/(2lam) = {e1n + 0.8/2.6:.6f}")
L = lambda x: P['lam']/2*x**2 + P['al']/6*x**3 + P['ga']/24*x**4
for t in [10, 40, 160, 640, 2560]:
    w = lambda x: np.exp(-t*L(x) + P['g']*P['x0']*x - P['g']/2*x**2)
    Z = quad(w, -3, 3, points=[0], limit=400)[0]; E = quad(lambda x: L(x)*w(x), -3, 3, points=[0], limit=400)[0]/Z
    trace = 0.5*t*P['lam']/(t*P['lam'] + P['g'])
    print(f"t={t:5d}: t<l>_loc={t*E:.6f}  t(t<l>_loc - 1/2)={t*(t*E-0.5):.5f} (e1 {e1n:.5f})  t(t<l>_loc - trace)={t*(t*E-trace):.5f} (pred {e1n+0.8/2.6:.5f})")
