"""Localised anharmonic mean to second order: t<x>_loc = c + c'/t + O(1/t^2), c = -alpha/(2 lam^2) + g x0/lam.
GPT (tide 67) predicted c' = B1 + a alpha^2/lam^4 - a gamma/(2 lam^3) + alpha g/lam^3 - alpha a^2/(2 lam^3) - a g/lam^2, a = g x0.
Compute via Wick expansion with the localiser as part of the perturbation: e^{-t l - (g/2)(x-x0)^2}."""
import sympy as sp
al, ga, lam, g, x0, eps = sp.symbols('alpha gamma lambda g x0 epsilon', positive=True)
u = sp.symbols('u', real=True)
# x = u/sqrt(lam t) = u eps/sqrt(lam);  t l = u^2/2 + A u^3 eps + B u^4 eps^2;  localiser (g/2)(x - x0)^2 = (g/2)(u eps/sqrt(lam) - x0)^2
A = al/(6*lam**sp.Rational(3,2)); B = ga/(24*lam**2)
loc = sp.expand(sp.Rational(1,2)*g*(u*eps/sp.sqrt(lam) - x0)**2)   # constant g x0^2/2 cancels in normalisation
pert = sp.series(sp.exp(-A*u**3*eps - B*u**4*eps**2 - (loc - g*x0**2/2)), eps, 0, 6).removeO()
def gm(expr):
    poly = sp.Poly(sp.expand(expr), u); return sum(c*(0 if m[0] % 2 else sp.factorial2(m[0]-1)) for m, c in zip(poly.monoms(), poly.coeffs()))
raw1 = sp.series(gm(u*pert)/gm(pert), eps, 0, 6).removeO()
t = 1/eps**2
tm = sp.expand(sp.series(t * raw1 * eps/sp.sqrt(lam), eps, 0, 4).removeO())   # t <x>_loc = t * (u eps/sqrt(lam) averaged)
c0 = tm.coeff(eps, 0); c1 = tm.coeff(eps, 2)
print("c  =", sp.simplify(c0))
print("c' =", sp.simplify(c1))
a = g*x0; B1 = -5*al**3/(8*lam**5) + 2*al*ga/(3*lam**4)
cpred = B1 + a*al**2/lam**4 - a*ga/(2*lam**3) + al*g/lam**3 - al*a**2/(2*lam**3) - a*g/lam**2
print("GPT c' =", sp.simplify(cpred), "  diff =", sp.simplify(c1 - cpred))
print("numeric c' at lam=1.3, al=0.7, ga=1.1, g=0.8, x0=0.6:", float(c1.subs({lam:1.3, al:0.7, ga:1.1, g:0.8, x0:0.6})))
