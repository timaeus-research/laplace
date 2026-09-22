"""Perturbative (Wick) expansion of the anharmonic Gibbs moments in eps = 1/sqrt(t):
x = u/sqrt(lam t); e^{-t l} = e^{-u^2/2} exp(-A u^3 eps - B u^4 eps^2), A = alpha/(6 lam^{3/2}), B = gamma/(24 lam^2).
Gives <x^k> as a series; then t^2 Cov[l, x^2] and t^2 Cov[l, x] to O(1/t)."""
import sympy as sp
al, ga, lam, eps = sp.symbols('alpha gamma lambda epsilon', positive=True)
u = sp.symbols('u', real=True)
A = al/(6*lam**sp.Rational(3,2)); B = ga/(24*lam**2)
N = 6  # order in eps
pert = sp.series(sp.exp(-A*u**3*eps - B*u**4*eps**2), eps, 0, N+1).removeO()
def gauss_moment(n):  # E[u^n] under standard normal
    return 0 if n % 2 else sp.factorial2(n-1)
def raw(k):  # <x^k> * (lam t)^{k/2} / Z-normalisation: E_gauss[u^k pert]/E_gauss[pert]
    num = sp.expand(u**k * pert); den = sp.expand(pert)
    def gm(expr):
        poly = sp.Poly(expr, u); return sum(c*gauss_moment(m[0]) for m, c in zip(poly.monoms(), poly.coeffs()))
    return sp.series(gm(num)/gm(den), eps, 0, N+1).removeO()
t = 1/eps**2
def mom(k):  # <x^k> as series in eps: (lam t)^{-k/2} * raw(k)
    return sp.expand(sp.series(raw(k) * (lam*t)**(-sp.Rational(k,2)), eps, 0, N+1).removeO())
m = {k: mom(k) for k in range(1,7)}
print("t<x>   =", sp.simplify(sp.series(t*m[1], eps, 0, 3).removeO()))
print("t<x^2> =", sp.simplify(sp.series(t*m[2], eps, 0, 3).removeO()))
# covariances with l = lam/2 x^2 + al/6 x^3 + ga/24 x^4
def E(expr_coeffs):  # dict power->coeff
    return sum(c*m[k] for k, c in expr_coeffs.items())
l = {2: lam/2, 3: al/6, 4: ga/24}
def cov_l(k):  # Cov[l, x^k] = <l x^k> - <l><x^k>
    lx = {p+k: c for p, c in l.items()}
    return sp.expand(E(lx) - E(l)*m[k])
mm = {k: mom(k) for k in range(1,9)}; m.update(mm)
c2 = sp.simplify(sp.series(t**2*cov_l(2), eps, 0, 3).removeO()); c1 = sp.simplify(sp.series(t**2*cov_l(1), eps, 0, 3).removeO())
print("t^2 Cov[l,x^2] =", sp.collect(sp.expand(c2), eps))
print("t^2 Cov[l,x]   =", sp.collect(sp.expand(c1), eps))
# numeric check
vals = {al: 0.7, ga: 1.1, lam: 1.3}
import numpy as np
from scipy.integrate import quad
lamv, alv, gav = 1.3, 0.7, 1.1
def ell(x): return lamv*x**2/2 + alv*x**3/6 + gav*x**4/24
def E_num(tt, f):
    w = lambda x: np.exp(-tt*ell(x)); R = 12/np.sqrt(lamv*tt) + 2
    Z = quad(w, -R, R, epsabs=1e-16, epsrel=1e-15, limit=800)[0]
    return quad(lambda x: f(x)*w(x), -R, R, epsabs=1e-16, epsrel=1e-15, limit=800)[0]/Z
for tt in [40.0, 160.0, 640.0]:
    c2n = tt**2*(E_num(tt, lambda x: ell(x)*x**2) - E_num(tt, ell)*E_num(tt, lambda x: x**2))
    c1n = tt**2*(E_num(tt, lambda x: ell(x)*x) - E_num(tt, ell)*E_num(tt, lambda x: x))
    print(f"t={tt:g}: t^2Cov[l,x^2]={c2n:.6f} pred={float(c2.subs(vals).subs(eps, 1/np.sqrt(tt))):.6f}   t^2Cov[l,x]={c1n:.6f} pred={float(c1.subs(vals).subs(eps, 1/np.sqrt(tt))):.6f}")
print("t^2<x^3> =", sp.collect(sp.expand(sp.series(t**2*m[3], eps, 0, 3).removeO()), eps))
print("t^2<x^4> =", sp.collect(sp.expand(sp.series(t**2*m[4], eps, 0, 3).removeO()), eps))
print("t^3<x^5> =", sp.collect(sp.expand(sp.series(t**3*m[5], eps, 0, 3).removeO()), eps))
print("t^3<x^6> =", sp.collect(sp.expand(sp.series(t**3*m[6], eps, 0, 3).removeO()), eps))
# check the IBP-derived B3: (2 B1 - (alpha/2) C2' - (gamma/6) c5)/lambda with C2' = 25 alpha^2/(2 lam^5) - 4 gamma/lam^4, c5 = -35 alpha/(2 lam^4)
B1 = -5*al**3/(8*lam**5) + 2*al*ga/(3*lam**4); C2p = 25*al**2/(2*lam**5) - 4*ga/lam**4; c5 = -35*al/(2*lam**4)
print("B3 via IBP k=2 =", sp.simplify((2*B1 - al/2*C2p - ga/6*c5)/lam))
