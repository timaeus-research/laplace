"""Tide 78: second-order localised eq:covK via the Stein-covariance reduction. sympy: does the reduction reproduce 2c', 2c2'?"""
import sympy as sp
lam, al, ga, g, x0, eps, u = sp.symbols('lambda alpha gamma g x0 epsilon u', positive=True)
a = g*x0; b = g/2
pert = sp.series(sp.exp(eps*(-al*u**3/6 + a*u) + eps**2*(-ga*u**4/24 - b*u**2)), eps, 0, 6).removeO()
def gmom(n): return 0 if n % 2 else sp.factorial2(n-1)/lam**(n//2)
def gexp(expr):
    poly = sp.Poly(sp.expand(expr), u); return sum(c*gmom(m[0]) for m, c in zip(poly.monoms(), poly.coeffs()))
den = gexp(pert)
# localised moments m_j = <x^j>_loc = eps^j <u^j>_loc ; expansions in eps
m = {j: sp.series(gexp(sp.expand(u**j*pert))/den, eps, 0, 7).removeO() * eps**j for j in range(0, 7)}
t = 1/eps**2
def coeff_t(expr, k):   # coefficient of t^-k in a Laurent series in eps (t = eps^-2)
    return sp.simplify(sp.expand(expr).coeff(eps, 2*k))
C = lambda r, n: sp.expand(m[r+n] - m[r]*m[n])
for n in (1, 2):
    red = sp.expand(sp.Rational(n, 2)*t*m[n] - al/12*t**2*C(3, n) - ga/24*t**2*C(4, n) - g/2*t*C(2, n) + a/2*t*C(1, n))
    lead, first = coeff_t(red, 0), coeff_t(red, 1)
    print(f"n={n}: t^2 Cov_loc[l, x^{n}] = ({sp.factor(lead)}) + ({sp.factor(first)})/t + ...")
# tide 72/73 coefficients
B1 = -5*al**3/(8*lam**5) + 2*al*ga/(3*lam**4); B2 = 5*al**2/(4*lam**4) - ga/(2*lam**3)
c = -al/(2*lam**2) + a/lam
cp = B1 + a*al**2/lam**4 - a*ga/(2*lam**3) + al*g/lam**3 - al*a**2/(2*lam**3) - a*g/lam**2
c3 = -5*al/(2*lam**3); p3 = (a**2-g)/2; d1 = -a*al/(2*lam**2) + p3/lam; n2 = B2 + a*c3 + 3*p3/lam**2; c2p = n2 - d1/lam
red1 = sp.expand(sp.Rational(1,2)*t*m[1] - al/12*t**2*C(3,1) - ga/24*t**2*C(4,1) - g/2*t*C(2,1) + a/2*t*C(1,1))
red2 = sp.expand(t*m[2] - al/12*t**2*C(3,2) - ga/24*t**2*C(4,2) - g/2*t*C(2,2) + a/2*t*C(1,2))
print("n=1: lead - c =", sp.simplify(coeff_t(red1,0) - c), " first - 2c' =", sp.simplify(coeff_t(red1,1) - 2*cp))
print("n=2: lead - 1/lam =", sp.simplify(coeff_t(red2,0) - 1/lam), " first - 2c2' =", sp.simplify(coeff_t(red2,1) - 2*c2p))
# the new input: t^2 m4 to second order, and t^3 m5, t^3 m6 leading
print("t^2 m4 =", sp.factor(coeff_t(sp.expand(t**2*m[4]),0)), "+ (", sp.factor(coeff_t(sp.expand(t**2*m[4]),1)), ")/t")
print("t^3 m5 ->", sp.factor(coeff_t(sp.expand(t**3*m[5]),0)), "; t^3 m6 ->", sp.factor(coeff_t(sp.expand(t**3*m[6]),0)))
