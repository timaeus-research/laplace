"""Tide unique-minimum: l(x) = lam x^2/2 + alpha x^3/6 + gamma x^4/24 (lam, gamma > 0).
(A) l(x) > 0 for all x != 0  iff  alpha^2 < 3 lam gamma  (the quadratic factor lam/2 + alpha x/6 + gamma x^2/24 has no real root);
    at alpha^2 = 3 lam gamma the factor has the double root x0 = -2 alpha/gamma and l(x0) = 0 = l(0): the minimiser is not unique.
(B) l'(x) = x (lam + alpha x/2 + gamma x^2/6) has a nonzero root iff alpha^2 >= 8 lam gamma/3.
Note's parametrisation alpha^2 = a^2 lam^3, gamma = lam^2: thresholds a^2 < 3 (unique global minimum) and a^2 >= 8/3 (extra critical points)."""
import sympy as sp
x, lam, alpha, gamma = sp.symbols('x lam alpha gamma', real=True)
l = lam*x**2/2 + alpha*x**3/6 + gamma*x**4/24
q = sp.factor(l / x**2); print("l/x^2 =", q, " discriminant:", sp.discriminant(sp.expand(l/x**2), x), " <0 iff alpha^2 < 3 lam gamma")
dl = sp.diff(l, x); print("l'/x =", sp.factor(dl/x), " discriminant:", sp.discriminant(sp.expand(dl/x), x), " >=0 iff alpha^2 >= 8 lam gamma/3")
x0 = -2*alpha/gamma; print("at alpha^2 = 3 lam gamma: l(-2 alpha/gamma) =", sp.simplify(l.subs(x, x0).subs(lam, alpha**2/(3*gamma))))
# numeric: lam = 1, gamma = 1 (a^2 = alpha^2): a^2 = 2.8 has extra critical points but positive l; a^2 = 3.2 has negative values
for a2 in [2.5, 2.8, 3.0, 3.2]:
    al = sp.sqrt(a2); ln = l.subs({lam: 1, gamma: 1, alpha: al}); crit = [r for r in sp.Poly(sp.expand(dl.subs({lam:1,gamma:1,alpha:al})/x), x).nroots() if abs(sp.im(r)) < 1e-12]
    mn = min(float(ln.subs(x, r)) for r in [sp.Rational(1,1)*t/10 for t in range(-150, 151)])
    print("a^2=%.1f: nonzero critical points %s, min over grid %.4f, l(-2a)= %.4f" % (a2, [round(float(sp.re(r)),3) for r in crit], mn, float(ln.subs(x, -2*al))))
