"""Residual of F on the exceptional divisor of a weighted blow-up versus the Newton edge form.

Chart of the weighted blow-up of the (x, s)-plane with weights (p, q): x = u v^p, s = v^q.
F∘g = v^N Φ(u, v); the residual is Φ(u, 0).  Compare with the edge form E(u, 1)."""
import sympy as sp
u, v, x, s = sp.symbols('u v x s')

def residual(F, p, q):
    G = sp.expand(F.subs({x: u*v**p, s: v**q}))
    N = min(sp.Poly(G, v).monoms())[0]
    return sp.factor(sp.expand(G / v**N).subs(v, 0)), N

cases = {
 'A degenerating unit (s + x^2) x^2':  ((s + x**2)*x**2,        [(1, 2), (1, 1)]),
 'B degenerating unit (s + x^4) x^2':  ((s + x**4)*x**2,        [(1, 4), (1, 1)]),
 'D merging zeros x^2 (x - s)^2':      (x**2*(x - s)**2,        [(1, 1), (1, 2)]),
 'E pitchfork (x^2 - s)^2':            ((x**2 - s)**2,          [(1, 2), (1, 1)]),
 'two-layer x^6 + x^4 s^2 + x^2 s^6':  (x**6 + x**4*s**2 + x**2*s**6, [(1, 1), (2, 1), (1, 2), (3, 1)]),
}
for name, (F, weights) in cases.items():
    print(name)
    for p, q in weights:
        R, N = residual(F, p, q)
        mono = len(sp.Poly(R, u).terms()) == 1
        print(f"   weights (x,s)=({p},{q}), order N={N}, divisorial ratios (alpha,gamma)=({p}/{N},{q}/{N}):"
              f"  residual = {R}   {'monomial (no layer)' if mono else 'EDGE FORM (layer)'}")
