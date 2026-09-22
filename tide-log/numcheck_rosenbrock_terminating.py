"""Tide rosenbrock-terminating: for Rosenbrock d=2, L = (a (y-x^2)^2 + (1-x)^2)/2, minimiser (1,1),
H = [[1+4a, -2a], [-2a, a]], T_000 = 12a, T_001 = T_010 = T_100 = -2a, Q4_0000 = 12a, S = (tH)^{-1} = (1/t) [[1,2],[2,4+1/a]].
Exact moments (shear z = x-1 ~ N(0,1/t), u = y-x^2 ~ N(0,1/(at)) independent): <x> = 1, <y> = 1 + 1/t, <L> = 1/t.
Claims: (A) twoLoopEnergy = 1/2 tr(HS) + (t/12) theta + (t/8) dumbbell - q/8 = 1/t exactly (theta = 12a/t^3, dumbbell = 4a/t^3, q = 12a/t^2);
(B) meanShift = -(1/2) S (t T:S) = (0, 1/t) = (<x>-1, <y>-1) exactly;
(C) Cov[L, psi] - covKFormula = 3 B22/t^3 for psi = 1/2 v.Bv + b.v, v = (x-1, y-1); exact for linear probes."""
import sympy as sp
a, t = sp.symbols('a t', positive=True); z, u = sp.symbols('z u')
B11, B12, B21, B22, b1, b2 = sp.symbols('B11 B12 B21 B22 b1 b2')
def E(poly):
    poly = sp.Poly(sp.expand(poly), z, u); res = 0
    for (i, j), c in poly.terms():
        mz = sp.factorial2(i - 1) / t**sp.Rational(i, 2) if i % 2 == 0 else 0
        mu = sp.factorial2(j - 1) / (a * t)**sp.Rational(j, 2) if j % 2 == 0 else 0
        res += c * mz * mu
    return sp.simplify(res)
H = sp.Matrix([[1 + 4 * a, -2 * a], [-2 * a, a]]); S = (t * H).inv()
T = {(0,0,0): 12*a, (0,0,1): -2*a, (0,1,0): -2*a, (1,0,0): -2*a}; Q4 = {(0,0,0,0): 12*a}
def Tg(i,j,k): return T.get((i,j,k), 0)
theta = sp.simplify(sum(Tg(i,j,k)*Tg(l,m,n)*S[i,l]*S[j,m]*S[k,n] for i in range(2) for j in range(2) for k in range(2) for l in range(2) for m in range(2) for n in range(2)))
TS = sp.Matrix([sum(Tg(l,m,n)*S[m,n] for m in range(2) for n in range(2)) for l in range(2)])
dumb = sp.simplify((TS.T * S * TS)[0]); q = sp.simplify(sum(Q4.get((i,j,k,l),0)*S[i,j]*S[k,l] for i in range(2) for j in range(2) for k in range(2) for l in range(2)))
twoloop = sp.simplify(sp.Rational(1,2)*(H*S).trace() + t/12*theta + t/8*dumb - q/8)
print("A: theta =", theta, " dumbbell =", dumb, " q =", q, " twoLoopEnergy =", twoloop, " (exact <L> = 1/t)")
shift = sp.simplify(-sp.Rational(1,2) * S * (t * TS)); print("B: meanShift =", list(shift), " exact (<x>-1, <y>-1) = (0, 1/t)")
L = (a*u**2 + z**2)/2; vx = z; vy = u + 2*z + z**2
psi = sp.Rational(1,2)*(B11*vx**2 + (B12 + B21)*vx*vy + B22*vy**2) + b1*vx + b2*vy
cov_exact = sp.simplify(E(L*psi) - E(L)*E(psi))
Bm = sp.Matrix([[B11, B12], [B21, B22]]); bv = sp.Matrix([b1, b2]); SHS = S*H*S
def contractT(M): return sp.Matrix([sum(Tg(l,m,n)*M[m,n] for m in range(2) for n in range(2)) for l in range(2)])
formula = sp.Rational(1,2)*(H*S*Bm*S).trace() + sp.Rational(1,2)*((S*bv).T*TS)[0] - t/2*(bv.T*SHS*TS)[0] - t/2*((S*bv).T*contractT(SHS))[0]
print("C: covKFormula =", sp.factor(sp.simplify(formula)))
print("   exact Cov[L,psi] - covKFormula =", sp.factor(sp.simplify(cov_exact - formula)))
# coefficient table of L*psi and psi in z^i u^j (for the Lean coefficient matrices)
for name, poly in [("psi", psi), ("L*psi", L*psi)]:
    P = sp.Poly(sp.expand(poly), z, u); print("  %s: max z-degree %d, max u-degree %d" % (name, P.degree(z), P.degree(u)))
