**A, B, and C are correct**, assuming \(a>0\), \(t>0\), the full-space Gibbs measure proportional to \(e^{-tL}\), and \(B,b\) independent of \(t\). Here \(B_{11}\) in zero-based Lean indexing is \(B_{22}\) in the note’s one-based indexing. Symmetry of \(B\) is not necessary: the quadratic probe only sees its symmetric part.

## 1. Contractions, signs, and termination

Write
\[
S=(tH)^{-1}=\frac1t
\begin{pmatrix}1&2\\2&4+1/a\end{pmatrix},
\qquad d=T:S.
\]
Direct contraction gives
\[
d=\frac1t\binom{12a-2a(2+2)}{-2a}
=\frac1t\binom{4a}{-2a},
\qquad
Sd=\binom{0}{-2/t^2}.
\]

### A. Two-loop energy

For a transparent check of the tensor contractions, use the **linear tangent coordinates**
\[
v=(x-1,y-1)=(r,2r+s).
\]
In these coordinates,
\[
L=\frac12r^2+\frac a2(s-r^2)^2.
\]
Thus the Hessian is \(\operatorname{diag}(1,a)\), the Gaussian covariance is
\(\operatorname{diag}(1,1/a)/t\), and the only nonzero cubic components are the three permutations
\[
T'_{001}=-2a.
\]
The quartic tensor has \(Q'_{0000}=12a\). Consequently,
\[
\theta
=3(-2a)^2\frac1{t^2}\frac1{at}
=\frac{12a}{t^3},
\]
\[
\delta=d^\top Sd=\frac{4a}{t^3},
\qquad
q=12a\left(\frac1t\right)^2=\frac{12a}{t^2}.
\]

For comparison with the existing original-coordinate machinery, the bubble matrix is
\[
(TSST)=\frac1{t^2}
\begin{pmatrix}
8a+16a^2&-8a^2\\
-8a^2&4a^2
\end{pmatrix},
\]
and
\[
Q:S=\begin{pmatrix}12a/t&0\\0&0\end{pmatrix}.
\]
Contracting these with \(S\) gives the same \(\theta\) and \(q\).

Since \(HS=I/t\),
\[
\operatorname{twoLoopEnergy}
=\frac1t+\frac{a}{t^2}+\frac{a}{2t^2}-\frac{3a}{2t^2}
=\frac1t.
\]
The triangular shear gives \(\langle L\rangle=1/t\), so both proposed A statements hold. In particular, **\(\theta=3\delta\)**, as claimed.

### B. Mean shift

Using the contraction above,
\[
\operatorname{meanShift}=-\frac t2Sd
=\binom{0}{1/t}.
\]
This agrees exactly with
\[
(\langle x\rangle-1,\langle y\rangle-1)=(0,1/t).
\]

### C. Sign convention in `covKFormula`

Your simplification is correct. Because
\[
SHS=S/t,\qquad T:(SHS)=d/t,
\]
each of the last two terms becomes \(-\tfrac12(Sb)\cdot d\). Together with the preceding positive half-term, this leaves
\[
\operatorname{covKFormula}
=\frac12\operatorname{tr}(HSBS)-\frac12(Sb)\cdot d.
\]
Now
\[
\frac12\operatorname{tr}(HSBS)
=\frac{B_{00}+2(B_{01}+B_{10})+(4+1/a)B_{11}}{2t^2},
\]
and
\[
-\frac12(Sb)\cdot d
=-\frac12 b\cdot Sd=\frac{b_1}{t^2}.
\]
This is exactly the proposed rational expression.

### What “terminates” should mean

It is correct to say that **the net inverse-temperature expansions of these observables terminate**:

- \(\langle L\rangle\) has only its \(t^{-1}\) term;
- \(\langle w\rangle-w_*\) has only its \(t^{-1}\) term.

For A, the nominal \(t^{-2}\) correction cancels. This does **not** mean that higher-order diagrams individually vanish, or that every observable has a terminating expansion. I would phrase it as:

> The two-loop energy and leading mean-shift formulas are exact for Rosenbrock; all subsequent coefficients in these observables’ inverse-temperature expansions vanish.

## 2. The covariance remainder and second order

Set
\[
A_B=B_{00}+2(B_{01}+B_{10})+(4+1/a)B_{11}.
\]
The exact moments immediately give
\[
\langle\psi\rangle
=\frac{A_B/2+b_1}{t}+\frac{3B_{11}}{2t^2}.
\]
For a \(t\)-independent probe,
\[
\operatorname{Cov}(L,\psi)=-\frac{d}{dt}\langle\psi\rangle,
\]
hence
\[
\boxed{\operatorname{Cov}(L,\psi)
=\frac{A_B/2+b_1}{t^2}+\frac{3B_{11}}{t^3}
=\operatorname{covKFormula}+\frac{3B_{11}}{t^3}.}
\]

The proposed mechanism is also correct:
\[
\operatorname{Cov}\!\left(\frac{z^2}{2},\frac{B_{11}z^4}{2}\right)
=\frac{B_{11}}4
\left(\frac{15}{t^3}-\frac{3}{t^3}\right)
=\frac{3B_{11}}{t^3}.
\]
In particular, the formula is exact for linear probes—and more generally whenever \(B_{11}=0\).

**Yes:** a complete second-order expansion, meaning one retaining all terms through \(t^{-3}\) here, must reproduce this correction and is exact for these quadratic-affine probes. There are no higher powers left.

The qualification is about nomenclature and scope: “two-loop” is not uniformly indexed across observables. Nor does this calculation validate any particular unprovided general second-order formula. Suggested staging-note wording:

> For quadratic-affine probes, the first-order covariance formula misses exactly \(3B_{22}/t^3\). The exact inverse-temperature expansion terminates at this next order, so a complete second-order covariance formula would be exact.

## 3. Lean implementation

There is **no mathematical obstruction** to `Fin 7 → Fin 5`. The required vector is correct:
\[
![1,0,1/(\lambda t),0,3/(\lambda t)^2,0,15/(\lambda t)^3].
\]

The practical points are:

1. **Keep positivity hypotheses explicit.**  
   Use \(\lambda>0\), \(t>0\); the Rosenbrock application requires \(a>0\). These supply both Gaussian integrability and the nonzero facts needed for denominator normalization.

2. **Generalize integrability along with the finite-sum identity.**  
   A generic `Fin n → Fin m` result needs integrability of arbitrary relevant monomials, not a proof that silently retains the old degree-four bound. Gaussian polynomial integrability supplies this.

3. **Do not depend on `Fin.sum_univ_seven` existing in the pinned Mathlib.**  
   Check it locally. If absent, repeated `Fin.sum_univ_succ`, or suitable finite-sum simplification, is enough. This is an API issue, not a mathematical one.

4. **Expose natural-number exponents before `ring`.**  
   After expanding the finite sums, simplify the `Fin` coercions so that the powers are literal natural powers.

The degree bounds are exactly right. With
\[
C=B_{01}+B_{10},\quad D=B_{11},\quad r=b_0,\quad s=b_1,
\]
the probe in shear coordinates is
\[
\begin{aligned}
\psi={}&\frac D2u^2
+\left[D z^2+(2D+C/2)z+s\right]u\\
&+\frac D2z^4+(2D+C/2)z^3
+(B_{00}/2+C+2D+s)z^2+(r+2s)z.
\end{aligned}
\]
Multiplication by
\[
L=\frac12(z^2+au^2)
\]
has \(z\)-degree at most six and \(u\)-degree at most four. Thus the 35-entry coefficient array is sufficient, and its pointwise identity is a `ring` problem after finite-sum expansion. Most entries are zero.

I would retain the existing \(5\times5\) result as a wrapper if generalizing it otherwise causes downstream churn.

## 4. Scope and vote

- **A:** Strong target: a short algebraic proof and a useful non-separable check of the contraction weights.
- **B:** Very cheap once `contractT_rosenbrock` is available; worth including.
- **C:** The most informative boundary result: exact mean and covariance approximations do not imply exactness of this energy–probe covariance formula. The degree-six extension is modest and reusable.

Keep the tide focused on the **exact Rosenbrock identity and explicit remainder**, rather than introducing a general second-order `covKFormula`. Treat that general formula as future work.

**Vote: A + B + C.**