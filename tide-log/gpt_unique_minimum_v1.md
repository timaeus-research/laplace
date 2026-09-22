## 1. Thresholds and interpretation

The thresholds are correct, but **A’s headline and B’s equality case need correction**.

### A: exact condition for **0 to be the unique global minimiser**

Factor
\[
\ell(x)=x^2q(x),\qquad
q(x)=\frac{\lambda}{2}+\frac{\alpha x}{6}+\frac{\gamma x^2}{24}
=\frac{\gamma}{24}\left(x+\frac{2\alpha}{\gamma}\right)^2
+\frac{3\lambda\gamma-\alpha^2}{6\gamma}.
\]
For \(\lambda,\gamma>0\):

- If \(\alpha^2<3\lambda\gamma\), then \(q(x)>0\) everywhere, so \(\ell(x)>0\) for \(x\ne0\).
- If \(\alpha^2=3\lambda\gamma\), then
  \[
  \ell(x)=\frac{\gamma}{24}x^2\left(x+\frac{2\alpha}{\gamma}\right)^2.
  \]
  Thus the global minimisers are exactly \(0\) and \(-2\alpha/\gamma\). They are distinct because the equality and positivity assumptions force \(\alpha\ne0\).
- If \(\alpha^2>3\lambda\gamma\), the proposed witness gives
  \[
  \ell(-2\alpha/\gamma)
  =\frac{2\alpha^2(3\lambda\gamma-\alpha^2)}{3\gamma^3}<0.
  \]

Consequently,
\[
\boxed{0\text{ is the unique global minimiser}\iff\alpha^2<3\lambda\gamma.}
\]

**Do not omit “0 is” from the iff.** Above the threshold, the potential actually has a unique global minimiser elsewhere. The proposed negative-value theorem proves that **0 ceases to be globally minimising**, not that global minimiser uniqueness fails.

Under the note’s parametrisation, \(\alpha^2=a^2\lambda^3\) and \(\lambda\gamma=\lambda^3\), giving the threshold \(a^2<3\).

### B: exact condition for additional critical points

We have
\[
\ell'(x)=\frac{x}{6}\bigl(\gamma x^2+3\alpha x+6\lambda\bigr).
\]
The quadratic discriminant is
\[
9\alpha^2-24\lambda\gamma.
\]
Its roots, when real, cannot be zero because its constant term is \(6\lambda>0\). Hence
\[
\boxed{\exists x\ne0,\ \ell'(x)=0
\iff \frac83\lambda\gamma\le\alpha^2.}
\]

However, distinguish:

- **\(\alpha^2<\frac83\lambda\gamma\):** only one critical point, namely \(0\).
- **\(\alpha^2=\frac83\lambda\gamma\):** one additional, double root of \(\ell'\), at
  \[
  x_*=-\frac{3\alpha}{2\gamma}.
  \]
  This is a **stationary inflection**, not a local maximum or minimum:
  \[
  \ell''(x_*)=0,\qquad \ell'''(x_*)=-\alpha/2\ne0.
  \]
- **\(\frac83\lambda\gamma<\alpha^2<3\lambda\gamma\):** there is an additional local maximum and local minimum, both at positive potential values.

Thus “keeps the minimum unique” is appropriately read as **“keeps the designated centre as the unique global minimiser.”** Unique critical point requires \(a^2<8/3\).

The staging note should flag the extra extrema for **\(8/3<a^2<3\)**, not the closed-left interval. At equality the potential remains strictly decreasing towards \(0\) from the left and strictly increasing to its right, despite the additional stationary point; it is still unimodal in that sense.

E2’s \(a\in\{0.5,1\}\) is safely below both thresholds.

## 2. Lean proof strategy

Both approaches work mathematically. For Lean, I would prefer a **denominator-cleared square identity**, with sign arguments separated from polynomial normalization.

For the auxiliary quadratic:
\[
24\gamma q(x)
=(\gamma x+2\alpha)^2+4(3\lambda\gamma-\alpha^2).
\]

A robust proof structure is:

1. Establish this identity by `ring` after unfolding \(q\).
2. Prove \(0<3\lambda\gamma-\alpha^2\) from `hdisc`.
3. Combine that strict positivity with
   `sq_nonneg (γ * x + 2 * α)` to prove \(0<24\gamma q(x)\).
4. Cancel the positive factor \(24\gamma\), obtaining \(q(x)>0\).
5. Use `sq_pos_of_ne_zero` and `mul_pos` for \(\ell(x)=x^2q(x)\).

This avoids variable denominators and is generally more predictable than asking one large `nlinarith` call to handle the entire quartic argument. The completed-square proof is also fine, using `field_simp` with \(\gamma\ne0\), followed by `ring`.

For the supercritical witness, **your calculation is correct**:
\[
q(-2\alpha/\gamma)=\frac{3\lambda\gamma-\alpha^2}{6\gamma}<0.
\]
First derive \(\alpha\ne0\), then the witness is nonzero and its square is positive. Prove the evaluation identity separately with `field_simp`/`ring`, and finish using multiplication/division sign lemmas.

For the equality theorem, include **nonnegativity everywhere and distinctness of the witness** in a corollary establishing two global minimisers. The bare evaluation \(\ell(-2\alpha/\gamma)=0\) does not itself state that conclusion.

## 3. Other cheap, relevant results

### Nondegeneracy at the designated minimiser

Immediately,
\[
\ell'(0)=0,\qquad \ell''(0)=\lambda>0.
\]
This needs no discriminant assumption. It gives a nondegenerate strict local minimum at \(0\), and continuity of \(\ell''\) gives strict convexity in a neighbourhood.

For the rotated potential,
\[
\nabla L(c)=0,\qquad
\nabla^2L(c)=Q\,\operatorname{diag}(\lambda_i)\,Q^\top.
\]
For square orthogonal \(Q\) and positive \(\lambda_i\), this Hessian is positive definite and invertible. Thus **“Morse at \(w_*=c\)”** is justified.

Do not strengthen that to “the potential is Morse everywhere” under `hdisc`: the \(8/3\) equality case supplies a degenerate critical point while still satisfying `hdisc`.

### A useful convexity bound

Completing another square gives
\[
\ell''(x)
=\frac{\gamma}{2}\left(x+\frac{\alpha}{\gamma}\right)^2
+\lambda-\frac{\alpha^2}{2\gamma}.
\]
Thus \(\alpha^2<2\lambda\gamma\) gives a global positive lower bound on \(\ell''\). In the note’s parametrisation,
\[
\ell''(x)\ge\lambda(1-a^2/2).
\]
So E2’s two choices are actually **globally strongly convex**, a stronger safety statement than merely avoiding the critical-point threshold.

## 4. Scope and vote

**C is correct for square orthogonal \(Q\).** Put \(z=Q^\top(w-c)\). Orthogonality makes this coordinate map injective, so \(w\ne c\) implies some \(z_i\ne0\). Every summand is nonnegative by A, and that summand is positive. At \(w=c\), every coordinate vanishes.

In Lean, isolate the linear-algebra implication
\[
Q^\top(w-c)=0\implies w=c.
\]
For square matrices, \(Q^\top Q=I\) suffices, but deriving the other inverse identity or an orthogonal linear equivalence may be necessary. For rectangular matrices, that assumption alone would not suffice.

**Recommended staging:**

1. **A + C as the core:** positivity, value at the centre, unique global minimiser; include A’s sharpness witnesses.
2. **B as a separate clarification:** valuable because it prevents conflating unique minimiser with unique critical point. Correct the equality-case description.
3. Add centre-Hessian/nondegeneracy results if the derivative infrastructure makes them short.

**Vote: yes to A+B+C, with A explicitly about the minimiser at \(0\), and B separating the stationary-inflection boundary from the two-extra-extrema regime.**