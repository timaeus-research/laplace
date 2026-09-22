## 1. A and B are correct; the signed third moment removes the half-power loss

Write \(a=gx_0\), \(y=ax-gx^2/2\), and \(b=(a^2-g)/2\). Your algebra is correct:
\[
x\phi-x-ax^2-bx^3
=x\bigl(\phi-1-y-y^2/2\bigr)
-\frac{g^2x_0}{2}x^4+\frac{g^2}{8}x^5.
\]

The proposed global exponential bound also works. Since
\[
y\le M:=gx_0^2/2,
\]
put \(D=e^M+3\). For \(|y|\le1\), `Real.exp_bound` at \(n=3\) gives \(2|y|^3/9\). For \(|y|>1\), the triangle inequality and \(e^y\le e^M\) give
\[
|e^y-1-y-y^2/2|\le D|y|^3.
\]

Consequently, your remainder \(R\) satisfies
\[
|R(x)|\le A_4x^4+A_6x^6+A_8x^8
\]
with, for example,
\[
\begin{aligned}
A_4&=4D|a|^3+\frac{g^2|x_0|}{2}+\frac{g^2}{16},\\
A_6&=\frac{Dg^3}{4}+\frac{g^2}{16},\\
A_8&=\frac{Dg^3}{4}.
\end{aligned}
\]
These follow from
\[
|y|^3\le4\bigl(|a|^3|x|^3+(g/2)^3|x|^6\bigr)
\]
and the two fixed, rather than \(t\)-dependent, inequalities for \(|x|^5\) and \(|x|^7\).

Thus the even-moment bounds at \(k=2,3,4\) imply, eventually for \(t\ge1\),
\[
|\langle R\rangle|\le K/t^2.
\]

**The third-moment coefficient is exactly right:**
\[
t^2\langle x^3\rangle\longrightarrow
-\frac{5!!\,\alpha}{6\lambda^3}
=-\frac{5\alpha}{2\lambda^3}.
\]
The stated quantitative theorem therefore gives
\[
|\langle x^3\rangle|\le M_3/t^2,
\qquad
|t\langle x^3\rangle|\le M_3/t.
\]
Keeping this term *signed until after integration* is the essential improvement.

Set \(N=\langle x\phi\rangle\), \(Z=\langle\phi\rangle\). The expansion yields
\[
N=\langle x\rangle+a\langle x^2\rangle+b\langle x^3\rangle+\langle R\rangle,
\]
hence \(|tN-c|\le K_N/t\). With \(|Z-1|\le K_Z/t\), enlarge the threshold until \(Z\ge1/2\), and use
\[
\left|\frac{tN}{Z}-c\right|
\le 2\bigl(|tN-c|+|c|\,|Z-1|\bigr).
\]
This proves A’s sharp scaled rate. Dividing by \(t\) and combining with `locLeading_sub_le` proves
\[
|\langle x\rangle_{\rm loc}-P_t|\le K/t^2.
\]

B then follows directly from tide 66’s exact reduction and finite summation. For coordinate \(j\), a valid eventual constant is
\[
K_j=\sum_i |Q_{ji}|K_i,
\]
after taking a common threshold. There is no further analytical loss.

## 2. Yes—on this fixed family, with an explicit interpretation of \(O(S^2)\)

B certifies the displayed formula’s second-order remainder **for the fixed-dimensional, rotated-separable anharmonic family with isotropic localisation**.

Suggested wording:

> For fixed admissible oscillator parameters, orthogonal frame, localiser strength, and anchor, the exact localised mean differs from the displayed Laplace/Hessian-route expression by \(O(t^{-2})\), coordinatewise and hence in Euclidean norm. Since \(S_t=(tH+gI)^{-1}\) with fixed positive-definite \(H\), this is equivalently an \(O(\|S_t\|^2)\) remainder.

One logical detail matters: merely saying \(S_t=O(t^{-1})\) does **not** establish that equivalence. Here you have the stronger fact
\[
\|S_t\|_{\rm op}=\frac1{t\lambda_{\min}(H)+g}
=\Theta(t^{-1}).
\]
For \(t\ge1\),
\[
t^{-2}\le(\lambda_{\min}(H)+g)^2\|S_t\|_{\rm op}^2.
\]

Caveats to retain:

- Constants and thresholds may depend on all fixed parameters, including \(g,w_0,Q\) and dimension.
- This is not uniform over parameter degenerations or anchors growing with \(t\).
- It does not establish the formula for arbitrary nonseparable potentials.
- For a vector remainder, interpret “\(O(S^2)\)” through a norm or a stated coordinatewise bound—not as an unspecified matrix-order assertion.

## 3. C has a short analytical bridge: integration by parts supplies the missing mean coefficient

There is a useful qualification to “the second-order mean is absent, so defer.” It is absent as an available theorem, but it follows from the supplied moment theorems and one exact identity:
\[
\lambda\langle x\rangle+\frac\alpha2\langle x^2\rangle
+\frac\gamma6\langle x^3\rangle=0.
\]
This holds for \(t>0\) by integrating the derivative of \(e^{-t\ell(x)}\); quartic decay removes the boundary term.

Specifically, write
\[
\langle x^2\rangle=\frac1{\lambda t}+\frac{B_2}{t^2}+O(t^{-3}),
\qquad
B_2=\frac{5\alpha^2}{4\lambda^4}-\frac{\gamma}{2\lambda^3}.
\]
Combining this with the third-moment rate gives
\[
\langle x\rangle
=-\frac{\alpha}{2\lambda^2t}+\frac{B_1}{t^2}+O(t^{-3}),
\qquad
B_1=-\frac{5\alpha^3}{8\lambda^5}
+\frac{2\alpha\gamma}{3\lambda^4}.
\]

For reference, the resulting localised coefficient, with \(a=gx_0\), is
\[
\boxed{
c'=B_1
+\frac{a\alpha^2}{\lambda^4}
-\frac{a\gamma}{2\lambda^3}
+\frac{\alpha g}{\lambda^3}
-\frac{\alpha a^2}{2\lambda^3}
-\frac{ag}{\lambda^2}.
}
\]

However, **proving the stated \(O(t^{-2})\) remainder in \(t\langle x\rangle_{\rm loc}\) requires more than A’s Taylor estimate**. A straightforward route is:

- expand \(x\phi\) through degree five, with an even-power-controlled remainder starting at degree six;
- use the signed fifth-moment bound, as well as the supplied lower moment expansions;
- prove \(Z=1+d_1/t+O(t^{-2})\), where
  \[
  d_1=-\frac{a\alpha}{2\lambda^2}+\frac{a^2-g}{2\lambda};
  \]
- perform one more order of ratio bookkeeping.

So C needs **no genuinely new asymptotic input**, but it does need an integration-by-parts formalisation and higher-order localiser bookkeeping. Unless integration by parts is already convenient in the repository, I would defer full C from tide 67.

## 4. Recommended route and bundle

For A, your proposed route is the best fit to the named infrastructure:

1. A reusable exponential remainder lemma for arguments bounded above.
2. The explicit polynomial identity and even-power remainder bound.
3. A sharp numerator rate using the existing signed third-moment theorem.
4. The existing denominator argument.
5. `locLeading_sub_le`.
6. A finite-sum \(t^{-2}\) transport lemma for B.

Integration by parts can replace the third-moment input **at the level of a bound**: solving the identity for \(\langle x^3\rangle\), the leading terms from the existing mean and second-moment rates cancel, giving \(\langle x^3\rangle=O(t^{-2})\). But with `oddMoment_anharmonic_rate` already available, this adds infrastructure without simplifying A. Its real payoff is the second-order mean coefficient for C.

**Vote: approve A + B as the tide 67 bundle.** They close the advertised remainder gap on this family. Defer full C, while recording the integration-by-parts bridge and coefficient as a concrete follow-up.