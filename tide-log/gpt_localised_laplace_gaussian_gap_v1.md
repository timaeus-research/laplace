**A and B are correct for the stated product prediction. Two qualifications matter: the unscaled energy discrepancy is \(C_1/t^2\), not \(C_1/t\), and the product is the transform of a centered Gaussian—not generally the Gaussian obtained by retaining the displaced localiser.**

Write \(q=1+s>0\) and
\[
B_g=\sum_i\frac{g}{2\lambda_i},\qquad
E_1=\sum_i e_{1i},\qquad C_1=E_1+B_g.
\]

## 1. Correctness, signs, bounds, and thresholds

### A and B

The Gaussian expansion is
\[
\Lambda^G_t(s)
=q^{-d/2}\left(1+\frac{sB_g}{qt}\right)+O(t^{-2}),
\]
while tide 90 gives
\[
\Lambda_t(s)
=q^{-d/2}\left(1-\frac{sE_1}{qt}\right)+O(t^{-2}).
\]
Consequently,
\[
\boxed{\Lambda_t(s)-\Lambda^G_t(s)
=-\frac{sC_1}{q^{d/2+1}t}+O(t^{-2}).}
\]
Thus the signs and the power in A and B are right.

### The energy normalization needs correction

The consistent three expansions are
\[
\boxed{
\begin{aligned}
\langle L\rangle_{\rm loc}-P(t)
  &=\frac{C_1}{t^2}+O(t^{-3}),\\
-\partial_t\langle L\rangle_{\rm loc}+P'(t)
  &=\frac{2C_1}{t^3}+O(t^{-4}),\\
\Lambda_t(s)-\Lambda^G_t(s)
  &=-\frac{sC_1}{q^{d/2+1}t}+O(t^{-2}).
\end{aligned}}
\]
Here the first two remainder orders should, of course, be taken from the actual landed theorems.

In particular, **\(C_1/t\) belongs to the scaled energy discrepancy**
\[
t\langle L\rangle_{\rm loc}-tP(t)=C_1/t+O(t^{-2}).
\]
The prompt’s unscaled \(C_1/t\) assertion cannot coexist with its \(2C_1/t^3\) derivative assertion.

Indeed,
\[
P(t)=\frac d{2t}-\frac{B_g}{t^2}+O(t^{-3}),
\qquad
\langle L\rangle_{\rm loc}
=\frac d{2t}+\frac{E_1}{t^2}+O(t^{-3}).
\]
This identifies exactly the stated \(C_1=\sum_i(e_{1i}+g/(2\lambda_i))\). The transform check also matches:
\[
-\partial_s(\Lambda_t-\Lambda_t^G)(0)
=t(\langle L\rangle_{\rm loc}-P).
\]
As you note, this is a coefficient check—not justification for differentiating a pointwise-in-\(s\) remainder.

### Square-root bound

Your bound is valid. In fact, for every \(x\ge -1\),
\[
\sqrt{1+x}-1-\frac x2
=-\frac{x^2}{2(\sqrt{1+x}+1)^2},
\]
so
\[
1+\frac x2-\frac{x^2}{2}
\le \sqrt{1+x}\le 1+\frac x2.
\]
Thus \(|x|\le \tfrac12\) is sufficient but unnecessary for this particular estimate.

If you nevertheless use that range for the **two separate roots**, you need both
\[
t\ge \frac{2g}{\lambda_{\min}},
\qquad
t\ge \frac{2g}{q\lambda_{\min}}.
\]
A convenient eventual threshold is
\[
T=\max\left(1,\frac{2g}{\lambda_{\min}\min(1,q)}\right).
\]
The threshold in the question alone does not handle \(-1<s<0\). Handle an empty index set separately, or avoid introducing \(\lambda_{\min}\) by taking finite maxima of coordinatewise thresholds.

## 2. Recommended proof route

The two-root plus `ratio_rate_order2` route is sound. **A shorter route is one rational perturbation followed by the exact square-root remainder identity.**

For \(t>0\), set
\[
z_t=\frac{sg}{qt\lambda+g}.
\]
Then
\[
\sqrt{\frac{t\lambda+g}{qt\lambda+g}}
=q^{-1/2}\sqrt{1+z_t}.
\]
Moreover,
\[
z_t-\frac{sg}{q\lambda t}
=-\frac{sg^2}{q\lambda t(q\lambda t+g)}.
\]
Since \(g\ge0\),
\[
|z_t|\le\frac{|s|g}{q\lambda t},
\qquad
\left|z_t-\frac{sg}{q\lambda t}\right|
\le\frac{|s|g^2}{q^2\lambda^2t^2}.
\]
Also \(1+z_t=q(t\lambda+g)/(qt\lambda+g)>0\), so the square-root identity applies without an additional smallness threshold. It yields
\[
\left|
\sqrt{\frac{t\lambda+g}{qt\lambda+g}}
-q^{-1/2}\left(1+\frac{sg}{2q\lambda t}\right)
\right|
\le
\frac{g^2(|s|+s^2)}{2q^{5/2}\lambda^2t^2}.
\]

This gives an explicit per-factor constant and avoids a quotient of two asymptotic expansions. For Lean, I would retain the constant in factored form involving `Real.sqrt q`, rather than normalize fractional powers immediately.

Suggested sequence:

1. Generic square-root first-order remainder lemma for \(x\ge-1\).
2. Rational perturbation identity and per-factor rate.
3. Apply `prod_one_rate2` to the normalized factors \(\sqrt{1+z_{t,i}}\).
4. Restore the common prefactor and only then rewrite it as \(q^{-d/2}\).
5. Combine A and tide 90 using the triangle inequality and coefficient algebra.

For B, the remainder constant can simply be the sum of the two existing constants, after taking the maximum threshold. The final algebra is `ring`/`field_simp` territory; `linarith` handles the resulting inequalities.

A bare Lipschitz estimate for square roots does **not** by itself identify the first-order coefficient with an \(O(t^{-2})\) error. The exact remainder identity supplies precisely that missing ingredient.

## 3. Nearby additions worth landing

### A shared-coefficient corollary is worthwhile

Use the **existing invariant coefficient definition**, rather than introduce a competing definition. A lightweight corollary can collect:

- scaled energy discrepancy: \(C_1/t\);
- variance-minus-Gaussian-variance discrepancy: \(2C_1/t^3\);
- transform discrepancy: \(-sC_1q^{-d/2-1}/t\).

Under the usual Gibbs differentiation identity,
\[
-\partial_t\langle L\rangle=\operatorname{Var}(L),
\]
and for the centered Gaussian prediction,
\[
-P'(t)=\operatorname{Var}_G(L).
\]
That makes the second statement especially readable.

I would land the transform theorem first and treat this packaging as a small corollary, not a prerequisite.

### Name the Gaussian scaled-energy transform

“**Localized Gaussian scaled-energy Laplace transform**” is a precise name. Its relationship to the E3 LLC proxy is
\[
-\partial_s\Lambda_t^G(0)
=tP(t)=\frac12t\,\operatorname{tr}\!\left(H(tH+gI)^{-1}\right).
\]
It is the transform of the **random scaled quadratic energy**, not the transform of the scalar LLC proxy.

### Important nearby distinction: displaced Gaussian versus centered prediction

Precision alone does not specify the Gaussian mean. Keeping the localiser centered at \(u_0\) in the quadratic model produces coordinate means
\[
m_i=\frac{a_i}{t\lambda_i+g}.
\]
Its transform is
\[
\Lambda_t^{G,\mathrm{anch}}(s)
=\Lambda_t^G(s)
\exp\!\left(
-\frac{st}{2}\sum_i
\frac{\lambda_i a_i^2}
{(t\lambda_i+g)(qt\lambda_i+g)}
\right).
\]
Thus its first-order correction includes
\[
-\frac{s}{qt}\sum_i\frac{a_i^2}{2\lambda_i}.
\]
Against this **anchored** Gaussian, the discrepancy coefficient would instead be
\[
C_1-\sum_i\frac{a_i^2}{2\lambda_i}.
\]
This does not invalidate A or B, but it makes “centered Gaussian prediction” an important qualification.

## 4. Wording against E2/E3

Your wording is fair with those qualifications. I suggest:

> For fixed localiser strength and anchor, and each fixed \(s>-1\), the exact localized scaled-energy transform differs from the centered Gaussian trace-based prediction by
> \[
> -\frac{sC_1}{(1+s)^{d/2+1}t}+O(t^{-2}).
> \]
> The same invariant anharmonic-plus-anchor coefficient \(C_1\) governs the \(t^{-2}\) unscaled energy discrepancy and the \(2C_1t^{-3}\) variance discrepancy.

Add that thresholds and constants may depend on \(s\); no uniformity near \(s=-1\), nor differentiation of the transform remainder, is claimed.

Your cancellation remark is correct:
\[
e_{1i}+\frac g{2\lambda_i}
=e_{0i}+\frac{a_i^2}{2\lambda_i}
-\frac{a_i\alpha_i}{2\lambda_i^2}.
\]
At the minimum anchor, \(C_1=\sum_i e_{0i}\), independent of \(g\). Say the separate localiser contribution is **nonnegative**, rather than positive, since \(g=0\) is allowed.

**Vote: bundle A+B, using the single-rational-perturbation square-root route, with an explicit centered-Gaussian qualification and corrected energy normalization. Add the shared-\(C_1\) corollary only as lightweight packaging.**