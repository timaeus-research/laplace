## 1. Correctness of A and B; the first correction

**Yes—A and B are correct for fixed \(s>-1\), \(t>0\), and the fixed parameters stated, with one normalization correction.**

### The exact temperature-change identity

Write \(a=1+s>0\) and use the actual localized partition function
\[
Z_{\mathrm{loc}}(u)
=\int_{\mathbb R}e^{-u\ell(x)-g(x-x_0)^2/2}\,dx.
\]
Then
\[
e^{-st\ell(x)}
e^{-t\ell(x)-g(x-x_0)^2/2}
=e^{-at\ell(x)-g(x-x_0)^2/2},
\]
so
\[
\boxed{\Lambda_t(s)=\frac{Z_{\mathrm{loc}}(at)}{Z_{\mathrm{loc}}(t)}}.
\]
Crucially, the numerator uses \(\operatorname{locPotential1}(at)\) at temperature \(at\), **not** \(\operatorname{locPotential1}(t)\) at temperature \(at\). The latter would incorrectly rescale the localizer.

For Lean, impose \(t>0\) and \(a>0\) on this identity and explicitly discharge partition-function positivity and the needed integrability. For negative \(s\), the observable is unbounded, but the combined integrand is exactly the integrable density at \(at>0\).

### A missing constant in the stated factorization

With your definition
\[
\phi(x)=e^{gx_0x-gx^2/2},\qquad D(u)=\langle\phi\rangle_u,
\]
the actual identity is
\[
\boxed{Z_{\mathrm{loc}}(u)=e^{-gx_0^2/2}Z(u)D(u)}.
\]
Thus “\(Z_{\mathrm{loc}}=ZD\)” is correct only for a partition function with the constant localizer term removed. **This constant cancels in every proposed temperature ratio**, so none of the transform conclusions changes. Audit which convention the landed Lean lemma uses.

Consequently,
\[
\Lambda_t(s)
=a^{-1/2}\frac{J_0(at)}{J_0(t)}
                  \frac{D(at)}{D(t)}
\]
is correct.

### Rate and domain

The rates transfer immediately:
\[
|J_0(at)-\sqrt{2\pi}|\le \frac{K_J/a}{t},
\qquad
|D(at)-1|\le \frac{K_D/a}{t}.
\]
Combine these with eventual positive lower bounds for \(J_0(t)\) and \(D(t)\), then multiply the two ratio estimates. This gives
\[
|\Lambda_t(s)-a^{-1/2}|\le K_s/t.
\]
Thresholds must ensure both \(t\) and \(at\) satisfy all source estimates. Your \(\max(1,1/a)\)-type scaling is right.

The domain \(s>-1\) is the correct open domain corresponding to the limiting Gamma transform. Do not call it necessarily the *maximal finite-\(t\) domain*: at \(s=-1\), the transform is also finite when \(g>0\). For \(s<-1\), the positive quartic produces divergence in nonzero dimension.

### A2: the coefficient is correct

If the landed expansions establish
\[
J_0(u)=\sqrt{2\pi}\left(1+\frac{j_1}{u}+o(u^{-1})\right),
\qquad
D(u)=1+\frac{d_1}{u}+o(u^{-1}),
\]
then, writing \(c_1=j_1+d_1\),
\[
\boxed{
\Lambda_t(s)
=a^{-1/2}
-\frac{s\,c_1}{a^{3/2}t}
+o(t^{-1}).
}
\]
If the source remainders are \(O(u^{-2})\), the final remainder is \(O_s(t^{-2})\). Do not infer that stronger remainder solely from the theorem names.

For the polynomial normalization in the question,
\[
j_1=\frac{5\alpha^2}{24\lambda^3}-\frac{\gamma}{8\lambda^2},
\]
and, with your \(\phi\),
\[
d_1=
\frac{g^2x_0^2-g}{2\lambda}
-\frac{g x_0\alpha}{2\lambda^2}.
\]
These are useful checks against the landed coefficients.

In E2, the corresponding coefficient is also immediate mathematically:
\[
\Lambda_{t,\mathrm{E2}}(s)
=a^{-d/2}
-\frac{s\,a^{-d/2-1}}{t}
  \sum_i(j_{1,i}+d_{1,i})
+o(t^{-1}).
\]

## 2. Recommended single-tide scope and product pitfalls

**Prioritize A+B.** That delivers the substantive advance from finitely many cumulants to a law-identifying transform statement. A2 is a valuable subsequent refinement, but it introduces coefficient-aware reciprocal/product remainder bookkeeping that is unnecessary for the central result.

A clean implementation order is:

1. Exact 1D temperature-change identity.
2. Eventual \(O(1/t)\) bound for the normalized transform
   \[
   R_i(t,s):=\sqrt a\,\Lambda_{t,i}(s),\qquad |R_i-1|\le K_i/t.
   \]
3. Exact rotated/separable partition factorization, hence exact transform factorization.
4. Finite-product rate.
5. Identification of \((a^{-1/2})^d\) with \(a^{-d/2}\).

For the product estimate, if \(K_i\ge0\) and \(t\) is large enough that \(K_i/t\le1\), then \(|R_i|\le2\). Telescoping gives, for \(d\ge1\),
\[
\left|\prod_iR_i-1\right|
\le 2^{d-1}\sum_i|R_i-1|.
\]
Your weaker \(2^d\sum_iK_i/t\) bound is perfectly safe and also convenient for the empty-product case.

**Practical pitfalls:**

- Factor out \(a^{-d/2}\) before using a product lemma centered at \(1\).
- Combine all coordinate thresholds using finite maxima, or a larger finite sum of nonnegative thresholds.
- Keep the rotation/localizer identity exact: isotropy is what makes the localizer separable in frame coordinates.
- Handle positivity of the base \(a\) explicitly when converting square roots and real powers.

Since `prod_rate` is already landed, reuse it if its hypotheses fit. I would not spend the tide searching for a particular Mathlib product-difference lemma: a short induction or telescoping proof is robust, and I would not promise an exact library name without checking the installed version.

## 3. Nearby opportunities

### Uniformity is cheaper than it first appears

There is a useful strengthening beyond compact intervals:

> For each fixed \(\delta>0\), the same absolute \(O(1/t)\) estimate can hold uniformly over **all** \(s\ge-1+\delta\).

Indeed, \(a\ge\delta\) gives
\[
\frac1{at}\le\frac1{\delta t},
\qquad
a^{-d/2}\le\delta^{-d/2}.
\]
The source estimates therefore apply uniformly once
\[
t\ge \max(1,\delta^{-1})T,
\]
and the normalized ratio/product constants can be bounded using \(1/a\le1/\delta\). No upper bound \(S\) is needed.

Thus a natural optional strengthening is
\[
\exists K_\delta,T_\delta,\quad
\forall t\ge T_\delta,\ \forall s\ge-1+\delta,\quad
|\Lambda_{t,\mathrm{E2}}(s)-(1+s)^{-d/2}|
\le K_\delta/t.
\]
This remains fixed-\(\delta\), fixed-parameter asymptotics; it is not uniform as \(s\downarrow-1\).

If the proof exposes the constants cleanly, this is a better nearby addition than characteristic functions.

### Characteristic functions are not the cheap route

Substituting imaginary \(s\) requires complex-valued integrals and complex-temperature asymptotics; the landed real-\(u\) estimates do not automatically supply them. Real Laplace transforms already identify the nonnegative limiting law.

You also already cover the limiting MGF domain: setting \(\theta=-s\) gives
\[
\mathbb E[e^{\theta t\ell}]
\longrightarrow (1-\theta)^{-1/2},
\qquad \theta<1.
\]
That is a rephrasing, not a separate theorem requiring new analytic machinery.

The cumulant discussion is appropriate as a consistency remark. Explicitly avoid suggesting that differentiation of the pointwise transform limit is justified by the \(O(1/t)\) statement alone.

## 4. Wording relative to §14

Your proposed gloss is fair, with these qualifications:

- All quartic, frame, center, and localizer parameters are fixed as \(t\to\infty\), including \(g\) and \(w_0\).
- The expectation is under the **normalized exact E2 localized Gibbs measure**, not automatically under a posterior or another global measure.
- The transformed observable is the unlocalized energy \(t(L\circ A)\), not \(t\) times the full temperature-dependent localized potential.
- The stated rate is pointwise in \(s>-1\), unless the uniform strengthening is actually proved.
- Weak convergence is a mathematical corollary cited in prose, not a Lean theorem delivered by this tide.
- Assume \(d\ge1\) when naming \(\Gamma(d/2,1)\). For \(d=0\), the transform is \(1\) and the law is \(\delta_0\).

Suggested wording:

> For fixed admissible E2 parameters and fixed localizer, the Laplace transform of \(t(L\circ A)\) under the exact localized Gibbs measure converges, for every fixed \(s>-1\), to \((1+s)^{-d/2}\), with eventual error \(O_s(t^{-1})\). For \(d\ge1\), the continuity theorem for Laplace transforms therefore yields convergence in distribution to \(\Gamma(d/2,\mathrm{rate}\ 1)\). The formalized result is the transform identity and quantitative transform convergence; the weak-convergence implication is stated in prose.

The nonnegativity needed for that Laplace-transform argument follows from the admissible quartics. This establishes the fixed-localizer, large-\(t\) Gamma regime, **not by itself both regimes or a crossover theorem** from the note.

**Vote: A+B.** Correct the partition-function normalization wording, land the exact temperature-change bridge and E2 transform rate, and treat uniformity away from \(s=-1\) as an optional strengthening. Defer A2 unless coefficient-aware quotient infrastructure makes it genuinely routine.