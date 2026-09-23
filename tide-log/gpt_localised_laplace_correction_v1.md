## 1. A, B, and C are correct

Write \(A=1+s>0\), \(j_1=15A_{\mathrm{cubic}}^2/2-3B_{\mathrm{quartic}}\), and \(d_1=\mathrm{locD1}\), avoiding the overloaded \(A\) in implementation. Then
\[
e_1=j_1+d_1
=\frac{a^2-g}{2\lambda}
-\frac{a\alpha}{2\lambda^2}
-\frac{\gamma}{8\lambda^2}
+\frac{5\alpha^2}{24\lambda^3}.
\]
Thus C is a genuine algebraic identity between the landed definitions, not a new analytic assertion.

The two quotients have expansions
\[
\frac{J_0(At)}{J_0(t)}
=1-\frac{j_1s}{At}+O(t^{-2}),\qquad
\frac{D(At)}{D(t)}
=1-\frac{d_1s}{At}+O(t^{-2}).
\]
Consequently,
\[
\sqrt A\,\Lambda_t(s)
=1-\frac{s e_1}{At}+O(t^{-2}),
\]
and hence
\[
\boxed{\left|\Lambda_t(s)-A^{-1/2}
+\frac{s e_1}{A^{3/2}t}\right|\le \frac K{t^2}.}
\]
The sign and power are exactly right.

For E2, put \(d=\#I\) and \(E=\sum_i e_{1,i}\). Then
\[
\boxed{\left|\left\langle e^{-stL\circ A}\right\rangle_{\rm loc}
-A^{-d/2}+\frac{sE}{A^{d/2+1}t}\right|
\le \frac K{t^2}.}
\]
Here the frame map \(A\) and scalar \(1+s\) should again receive different implementation names.

### Applying `ratio_rate_order2`

Yes, directly. For the \(J_0\) quotient, with \(c_0=\sqrt{2\pi}>0\), use
\[
a=c=c_0,\qquad b=c_0j_1/A,\qquad d=c_0j_1.
\]
Its coefficient is
\[
\frac{bc-ad}{c^2}=\frac{j_1}{A}-j_1=-\frac{j_1s}{A}.
\]
The numerator remainder becomes \(K_J/(A^2t^2)\). The denominator lower bound \(J_0(t)\ge c_0/2\) is independent of \(s\). For \(D\), use \(a=c=1\) and its eventual lower bound \(D(t)\ge 1/2\).

**Threshold qualification:** if an input expansion is valid for \(u\ge U\), pointwise one needs
\[
t\ge \max(U,U/A).
\]
Uniformly on \(A\ge\delta>0\), it suffices to take
\[
t\ge \max(U,U/\delta),
\]
along with all denominator-positivity thresholds. Nothing else goes wrong for negative \(s\).

The uniform assertion is sound because
\[
A^{-1}\le\delta^{-1},\qquad A^{-2}\le\delta^{-2},
\qquad \left|\frac{s}{A}\right|
=\left|1-\frac1A\right|\le 1+\delta^{-1}.
\]
But **uniformity must be preserved through the quotient lemma**: pointwise existence of a remainder constant does not alone produce a common \(K_\delta\). If its quantitative constant depends on \(b\), explicitly bound \(b\) uniformly.

## 2. Recommended implementation bundle and proof route

I recommend **A+B+C**, with the following order:

1. Prove C by unfolding coefficient definitions and algebra.
2. Add a reusable two-factor second-order multiplication lemma.
3. Prove the **normalized** one-dimensional expansion.
4. Iterate the multiplication lemma over a finite set.
5. Rescale to obtain the displayed transform statements.

The normalized theorem is the best interface:
\[
\left|\sqrt A\,\Lambda_t(s)
-\left(1-\frac{s e_1}{At}\right)\right|
\le \frac{K_\delta}{t^2}.
\]

**Do not derive the E2 uniform theorem merely by multiplying the unnormalized error estimate by \(\sqrt A\)**: that loses uniformity as \(s\to\infty\). Derive the normalized estimate directly from the exact quotient factorization.

### A small multiplication lemma is enough

Suppose, for \(t\ge1\),
\[
|F-(1+b/t)|\le R/t^2,\qquad
|G-(1+c/t)|\le S/t^2.
\]
Then
\[
|FG-(1+(b+c)/t)|\le C/t^2
\]
with, for example,
\[
C=R+S+|bc|+|b|S+|c|R+RS.
\]
This follows by expanding \(F=1+b/t+r\), \(G=1+c/t+q\).

That same lemma handles both:

- multiplication of the \(J_0\) and \(D\) quotients;
- the finite product of normalized coordinate transforms.

For uniform finite products, the coordinate coefficients are
\[
b_i(s)=-\frac{s}{A}e_{1,i},
\]
so their absolute values have fixed bounds depending only on \(\delta\) and the fixed coordinate parameters.

**The finite-product lemma is the main new reusable ingredient, but not a major conceptual cost.** Uniform constant bookkeeping and rescaling thresholds may be just as much Lean work. Avoid logarithms: they add positivity and Taylor machinery without simplifying this order of expansion.

## 3. One coefficient governs all three corrections—and the candidate law correction

Yes: it is worth explicitly recording that \(E=\sum_i e_{1,i}\) governs the landed mean correction, variance correction, and now transform correction. Set \(k=d/2\). The three formulas are
\[
\begin{aligned}
\mathbb E[tL]&=k+\frac Et+O(t^{-2}),\\
\operatorname{Var}(tL)&=k+\frac{2E}{t}+O(t^{-2}),\\
\mathbb E[e^{-stL}]&=(1+s)^{-k}
-\frac Et\,s(1+s)^{-k-1}+O(t^{-2}).
\end{aligned}
\]
Treat the first two as independently proved results—not consequences of differentiating the transform remainder.

For comparison, the formal second raw-moment correction is
\[
\mathbb E[(tL)^2]
=k(k+1)+\frac{2(k+1)E}{t}+O(t^{-2}),
\]
giving \(3e_1/t\) in one dimension and variance correction \(2E/t\).

### The uniquely suggested signed-measure correction

Let \(G_k=\operatorname{Gamma}(k,\text{rate }1)\), with \(k>0\). Since
\[
-s(1+s)^{-k-1}
=(1+s)^{-k-1}-(1+s)^{-k},
\]
the correction has the Laplace transform of
\[
\boxed{\frac Et\,(G_{k+1}-G_k).}
\]
Equivalently, if \(g_k\) is the Gamma density, the candidate corrected density is
\[
g_k(y)\left[1+\frac Et\left(\frac yk-1\right)\right].
\]
In one dimension this is
\[
g_{1/2}(y)\left[1+\frac{e_1}{t}(2y-1)\right].
\]

This is a **signed correction**, not necessarily a nonnegative density approximation on the entire half-line. In particular, for \(E<0\), its bracket eventually becomes negative.

It is also equivalent, **to first order only**, to keeping shape \(k\) fixed and shifting the rate:
\[
\operatorname{Gamma}\!\left(k,\;1-\frac{E}{kt}\right).
\]
A shape shift alone instead introduces a \(\log(1+s)\) term, so it is not the right parametrization.

### What the transform estimate actually proves

It proves the correction against the exponential test functions in its stated domain and identifies the only possible finite signed-measure correction having that Laplace transform.

It does **not**, by itself, prove
\[
\operatorname{Law}(tL)
=G_k+\frac Et(G_{k+1}-G_k)+O(t^{-2})
\]
in total variation, density norm, distribution-function norm, or against arbitrary bounded continuous tests. Those require additional density estimates, inversion control, or an appropriate signed-measure compactness argument.

Thus: **identify the candidate correction now; do not advertise a proved general Edgeworth expansion.** For \(d=0\), keep the empty-product case separate: the law is exactly \(\delta_0\), and \(E=0\).

## 4. Suggested wording for §14

A defensible statement is:

> For fixed model parameters, the first finite-temperature correction to the Gamma limit of the localized scaled energy is governed by the same coefficient \(E\) that controls the mean and variance corrections. More precisely, its Laplace transform equals
> \[
> (1+s)^{-d/2}
> -\frac Et\,s(1+s)^{-d/2-1}+O_\delta(t^{-2}),
> \]
> uniformly for \(s\ge-1+\delta\), for every fixed \(\delta>0\). The correction is the Laplace transform of \(E(\Gamma(d/2+1,1)-\Gamma(d/2,1))\).

Then add:

> This is a transform-level correction for the exact localized measure; a distributional or density-level expansion, and transfer to an unlocalized sampling law, require separate estimates.

If §14 uses \(tK\), explicitly identify \(K\) with the energy variable proved here, or cite the existing bridge. Keep the qualifications **fixed parameters, fixed dimension, eventual bounds, and separation from \(s=-1\)**.

**Vote: A+B+C, with a normalized uniform 1D theorem and an iterated two-factor second-order product lemma; leave the signed-law expansion as an identified interpretation, not a newly claimed distributional theorem.**