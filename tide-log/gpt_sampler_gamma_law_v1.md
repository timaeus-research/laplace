## 1. Correctness and domains

**A1–A3 are correct**, with the following domain and interpretation qualifications.

Write
\[
X(u)=\frac t2u^\top Hu,\qquad p_i=t\lambda_i,\qquad a_i=p_i+\gamma,
\]
assuming \(H\succ0\), \(t>0\), \(\gamma\ge0\).

### A1: general precision-ratio identity

For symmetric positive-definite \(Q\) and \(Q+stH\),
\[
\mathbb E_Q[e^{-sX}]
=\frac{\sqrt{\det Q}}{\sqrt{\det(Q+stH)}}.
\]
There is **no commutation assumption**, and \(s\) need not be nonnegative. Indeed, for this identity alone, \(H\) can be any symmetric matrix.

The important analytic hypothesis is positive definiteness of the *modified precision*. It makes the numerator integrable, including when the test function itself is unbounded because \(s<0\).

### A2: localised Gibbs

Here
\[
r_i=\frac{a_i}{p_i}=1+\frac{\gamma}{p_i},
\qquad
\mathbb E[e^{-sX}]
=\prod_i(1+s/r_i)^{-1/2}.
\]
Thus \(s>-1\) is a clean sufficient domain. The **maximal finite-transform domain**, in positive dimension, is
\[
s>-\min_i r_i.
\]
When \(\gamma>0\), this is larger than the proposed domain:
\[
s>-1-\frac{\gamma}{p_{\max}}.
\]

In eigen-coordinates,
\[
X\ \overset d=\ \sum_i G_i,\qquad
G_i\text{ independent},\quad G_i\sim\Gamma(1/2,\text{rate }r_i).
\]
At \(\gamma=0\), this becomes \(\Gamma(d/2,1)\), and
\[
\mathbb E[e^{-sX}]=(1+s)^{-d/2}.
\]

**Empty-index qualification:** when \(d=0\), the statistic is identically zero and its transform is \(1\). Do not describe it as an ordinary positive-shape Gamma distribution.

### A3: ULA

Assume \(h>0\) and \(hp_i<2\) for every \(i\). The effective precision is
\[
Q=P-\frac h2P^2,\qquad P=tH,
\]
so
\[
r_i=1-\frac{hp_i}{2}>0.
\]
The proposed product and Gamma decomposition are correct. The maximal finite **Laplace-transform** domain is
\[
s>-\min_i r_i=-\left(1-\frac{hp_{\max}}2\right).
\]
Equivalently, the MGF \(\mathbb E[e^{zX}]\) is finite for
\[
z<1-\frac{hp_{\max}}2.
\]
So your stated inequality is right for the Laplace parameter \(s\), but distinguish it from the MGF parameter.

For localised ULA, assuming \(ha_i<2\),
\[
r_i=\frac{a_i(1-ha_i/2)}{p_i},
\qquad
\mathbb E[e^{-sX}]]
=\prod_i(1+s/r_i)^{-1/2},
\]
with the extraneous closing bracket in this displayed expression understood as a typo; equivalently,
\[
\boxed{\mathbb E[e^{-sX}]=\prod_i(1+s/r_i)^{-1/2}.}
\]
Its natural domain is \(s>-\min_i r_i\). Using \(s\ge0\) throughout the formal ULA theorem is entirely reasonable.

Equality of Laplace transforms for all \(s\ge0\) suffices to identify these nonnegative laws, **provided one invokes an appropriate uniqueness theorem**. The coordinatewise Gaussian-square argument is another route; the transform formula alone does not formally establish independence.

## 2. Recommended proof route

### A1: use the partition-function ratio as the intermediate theorem

I would structure it as:

1. Prove the pointwise weighted-integrand identity.
2. Rewrite the expectation as
   \[
   \frac{\operatorname{tiltedZ}(Q+stH,0)}
        {\operatorname{tiltedZ}(Q,0)}.
   \]
3. Rewrite both partition functions using `gaussianZ_matCLM`.
4. Cancel the common \(\sqrt{2\pi}^{\,d}\) factor.

The partition-function-ratio lemma is independently useful and keeps determinant algebra out of the integral proof.

For the pointwise identity, prove the quadratic-form linearity separately:
\[
u^\top(Q+stH)u=u^\top Qu+st\,u^\top Hu.
\]
Then use `Real.exp_add` and scalar ring normalization. Depending on the definitions, the relevant expansions are `add_mulVec`, scalar-multiplication compatibility, and dot-product linearity. **No change of variables or integral factorisation is necessary.**

Record explicitly:
- \(\det Q>0\) and \(\det(Q+stH)>0\);
- their square roots are nonzero;
- \(\sqrt{2\pi}^{\,d}\ne0\).

These are the hypotheses needed for reliable cancellation. Do not rely on Lean’s total division or its default value for a nonintegrable integral to encode the probabilistic domain.

### Determinants and products

The existing diagonalisation lemmas make the eigenbasis route attractive. A useful reusable lemma is
\[
\det(U^\top A U)=\det A
\quad\text{when }U^\top U=I.
\]
Prove this from `det_mul`, `det_transpose`, and
\[
\det(U^\top U)=1;
\]
there is no need to split into \(\det U=1\) and \(\det U=-1\).

For the first product theorem, I would prefer the Lean-friendly expression
\[
\prod_i\left(\sqrt{1+s/r_i}\right)^{-1}
\]
over real powers. Then obtain the \(^{-1/2}\) presentation as a corollary if convenient. Positivity supplies the hypotheses for moving square roots through products and quotients.

### Positive definiteness for ULA

For **\(s\ge0\)**, the slickest argument is:
\[
Q\succ0,\qquad sP\succeq0
\quad\Longrightarrow\quad Q+sP\succ0.
\]
Likewise, use \(Q_\gamma+s\,tH\) for localised ULA.

Thus:
- establish positivity of the ULA precision once, using the existing eigenbasis diagonalisation;
- add the nonnegative quadratic form for the transform theorem.

For the **full negative-\(s\) domain**, eigenvalue positivity is the natural route:
\[
p_i(1-hp_i/2+s)>0.
\]
I would not replace this with a commuting-positive-definite-product proof. The factorisation is mathematically valid, but proving symmetry, commutation, and positivity of the product is unlikely to be shorter than exploiting your existing diagonalisation.

### The `multivariateGaussian` bridge

**Do not budget this as cheap.** Without a density lemma, the bridge requires real infrastructure: linear Gaussian pushforwards/change of variables, or characteristic-function uniqueness after placing both laws on compatible spaces.

Prove A3 for `tiltedExpectation Q 0` this tide. State clearly that the bridge to Mathlib’s separately represented `multivariateGaussian 0 (ulaCov …)` is not part of that theorem. It is mathematically standard, but should not be presented as a machine-checked connection unless it actually is one.

## 3. Nearby extensions and pitfalls

### Cumulants and variance

Yes:
\[
\kappa_n(X)=\frac{(n-1)!}{2}\sum_i r_i^{-n},
\qquad n\ge1.
\]
In particular,
\[
\operatorname{Var}(X)=\frac12\sum_i r_i^{-2}.
\]
For unlocalised ULA,
\[
\operatorname{Var}(X)
=\frac12\sum_i(1-hp_i/2)^{-2}.
\]

This is a worthwhile corollary: discretisation inflates the variance more strongly than the mean in each direction. Localised ULA gives
\[
\operatorname{Var}(X)
=\frac12\sum_i
\left(\frac{p_i}{a_i(1-ha_i/2)}\right)^2.
\]

However, **formal differentiation of the transform is not free**. Unless suitable differentiation-under-integral or Gamma-moment infrastructure already exists, leave cumulants as a mathematical remark and prove variance later via Gaussian fourth moments.

### Minibatch: Gaussianity is the first question

There are two separate issues:

1. **A stationary covariance formula does not imply a Gaussian stationary law.** With non-Gaussian minibatch innovations, the invariant distribution can be non-Gaussian. Covariance alone cannot justify a Gamma decomposition.

2. **Diagonal \(\widetilde C\) is not necessary for some independent-Gamma decomposition**, assuming the stationary law really is centered Gaussian. For \(u\sim N(0,\Sigma)\), diagonalise
   \[
   B=t\,\Sigma^{1/2}H\Sigma^{1/2}.
   \]
   If its eigenvalues are \(b_j>0\), then
   \[
   X\overset d=\frac12\sum_j b_jZ_j^2,
   \]
   with independent standard normals, hence Gamma rates \(1/b_j\).

Diagonal \(\widetilde C\) in the \(H\)-basis gives the **simple original-direction formula**. For covariance eigenvalues
\[
\sigma_i^2=
\frac{1+ht^2\widetilde C_{ii}/2}
     {a_i(1-ha_i/2)},
\]
the rates become
\[
r_i=
\frac{a_i(1-ha_i/2)}
     {p_i(1+ht^2\widetilde C_{ii}/2)}.
\]
Without simultaneous diagonalisation, use the spectrum of \(B\), not these coordinatewise factors.

### Finite time

This is valuable, especially for quantifying burn-in, but not necessary for the current bundle.

From the mode, Gaussian innovations give a centered Gaussian finite-time law. If \(\Sigma_k\succ0\), A1 applies with \(Q_k=\Sigma_k^{-1}\). A covariance-side formula is more robust:
\[
\mathbb E[e^{-sX_k}]
=
\det\!\left(I+s\,t\Sigma_k^{1/2}H\Sigma_k^{1/2}\right)^{-1/2}.
\]
It also handles singular covariance, including \(k=0\), on the appropriate positivity domain. A nonzero initial mean introduces a noncentral exponential factor; a random non-Gaussian initial law need not give a Gaussian finite-time law.

## 4. Wording and comparison with E2/E3

Your gloss is fair with this wording:

> For the centered Gaussian target, under the stable ULA stationary Gaussian law, the scaled quadratic energy is distributed as a sum of independent shape-\(1/2\) Gamma variables. Localisation and discretisation modify their rates.

Add these qualifications:

- The **LLC estimate here is the mean of this statistic**. Its distribution is not the distribution of a finite-chain average, whose uncertainty also depends on temporal correlation.
- Stability requires \(h(t\lambda_i+\gamma)<2\) in every direction.
- Localisation raises the rates and suppresses the mean; ULA lowers those rates relative to the localised Gibbs law and inflates the mean.
- “5% inflation” means the exact multiplier \((1-ha_i/2)^{-1}\) is approximately \(1.05\). The approximation \(1+ha_i/2\) is first-order only.
- Distinguish the proved Gibbs-form expectation theorem from the unproved-in-this-bundle measure-representation bridge.

For B, I would avoid calling the two corrections simply “\(E/t\) and \(h\).” The discretisation parameter in direction \(i\) is **\(hp_i=ht\lambda_i\)**, or \(ha_i\) with localisation. Fixed positive \(h\) cannot remain stable as \(t\to\infty\). To recover the uninflated Gamma limit along a joint limit, require \(h(t)t\to0\) for fixed \(H,\gamma\).

Also distinguish comparison with the universal Gamma transform from comparison with **finite-\(t\) A2**. A2 itself has a localisation correction of order \(1/t\) when \(\gamma\) is fixed. Before asserting the displayed anharmonic correction *relative to A2*, verify that the tide-90 coefficient has that shared localisation contribution removed.

## Vote

**Vote: A1 + A2 + the combined localised-ULA product theorem for \(s\ge0\), with unlocalised A3 as a specialisation.**

Use determinant ratios internally and inverse-square-root products externally. Keep Gamma interpretations, cumulants, and the E2 comparison as carefully qualified prose this tide. Defer the `multivariateGaussian` bridge, minibatch laws, and finite-time extensions.