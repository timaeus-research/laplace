## 1. Correctness of A–C

**A–C are correct**, assuming the common orthogonal diagonalisation, strict stability \(|\rho_i|<1\), and the intended **ULA stationary covariance**.

One notation issue deserves explicit correction: distinguish
\[
\Sigma_{\rm target}=P^{-1},
\qquad
\Sigma_h=\operatorname{ulaCov}(P,h).
\]
For ordinary ULA with noise covariance \(2hI\), the stationary law is \(N(m,\Sigma_h)\), not \(N(m,P^{-1})\). The burn-in covariance is \(\Sigma_h(I-A^{2k})\). Your mode formulas use \(\Sigma_h\), correctly.

### A: conditional energy and autocovariance

Write \(R=A^\ell\), \(\Sigma=\Sigma_h\), and \(q(x)=\frac12x^\top Hx\). Then
\[
\operatorname{condEnergy}_\ell(x)
=\tfrac12x^\top B_\ell x+b_\ell^\top x+c_\ell,
\]
where
\[
B_\ell=RHR,\qquad b_\ell=RH(I-R)m,
\]
and
\[
c_\ell=
\tfrac12\operatorname{tr}\!\bigl(H\Sigma(I-R^2)\bigr)
+\tfrac12((I-R)m)^\top H((I-R)m).
\]
These agree with your diagonal formulas.

The mixed Wick identity gives
\[
c_\ell^{\rm lag}
=\tfrac12\operatorname{tr}(H\Sigma B_\ell\Sigma)
+(Hm)^\top\Sigma(B_\ell m+b_\ell).
\]
The useful cancellation is already a **matrix identity**:
\[
B_\ell m+b_\ell
=RHRm+RH(I-R)m
=RHm.
\]
Consequently,
\[
\boxed{
c_\ell^{\rm lag}
=\tfrac12\sum_i\lambda_i^2\sigma_i^4\rho_i^{2\ell}
+\sum_i\lambda_i^2\sigma_i^2\widehat m_i^2\rho_i^\ell.
}
\]
Thus your scalar merging identity is exactly right. The distinction between \(\rho^{2\ell}\) and \(\rho^\ell\) is essential: the mean-dependent term can alternate in sign when \(\rho<0\).

The same formula holds at \(\ell=0\), provided you **define**
\(\operatorname{condEnergy}_0=q\); do not represent the zero-step Dirac law using a nonsingular Gaussian precision.

### B: stationary variance and long-run variance

Putting \(\ell=0\) gives the stated stationary variance. Absolute summability follows from \(|\rho_i|<1\), and both displayed expressions for \(\tau^2\) are correct:
\[
\boxed{
\tau^2
=\frac12\sum_i\lambda_i^2\sigma_i^4
 \frac{1+\rho_i^2}{1-\rho_i^2}
+\sum_i\lambda_i^2\sigma_i^2\widehat m_i^2
 \frac{1+\rho_i}{1-\rho_i}
}
\]
and
\[
\boxed{
\tau^2
=\sum_i\frac{\lambda_i^2(1+\rho_i^2)}
 {4hp_i^3\kappa_i^3}
+2\sum_i\frac{\lambda_i^2\widehat m_i^2}{hp_i^2}.
}
\]

### C: finite-\(n\) variance

Correct for \(n\ge1\). In your range-\(n\) sum, the final lag is \(n\), but its coefficient is zero; this is equivalent to the usual sum over lags \(1,\ldots,n-1\).

The identity
\[
G_n(r)=\frac{r\{n(1-r)-(1-r^n)\}}{(1-r)^2}
\]
is correct for \(r\ne1\), including \(n=0\), and the proposed recurrence is correct. Strict stability supplies \(r\ne1\) for both \(r=\rho_i\) and \(r=\rho_i^2\).

## 2. Is this the right process-free proxy?

**Yes.** It is a standard kernel-level definition of stationary autocovariance:
\[
c_\ell=\operatorname{Cov}_{\pi_h}(q,K^\ell q),
\]
where \(K^\ell q(x)\) is the conditional-energy function.

For an actual stationary chain,
\[
\mathbb E[q(X_0)q(X_\ell)]
=\mathbb E[q(X_0)\,\mathbb E(q(X_\ell)\mid X_0)],
\]
so this is exactly \(\operatorname{Cov}(Y_0,Y_\ell)\). Gaussian polynomial moments supply the necessary integrability.

I would phrase the note as follows:

> We define the stationary lag covariance directly from the stationary Gaussian law and the explicit \(\ell\)-step conditional-energy function. For a stationary ULA chain these quantities coincide with its energy autocovariances by conditional expectation. No path-space process or tower-property theorem is formalised here.

One qualification: if the seabed has only the explicit burn-in Gaussian formulas, rather than a formal kernel-iteration theorem, then the identification of those Gaussians with \(K^\ell\) is also an unformalised bridge. Thus “the tower property is the only unformalised step” is accurate **only if that kernel identification is already established**.

Likewise, call C the “lag-sum variance functional” internally, and explain its interpretation as the sample-average variance in prose.

## 3. E5 interpretation

The right claim is
\[
\operatorname{Var}(t\overline Y_n)
=\frac{t^2\tau^2}{n}+O(n^{-2})
\]
for a fixed stable sampler, with the asymptotic interpretation \(n\to\infty\). This concerns **stationary Monte Carlo variance**, not bias or burn-in.

With \(h=\eta/t\) and \(p_i/t\to\lambda_i\),
\[
\rho_i\longrightarrow1-\eta\lambda_i.
\]
Hence the modewise integrated autocorrelation times approach constants, provided the relevant modes satisfy
\[
0<\eta\lambda_i<2.
\]
They are asymptotically \(t\)-independent, not necessarily exactly \(t\)-independent when \(p_i=t\lambda_i+g\).

To conclude that fixed precision needs no growing number of stationary steps, you also need **bounded \(t^2\tau^2\)**. In the intended anchored regime, \(\widehat m_i=O(t^{-1})\) supplies this, and the mean contribution to \(t^2\tau^2\) is \(O(t^{-1})\). Without the mean scaling, constant autocorrelation times alone do not imply bounded estimator variance.

A good E5 statement is:

> Under the anchored scaling and a fixed strictly stable scaled step size, the variance of the scaled observable and its integrated autocorrelation factors remain bounded as \(t\to\infty\). Consequently, stationary sampling requires an asymptotically \(t\)-independent number of steps for fixed absolute precision. This does not control initialization error, discretisation bias, minibatch bias, or computational cost per step.

Be cautious with “unlike burn-in”: the **contraction factor per step** is also asymptotically \(t\)-independent. Burn-in can nevertheless grow logarithmically with \(t\) when a fixed initial displacement must be reduced to the shrinking stationary fluctuation scale. State the initialization and tolerance before making that contrast.

**Yes, contrast with independent replicates:**
\[
\operatorname{Var}(t\overline Y_n^{\rm iid})=\frac{t^2c_0}{n},
\qquad
\operatorname{Var}(t\overline Y_n^{\rm chain})\sim\frac{t^2\tau^2}{n}.
\]
Use the *same stationary law* for this comparison. The \(d/2\) baseline belongs to the corresponding unbiased/small-step limit; finite scaled ULA steps retain the \(\kappa_i\) factors.

Finally, yes: the factor two is precisely the AR(1) versus centered squared-AR(1) distinction:
\[
\frac{1+\rho}{1-\rho}\sim\frac{2}{\eta\lambda},
\qquad
\frac{1+\rho^2}{1-\rho^2}\sim\frac{1}{\eta\lambda},
\]
for small \(\eta\lambda\). There is no single universal energy IAT: \(\tau^2/c_0\) is the variance-weighted average of the modewise quadratic and linear IATs.

## 4. Lean route and pitfalls

The proposed route is sound. I would make these adjustments.

### Avoid the 15-term integrability tree

Prove a reusable covariance constant-shift lemma at the expectation layer. If
\[
E(f)=Z^{-1}\int fw,\qquad E(1)=1,
\]
then the proof needs only integrability of
\[
w,\quad qw,\quad fw,\quad qfw,
\]
followed by integral linearity and ring algebra:
\[
E(q(f+c))=E(qf)+cE(q),\qquad E(f+c)=E(f)+c.
\]
For the second identity, normalization \(E(1)=1\) is essential.

Here \(f\) is the **whole quadratic-plus-linear probe**. Establish its integrability and that of \(qf\) once using Gaussian polynomial integrability or a degree-four growth bound. Do not re-expand the conditional mean into every monomial merely to remove its constant.

If convenient infrastructure already exists, representing the normalized density as a probability measure makes constant-shift invariance even cleaner. Otherwise, a raw weighted-integral lemma is sufficient and cheaper.

### Cancel before diagonalising

After applying `tiltedCov_quadForm_quadProbe`, prove
\[
B_\ell m+b_\ell=R Hm
\]
and combine the Wick mean terms **before** entering coordinates. This removes the need to formalise the scalar cancellation separately for every mode and simplifies the frame calculation.

### Package the stationary Gaussian conversion

For precision \(Q=\Sigma_h^{-1}\) and tilt \(v=Qm\), isolate reusable lemmas asserting:
- \(Q\) is positive definite;
- \(Q^{-1}=\Sigma_h\);
- `tiltMean Q (Q *ᵥ m) = m`.

Also avoid overloading `P`: it is the target precision in the sampler formulas but would be the stationary precision in the Wick theorem instantiation.

### Summation and geometric-series details

For B:

- Prove **absolute summability** of the lag formula explicitly.
- Handle \(\rho^\ell\) using \(|\rho|<1\); \(\rho\) need not be nonnegative.
- Obtain \(|\rho^2|<1\) through a small helper lemma.
- Prove a shifted geometric identity
  \[
  \sum_{\ell=0}^\infty r^{\ell+1}=\frac r{1-r}
  \]
  once.
- Move the finite mode sum outside the `tsum` only after supplying the summability hypotheses.

The proposed Mathlib ingredients are appropriate; check exact lemma names and argument order against the installed version.

For C, distinguish natural-number subtraction from real subtraction. A clean definition is
\[
G_n(r)=\sum_{j\in\operatorname{range}(n)}
\bigl((n:\mathbb R)-(j+1:\mathbb N)\bigr)r^{j+1}.
\]
If you instead use `((n - (j + 1) : ℕ) : ℝ)`, rewrite casts using the range bound before ring reasoning. Supply \(1-r\ne0\) before `field_simp`.

Finally, avoid asking a giant `ring` call to distribute nested finite sums: first normalize the sums using `Finset.sum_add_distrib`, scalar distribution, and small pointwise identities.

## 5. Cheap additions

My priorities would be:

1. **Lag-zero compatibility and absolute summability.** These make the definitions coherent and justify the long-run variance terminology.

2. **Nonnegativity of \(\tau^2\).** Immediate from the closed form and \(-1<\rho_i<1\), even though individual lag covariances can be negative.

3. **The exact finite-\(n\) correction**, obtained almost for free from C:
   \[
   n+2G_n(r)
   =n\frac{1+r}{1-r}
    -\frac{2r(1-r^n)}{(1-r)^2}.
   \]
   Writing \(a_i=\frac12\lambda_i^2\sigma_i^4\) and
   \(b_i=\lambda_i^2\sigma_i^2\widehat m_i^2\), this gives
   \[
   \operatorname{Var}(\overline Y_n)
   =\frac{\tau^2}{n}
   -\frac2{n^2}\sum_i\left[
   a_i\frac{\rho_i^2(1-\rho_i^{2n})}{(1-\rho_i^2)^2}
   +b_i\frac{\rho_i(1-\rho_i^n)}{(1-\rho_i)^2}
   \right].
   \]
   It directly yields \(n\operatorname{Var}(\overline Y_n)\to\tau^2\). The correction need not have one sign when some \(\rho_i<0\).

I would defer D unless the \(t\)-dependent limits and mean-decay lemmas are already packaged. Its coefficient is correct under the stated anchored scaling, but A–C already give a complete stationary-variance story.

**Vote: A+B+C.**