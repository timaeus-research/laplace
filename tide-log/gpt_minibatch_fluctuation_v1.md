## 1. A–C: correctness and the positivity proof

**A and B are correct**, assuming a finite real index type, orthogonal \(U\), symmetric \(H=U\operatorname{diag}(\lambda)U^\top\), and \(|\rho_i|<1\). **C’s algebra is correct, but its first-order interpretation needs correction.**

### A: the series argument is a good Lean route

For \(D=\operatorname{diag}(a)\), establish
\[
x^\top\operatorname{diagLyapunov}(a,N)x
 =\sum_{r=0}^{\infty}(D^rx)^\top N(D^rx).
\]
This identity does not require \(N\succeq0\). For each \(i,j\), geometric summability follows from
\[
|a_i a_j|<1,
\]
and multiplication by \(x_iN_{ij}x_j\) preserves summability. Finite summation then gives summability of the quadratic-form series.

Your proposed interchange—finite-sum/`tsum` interchange twice, with scalar multiplication moved through `tsum`—is appropriate. **Prove the entrywise summability facts first**, then the summability of the double finite sum; do not attempt the interchange solely by rewriting expressions involving potentially nonsummable `tsum`s.

If \(N\succeq0\), every summand is nonnegative, so
\[
x^\top\operatorname{diagLyapunov}(a,N)x\ge x^\top Nx.
\]
Together with symmetry, this proves the stronger result
\[
\operatorname{diagLyapunov}(a,N)-N\succeq0.
\]
Consequently it preserves PSD and PD. A singleton finite-sum bound against `tsum`, or splitting off the zeroth term and proving the remaining `tsum` nonnegative, gives the required inequality.

Under orthogonal conjugation, you obtain **both**
\[
\operatorname{lyapunovVia}(U,a,N)\succeq0,
\qquad
\operatorname{lyapunovVia}(U,a,N)\succeq N
\]
when \(N\succeq0\), and PD when \(N\succ0\).

Finally,
\[
2hI\succ0,\qquad h^2t^2C\succeq0
\]
for \(h>0\), \(C\succeq0\), with no sign assumption on \(t\). Thus the minibatch covariance is PD.

The fixed-point equation alone is circular as a positivity proof. A Schur-product proof using the PSD kernel \(1/(1-a_i a_j)\) is mathematically elegant, but proving that kernel PSD essentially recovers the series argument. **I would use the scalar quadratic-form series rather than develop matrix-valued infinite sums.**

### B: correct, with the statistic’s normalization made explicit

For \(Q(u)=\frac12u^\top Hu\),
\[
\operatorname{Var}(Q)
=\frac12\sum_{i,j}\lambda_i\lambda_j\widehat\Sigma_{ij}^{\,2}
+\sum_{i,j}\lambda_i\lambda_j\widehat m_i\widehat m_j
 \widehat\Sigma_{ij}.
\]
Here symmetry of \(\widehat\Sigma\) turns
\(\widehat\Sigma_{ij}\widehat\Sigma_{ji}\) into a square.

If the LLC statistic is instead \(tQ\), as your mean formula suggests, **multiply the entire variance formula by \(t^2\)**.

### C: the exact excess formula is correct

Write \(s_i=\sigma_i^2\), so \(\widehat\Sigma_0=\operatorname{diag}(s)\) and \(\widehat\Sigma_{\rm mb}=\widehat\Sigma_0+E\). For the same mean \(m\),
\[
\Delta\operatorname{Var}(Q)
=\sum_i\lambda_i^2s_iE_{ii}
+\frac12\sum_{i,j}\lambda_i\lambda_jE_{ij}^2
+\sum_{i,j}\lambda_i\lambda_j\widehat m_i\widehat m_jE_{ij}.
\]
The stated identity
\[
\sum_i\lambda_i^2s_iE_{ii}
=\frac{ht^2}{2}\sum_i\lambda_i^2s_i^2\widehat C_{ii}
\]
is correct under your established denominator relation. Linearity also gives
\[
\Sigma_{\rm mb}-\Sigma_{\rm ULA}
=\operatorname{lyapunovVia}(U,\rho,h^2t^2C)\succeq0.
\]

## 2. The first-order interpretation: two important corrections

Put
\[
\alpha_i=\frac{ht^2}{2}\widehat C_{ii},
\qquad
\widehat\Sigma_{{\rm mb},ii}=s_i(1+\alpha_i).
\]

For the **centered** law:

- The mode’s mean contribution scales by \(1+\alpha_i\).
- Its diagonal variance contribution scales by
  \[
  (1+\alpha_i)^2=1+2\alpha_i+O(\alpha_i^2).
  \]

Thus **the variance does not have the same first-order relative inflation factor as the mean: it has twice the relative increment**. Its per-mode standard deviation has the same factor \(1+\alpha_i\), but that is a different claim.

Also, “off-diagonal noise enters only at second order” is true for the **centered variance**, not generally for \(m\ne0\). The noncentral term contains
\[
\sum_{i,j}\lambda_i\lambda_j\widehat m_i\widehat m_jE_{ij},
\]
which includes off-diagonal entries at first order.

A precise statement worth including is:

> For a centered stationary Gaussian, minibatch noise increases the marginal variance of the quadratic LLC statistic. Its first-order correction depends only on the frame-diagonal noise covariance and has twice the per-mode relative increment of the mean; off-diagonal noise contributes only quadratically. For a nonzero mean, off-diagonal noise can contribute linearly.

Here “first order” should mean replacing \(C\) by \(\varepsilon C\) at fixed \(h,t,\rho\). It is not automatically an asymptotic statement in \(h\), because the Lyapunov denominator also depends on \(h\).

**Do not append “and hence long-run variance / needed steps” without a temporal argument.** Marginal variance does not determine integrated autocovariance. Even if long-run monotonicity holds for your fixed-transition additive-noise setup, prove it using that setup or the tide-102–103 lag formulas; the same inflation factor does not follow from B–C.

## 3. Lean pitfalls and recommended lemma structure

### Positivity characterizations

Yes: use `posDef_iff_dotProduct_mulVec` and `posSemidef_iff_dotProduct_mulVec` to keep the main proofs in ordinary finite vectors. Account explicitly for the Hermitian component of those characterizations; positivity inequalities alone should not leave it implicit.

A useful order is:

1. `diagLyapunov_isHermitian`;
2. geometric summability and quadratic-form series;
3. `diagLyapunov_sub_posSemidef`;
4. PSD and PD preservation;
5. conjugation transport;
6. `minibatchNoise_posDef`;
7. stationary minibatch covariance PD.

For symmetry, entrywise reduction suffices:
\[
N_{ji}=N_{ij},\qquad 1-a_ja_i=1-a_ia_j.
\]
No denominator nonzero proof is needed merely to establish symmetry.

### Conjugation orientation

Watch the orientation of `conjTranspose_mul_mul_same`: a theorem for
\[
B^\ast M B
\]
must be applied with \(B=U^\top\) to obtain \(UMU^\top\). Its injectivity requirement is therefore on \((U^\top).\mathrm{mulVec}\).

Directly, \(UU^\top=I\) proves that injectivity. Conversely, \(U^\top U=I\) directly proves injectivity of \(U.\mathrm{mulVec}\). Square finite-dimensional orthogonality supplies both identities, but the orientation matters in Lean.

A manual quadratic-form transport proof can be easier than adapting a bundled conjugation theorem:
\[
x^\top UMU^\top x=(U^\top x)^\top M(U^\top x).
\]

### Noise positivity

Use PSD scalar multiplication with `sq_nonneg` for \(h^2t^2\), and combine \(2hI\succ0\) with the PSD noise term. If the local `smul`/addition APIs become awkward, the characterization yields the short proof
\[
x^\top Nx
=2h\sum_i x_i^2+h^2t^2\,x^\top Cx>0
\quad(x\ne0).
\]

### Infinite sums

Your `Summable.tsum_finsetSum` approach is sound. The practical checklist is:

- Express the series over `ℕ`, with \(r=0\) included.
- Keep each scalar geometric sequence’s `Summable` proof available.
- Use finite-sum summability before exchanging sums.
- Explicitly normalize \((a_i a_j)^r=a_i^ra_j^r\).
- Prove the zeroth summand equals \(x^\top Nx\) separately.
- Use nonnegativity only for the **whole quadratic-form summand**; individual entrywise summands can be negative.

Treat the suggested API names as a proof plan and check their exact argument order in your Mathlib checkout.

## 4. Cheap additions and D

**The original-coordinate bound \(\Sigma_{\rm mb}\succeq N_{\rm mb}\) is indeed correct.** Once PSD is known, the fixed-point equation proves it cheaply:
\[
\Sigma_{\rm mb}-N_{\rm mb}=A\Sigma_{\rm mb}A^\top\succeq0.
\]
For \(H\succeq0\), this implies
\[
\operatorname{tr}(H\Sigma_{\rm mb})\ge\operatorname{tr}(HN_{\rm mb}).
\]
The assumption \(H\succeq0\) is essential for this general trace comparison.

I would prioritize **D over this trace bound**, because it directly supports the variance-inflation claim. It actually holds for every symmetric \(H\), not just PSD \(H\). If \(\Sigma_0,E\succeq0\), then
\[
\Delta\operatorname{Var}(Q)
=\operatorname{tr}(H\Sigma_0HE)
+\frac12\operatorname{tr}(HEHE)
+(Hm)^\top E(Hm)\ge0.
\]
Indeed:

- \(H\Sigma_0H\succeq0\), so its trace product with \(E\) is nonnegative;
- \(HEH\succeq0\), so \(\operatorname{tr}(HEHE)\ge0\);
- the last term is a PSD quadratic form.

Thus one reusable lemma, **nonnegativity of the trace product of two PSD matrices**, plus congruence positivity proves D without assuming \(\lambda_i\ge0\). For centered \(H\succeq0\), the frame expansion is an even cheaper specialized route.

**Vote: ship A+B+C with the factor-of-two and noncentral caveats corrected; add covariance order and D if the PSD trace-product lemma is inexpensive; defer long-run claims to a separate temporal proof.**