## 1. Mathematical check: A–C are correct, with two wording qualifications

Write
\[
p_i>0,\qquad \rho_i=1-hp_i,\qquad
a_i=1-\frac{hp_i}{2},\qquad f_i(k)=1-\rho_i^{2k}.
\]
Assume \(h>0\) and \(hp_i<2\). Then
\[
0<hp_i<2,\quad -1<\rho_i<1,\quad a_i>0.
\]
For every \(k\ge1\), \(f_i(k)>0\). Consequently,
\[
\Sigma_k
 =U\operatorname{diag}\!\left(\frac{f_i(k)}{p_i a_i}\right)U^\top,
\qquad
Q_k=\Sigma_k^{-1}
 =U\operatorname{diag}\!\left(\frac{p_i a_i}{f_i(k)}\right)U^\top
\]
are positive definite.

**Overshooting is entirely fine.** When \(1<hp_i<2\), \(\rho_i<0\), but the covariance involves \(\rho_i^{2k}=(\rho_i^2)^k\). The alternating sign affects the mean from a nonzero start, not these zero-start covariance formulas.

For the statistic \(X=\frac12u^\top P u\), where \(P=tH\), the transform is
\[
L_k(s)
=\mathbb E[e^{-sX}]
=\prod_i\left(\frac{q_i(k)}{q_i(k)+sp_i}\right)^{1/2}
=\prod_i\left(1+s\frac{f_i(k)}{a_i}\right)^{-1/2},
\qquad s\ge0.
\]
The sign is correct: this is a **Laplace transform**, with exponent \(-sX\), not an MGF.

In eigen-coordinates the Gaussian coordinates are independent, and
\[
\frac{p_i}{2}u_i^2
\sim \operatorname{Gamma}\!\left(\text{shape } \frac12,\ 
\text{rate } \frac{a_i}{f_i(k)}\right).
\]
Thus B is correct, including its rate convention.

The trace/mean identity is
\[
\frac12\operatorname{tr}(P\Sigma_k)
=\frac12\sum_i\frac{f_i(k)}{a_i},
\]
and the stationary-minus-finite-time mean is
\[
B_k
=\frac12\sum_i\frac{\rho_i^{2k}}{a_i}\ge0.
\]

Two qualifications:

* **“Gamma law” means a sum of Gamma variables**, generally with different rates—not generally a single Gamma distribution.
* The rates **decrease to** \(a_i\), but do not literally “decay geometrically.” Their excess is
  \[
  \frac{a_i}{1-\rho_i^{2k}}-a_i
  =\frac{a_i\rho_i^{2k}}{1-\rho_i^{2k}}.
  \]
  The covariance deficit and mean bias have exact geometric factors; the rate excess is asymptotically geometric. If \(\rho_i=0\), that coordinate is already stationary after one step.

C follows: \(f_i(k)\) is nondecreasing and tends to \(1\); therefore \(L_k(s)\) is nonincreasing and tends to the stationary transform. Use **non-strict** monotonicity, including \(s=0\) and \(\rho_i=0\).

## 2. Recommended interface and Lean route

**Expose the covariance as the trajectory object; prove an explicit precision bridge; use the precision for the transform theorem.** This matches both existing interfaces without forcing either to impersonate the other.

A useful theorem sequence is:

1. Identify the existing trajectory covariance with
   \[
   \Sigma_k=S(1-A^{2k}).
   \]
2. Prove its spectral formula.
3. For \(k\ge1\), prove positivity of its diagonal entries.
4. Prove its explicit inverse formula.
5. Apply `tiltedExpectation_exp_quadForm` to that inverse.

This gives a public transform statement involving `Σ_k⁻¹`, with the named spectral precision available internally or as a convenience definition. It also leaves a clean attachment point for the `multivariateGaussian` trajectory theorem.

### Algebraic route

Your orthogonal-conjugation lemmas are the right small reusable API:
\[
(UDU^\top)^n=UD^nU^\top,
\]
\[
(UD_1U^\top)(UD_2U^\top)=UD_1D_2U^\top,
\]
\[
1-UDU^\top=U(1-D)U^\top.
\]
The power lemma at \(n=0\) needs \(UU^\top=1\), so make sure the available orthogonality API supplies both orientations.

For the inverse, **the explicit left-inverse proof is a good route**, not a workaround to avoid:
\[
\bigl(U\operatorname{diag}(d_i^{-1})U^\top\bigr)
\bigl(U\operatorname{diag}(d_i)U^\top\bigr)=1.
\]
Then apply `Matrix.inv_eq_left_inv` in its required orientation. This needs only \(d_i\ne0\), which positivity supplies. A general inverse-of-conjugation theorem may shorten the final expression, but usually shifts the work into invertibility side conditions. I would not spend this tide searching for it.

For scalar positivity, organize the argument around
\[
0\le\rho_i^2<1,\qquad \rho_i^{2k}=(\rho_i^2)^k.
\]
That is cleaner than carrying negative-base power inequalities through the proof.

For determinant simplification, first establish the scalar identity
\[
\frac{q_i(k)}{q_i(k)+sp_i}
=\frac{1}{1+s f_i(k)/a_i},
\]
with positivity/nonzero facts already available. Then pass through determinant products and square roots. This avoids mixing matrix algebra, division, and square-root normalization in one goal.

**Keep \(k=0\) separate.** Lean’s total matrix inverse does not turn the singular zero covariance into a meaningful Gaussian precision. The zero-step transform is \(1\) because the law is \(\delta_0\), not by applying the positive-definite precision theorem at zero.

Finally, if the Gaussian-measure/tilted-expectation bridge is not proved, the checked conclusion is a transform under the tilted density with the trajectory precision—not yet a checked statement about the Markov-chain law itself.

## 3. Nearby additions: what is worth doing?

### First priority: a quantitative transform bound

The proposed logarithmic threshold needs a prefactor depending on \(s\), dimension, and the stationary variances.

Couple the scalar quadratic statistics using independent standard normals:
\[
X_k=\frac12\sum_i\frac{f_i(k)}{a_i}Z_i^2,
\qquad
X_\infty=\frac12\sum_i\frac1{a_i}Z_i^2.
\]
Since \(X_k\le X_\infty\) and \(x\mapsto e^{-sx}\) is \(s\)-Lipschitz on \([0,\infty)\),
\[
0\le L_k(s)-L_\infty(s)\le s B_k.
\]
This is also provable directly from the finite products, without formalizing the coupling.

Given a uniform bound \(|\rho_i|\le r<1\),
\[
B_k\le M_\infty r^{2k},
\qquad
M_\infty=\frac12\sum_i\frac1{a_i},
\]
so
\[
\boxed{0\le L_k(s)-L_\infty(s)
       \le sM_\infty r^{2k}.}
\]
For \(0<r<1\) and \(sM_\infty>\varepsilon>0\), a sufficient condition is
\[
k\ge
\frac{\log(sM_\infty/\varepsilon)}{-2\log r},
\]
rounded up to an integer. Handle \(s=0\) and \(r=0\) separately.

The geometric bound is more valuable than formalizing the logarithmic rearrangement. Also, this is a **pointwise-in-\(s\)** transform bound, not a total-variation or full chain-mixing bound.

### Localised burn-in: cheap if the theorem separates target and statistic

For localised precision eigenvalues
\[
\ell_i=p_i+\gamma,\qquad p_i=t\lambda_i,
\]
set
\[
a_i^\gamma=1-\frac{h\ell_i}{2},\qquad
f_i^\gamma(k)=1-(1-h\ell_i)^{2k}.
\]
The LLC statistic still uses \(p_i\), not \(\ell_i\). Hence
\[
L_k^\gamma(s)
=\prod_i\left(
1+s\frac{p_i f_i^\gamma(k)}{\ell_i a_i^\gamma}
\right)^{-1/2}.
\]
For \(p_i>0\), the corresponding rates are
\[
\frac{\ell_i a_i^\gamma}{p_i f_i^\gamma(k)}.
\]
This is a worthwhile corollary if the main theorem already allows a statistic diagonal in the same eigenbasis. Otherwise, defer it rather than duplicate substantial proof machinery.

### Nonzero start: correct, but defer

For deterministic start \(w_0\),
\[
m_k=A^kw_0,\qquad
\widehat m_{k,i}=\rho_i^k(U^\top w_0)_i,
\]
with the same covariance eigenvalues \(v_i(k)=f_i(k)/(p_i a_i)\). The transform becomes
\[
L_{k,w_0}(s)
=L_k(s)\exp\!\left(
-\frac{s}{2}\sum_i
\frac{p_i\widehat m_{k,i}^{\,2}}{1+sp_iv_i(k)}
\right).
\]
Call this a sum of **scaled noncentral chi-square variables**; “noncentral Gamma” is less unambiguous. This extension is useful, but completing the square and connecting nonzero means is a separate bundle.

One useful sanity check for the present tide is
\[
\Sigma_1=2hI,\qquad
L_1(s)=\prod_i(1+2hsp_i)^{-1/2}.
\]
Also, instability does not invalidate finite-time Gaussian formulas: the universally valid covariance eigenvalues are
\[
2h\sum_{j=0}^{k-1}\rho_i^{2j}.
\]
Stability is needed here for the stationary-covariance representation and stationary-limit claims, not for finite-time existence.

## 4. Wording against E4/E3

I would use:

> For an exactly quadratic Gaussian target, ULA initialized at the mode has, after \(k\ge1\) updates, an LLC statistic distributed as a sum of independent shape-\(1/2\) Gamma variables. Their rates decrease to the stationary ULA rates. The finite-time mean lies below the stationary ULA mean by exactly
> \[
> \frac12\sum_i\frac{\rho_i^{2k}}{1-hp_i/2}.
> \]

Then state these qualifications:

* **Index updates explicitly.** If E4’s first retained state follows \(b+1\) updates, its factor is \(\rho_i^{2(b+1)}\). That is \(k=b+1\), not a different burn-in formula.
* **Distinguish transient bias from discretization bias.** The displayed deficit is relative to stationary ULA, not relative to the Gibbs mean \(d/2\). Indeed,
  \[
  \mathbb E[X_k]-\frac d2
  =\frac12\sum_i(a_i^{-1}-1)-B_k.
  \]
  Early transient bias can cancel stationary discretization bias.
* **This is a marginal law, not a pooled-estimator law.** States at different times are correlated. Their pooled average is not covered by the independent-Gamma statement.
* **Scope “exact” correctly.** The result is exact for the quadratic model and exact ULA recursion. A local quadratic approximation to a nonlinear target remains an approximation.
* **Disclose the formal bridge boundary.** If only the tilted-expectation identity and trajectory covariance are checked, do not describe the entire chain-law Gamma identification as machine-checked.

## Vote

**Vote for one bundle: A + B + C, zero-start only, with the explicit covariance–precision bridge and the trace bias formula.** Prioritize monotonicity and the stationary limit; add the geometric mean-bias/transform bound if proof budget permits. Defer nonzero starts, pooled estimators, and logarithmic burn-in thresholds. Include localisation only as a genuinely cheap shared-eigenbasis corollary.