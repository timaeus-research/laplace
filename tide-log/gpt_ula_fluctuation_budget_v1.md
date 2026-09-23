## 1. A–D: correct, with stability and nondegeneracy qualifications

Write
\[
s_i:=\frac1{p_i\kappa_i},\qquad
v_{i,k}=s_i(1-\rho_i^{2k}),\qquad
\mu_{i,k}=b_i+\rho_i^k(z_i-b_i).
\]
Assume \(H=U\operatorname{diag}(\lambda_i)U^\top\), \(p_i>0\), and
\[
h>0,\qquad hp_i<2.
\]
Then \(|\rho_i|<1\) and \(\kappa_i>0\).

**A and B are correct.** For a Gaussian with mean \(m_k\) and covariance \(\Sigma_k\),
\[
\operatorname{Var}\!\left(\frac12u^\top Hu\right)
=\frac12\operatorname{tr}(H\Sigma_kH\Sigma_k)
 +(Hm_k)^\top\Sigma_k(Hm_k).
\]
In the shared frame,
\[
\operatorname{tr}(H\Sigma_kH\Sigma_k)=\sum_i(\lambda_i v_{i,k})^2,
\quad
(Hm_k)^\top\Sigma_k(Hm_k)
=\sum_i v_{i,k}\lambda_i^2\mu_{i,k}^2.
\]
Consequently, for \(Y_k=t\,u^\top Hu/2\),
\[
\boxed{\operatorname{Var}(Y_k)
=\frac{t^2}{2}\sum_i(\lambda_i v_{i,k})^2
+t^2\sum_i v_{i,k}\lambda_i^2\mu_{i,k}^2.}
\]
Substituting \(b_i=a_i/p_i\) gives B.

**C is correct**, taking \(k\to\infty\) at fixed \(t,h\):
\[
S_{t,h}:=\lim_k\mathbb E Y_k
=\frac t2\sum_i\frac{\lambda_i}{p_i\kappa_i}
+\frac t2\sum_i\lambda_i b_i^2,
\]
\[
\boxed{V_{t,h}:=\lim_k\operatorname{Var}(Y_k)
=\frac{t^2}{2}\sum_i\frac{\lambda_i^2}{p_i^2\kappa_i^2}
+t^2\sum_i\frac{\lambda_i^2b_i^2}{p_i\kappa_i}.}
\]
Every transient term in the stated burn-in budget vanishes.

**D has the correct signs.** With \(\ell_t=t\langle L\circ A\rangle_{\rm loc}\) and
\[
D_{t,h}:=\frac{th}{4}\sum_i\frac{\lambda_i}{\kappa_i},
\]
the statement is
\[
\left|\ell_t-S_{t,h}-\frac{C_1'}t+D_{t,h}\right|
\le \frac K{t^2}.
\]
Equivalently,
\[
S_{t,h}-\ell_t=D_{t,h}-\frac{C_1'}t+O(t^{-2}).
\]
“Exceeds” describes the signed expansion; it is not an unconditional finite-\(t\) inequality.

Two corrections to the commentary:

* **Stationary variance is independent of \(x_0\).** Its second term is an anchor/noncentrality contribution, not a start-dependent contribution.
* **Variance need not increase monotonically with \(k\).** A distant deterministic start can produce a large transient noncentrality contribution and overshoot stationary variance.

## 2. Fixed-\(\eta\) limits and statistical interpretation

Assume here that \(g,a_i,\lambda_i\) are fixed, \(\lambda_i>0\), and
\[
h=\frac{\eta}{t},\qquad 0<\eta<\frac2{\lambda_{\max}}.
\]
Set \(c_i=1-\eta\lambda_i/2>0\). Then
\[
p_i=t\lambda_i+g,\qquad
\kappa_i=c_i-\frac{\eta g}{2t}.
\]

The two stationary variance pieces satisfy
\[
\boxed{
\frac{t^2}{2}\sum_i\frac{\lambda_i^2}{p_i^2\kappa_i^2}
\longrightarrow \frac12\sum_i c_i^{-2},
}
\]
and
\[
\boxed{
t^2\sum_i\frac{\lambda_i^2b_i^2}{p_i\kappa_i}
=t^2\sum_i\frac{\lambda_i^2a_i^2}{p_i^3\kappa_i}
=\frac1t\sum_i\frac{a_i^2}{\lambda_i c_i}+O(t^{-2})
\longrightarrow0.
}
\]
Thus the proposed nonzero limit for the second piece loses a factor \(1/t\). In particular,
\[
\boxed{V_{t,\eta/t}=\frac12\sum_i c_i^{-2}+O(t^{-1}).}
\]

These conclusions require fixed \(a_i\). For example, \(a_i\) of order \(\sqrt t\) can produce a nonzero limiting noncentrality contribution. If \(H\) is merely positive semidefinite, sum over \(\lambda_i>0\); zero modes contribute nothing to this statistic, and the baseline is \(\operatorname{rank}(H)/2\), not \(d/2\).

### What one stationary sample says

In fact, under the fixed-parameter assumptions,
\[
Y_\infty\ \xrightarrow[t\to\infty]{\rm law}\
\frac12\sum_i\frac{Z_i^2}{c_i},
\qquad Z_i\stackrel{\rm iid}{\sim}N(0,1).
\]
Hence a single sample has order-one fluctuation:
\[
\operatorname{sd}(Y_\infty)\longrightarrow
\sqrt{\frac12\sum_i c_i^{-2}}.
\]
For small \(\eta\), this is approximately \(\sqrt{d/2}\). Increasing \(t\) does **not** concentrate one scaled observation.

Meanwhile,
\[
D_{t,\eta/t}\longrightarrow
\frac{\eta}{4}\sum_i\frac{\lambda_i}{c_i}
=\frac12\sum_i(c_i^{-1}-1).
\]
The contrast is therefore:

* sampling fluctuation: \(O(1)\);
* fixed-\(\eta\) ULA bias: \(O(1)\);
* anharmonic correction: \(C_1'/t\);
* remaining analytic error: \(O(t^{-2})\).

### Suggested wording on samples and steps

> Resolving a nonzero \(C_1'/t\) correction by ordinary averaging requires order \(t^2\) effectively independent observations for fixed signal-to-noise ratio, after controlling discretisation bias and burn-in. Consistently separating that correction from Monte Carlo noise requires \(M_{\rm eff}/t^2\to\infty\).

More explicitly, standard error at most \(\alpha |C_1'|/t\) requires
\[
M_{\rm eff}\gtrsim
\frac{V_{t,h}t^2}{\alpha^2(C_1')^2}.
\]
For a single chain, translate effective observations into steps using autocorrelation; do not substitute the raw number of steps.

At fixed stable \(\eta\), with positive eigenvalues bounded away from zero and stability boundaries, the relevant correlation times remain bounded as \(t\to\infty\). Thus ordinary averaging takes order \(t^2\) steps, plus burn-in. For bounded fixed starts, order \(\log t\) burn-in suffices to reduce the quadratic-expectation transient to order \(1/t\).

**Bias must be addressed first.** Either subtract the exact \(D_{t,h}\), or make it sufficiently small. Without correction,
\[
D_{t,h}\sim \frac{th}{4}\operatorname{tr}H
\]
in the small-step regime, so making it \(o(t^{-1})\) requires \(h=o(t^{-2})\). At the benchmark \(h\asymp t^{-2}\), correlation times are order \(t\), and the ordinary-averaging cost becomes order \(t^3\) steps—while discretisation bias is still order \(1/t\).

Finally, Gaussian ULA samples alone do not identify an unknown anharmonic coefficient: that information must come from the nonquadratic model or an analytic calculation. The sample-count statement is a precision budget, not an identification claim.

## 3. Lean route and pitfalls

Your proposed route is sound. I would separate it into deterministic frame algebra, Gaussian variance, and scalar limits.

### A: frame algebra first

Prove reusable lemmas giving
\[
H\Sigma_k=U\operatorname{diag}(\lambda_i v_{i,k})U^\top
\]
and
\[
U^\top(Hm_k)=\operatorname{diag}(\lambda_i)(U^\top m_k).
\]
Then the trace and dot-product calculations should reduce to diagonal simplification.

Specific pitfalls:

1. **Use \(\operatorname{tr}(H\Sigma H\Sigma)\).** Do not silently replace this by an entrywise squared norm without proving the appropriate symmetry identity.
2. **Check the parameters of `tiltedVar_quadForm`.** If it is parameterised by precision and natural tilt, the required inputs are
   \[
   Q_k=\Sigma_k^{-1},\qquad \text{tilt}=Q_km_k,
   \]
   not covariance and mean directly.
3. **Handle \(k=0\) separately if precision must be positive definite.** Here \(\Sigma_0=0\), the law is Dirac, and variance is zero. For \(k\ge1\), stability and \(h>0\) give \(v_{i,k}>0\).
4. **Apply scalar variance scaling explicitly.** Passing from \(u^\top Hu\) to half that statistic introduces \(1/4\); passing to \(tX\) introduces \(t^2\).
5. **Keep integrability attached to the probabilistic wrapper.** The frame lemmas should be pure matrix identities; Gaussian moment facts discharge the variance theorem’s analytic hypotheses.

### C: scalar convergence, then finite sums

Using `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` is the right route. Obtain
\[
\rho_i^k\to0,\qquad \rho_i^{2k}=(\rho_i^k)^2\to0,
\]
then \(v_{i,k}\to s_i\) and \(\mu_{i,k}\to b_i\). Products, squares, and finite sums finish all three limits.

Rewriting the even power as a square is usually cleaner than managing a subsequence indexed by \(2k\). These are fixed-\(t,h\) limits; joint limits need separate uniform estimates.

### D: direct algebra is cheaper than taking limits

Use tide 95 together with
\[
\frac{t\lambda_i}{2p_i}
-\frac{t\lambda_i}{2p_i\kappa_i}
=-\frac{th\lambda_i}{4\kappa_i}.
\]
Supply \(p_i\ne0\), \(\kappa_i\ne0\); after unfolding \(\kappa_i\), `field_simp` and ring normalisation should close the scalar identity.

This avoids proving that an absolute-value bound is preserved under the \(k\)-limit. It also makes clear that the same \(K\) and threshold from tide 95 survive: the discretisation adjustment is exact.

## 4. Cheap additions

My priority order:

**First: stationary variance asymptotics, at least as limits.**
Prove
\[
V_{t,\eta/t}\to\frac12\sum_i c_i^{-2},
\qquad
t\,V^{\rm noncentral}_{t,\eta/t}
\to\sum_i\frac{a_i^2}{\lambda_i c_i}.
\]
These are finite rational-expression limits. Establish eventual positivity of \(p_i,\kappa_i\) first. The \(O(t^{-1})\) strengthening can follow later.

**Second: an independent-replicate MSE theorem.**
For independent copies \(Y_1,\ldots,Y_M\), \(M\ge1\),
\[
\mathbb E[(\overline Y_M-\mathbb EY)^2]=\frac{V}{M}.
\]
Chebyshev then gives, for \(\varepsilon>0\),
\[
\Pr\!\left(|\overline Y_M-\mathbb EY|\ge\varepsilon\right)
\le\frac{V}{M\varepsilon^2}.
\]
If independence infrastructure is expensive, the MSE theorem alone already supports the sampling-budget note. State it for \(Y=tX\), avoiding ambiguity over the variance scaling.

**Third: stationary autocovariance, initially as a note or later theorem.**
It is explicitly
\[
\boxed{
\operatorname{Cov}(Y_0,Y_\ell)
=\frac{t^2}{2}\sum_i\lambda_i^2s_i^2\rho_i^{2\ell}
+t^2\sum_i\lambda_i^2b_i^2s_i\rho_i^\ell.
}
\]
Thus the long-run variance for time averaging is
\[
\frac{t^2}{2}\sum_i\lambda_i^2s_i^2
 \frac{1+\rho_i^2}{1-\rho_i^2}
+t^2\sum_i\lambda_i^2b_i^2s_i
 \frac{1+\rho_i}{1-\rho_i}.
\]
This directly answers “samples versus steps.” It is less cheap to formalise because it needs joint-time Gaussian moments, so I would not make it a tide-100 blocker.

A useful deterministic bonus is an explicit geometric burn bound. With \(q=\max_i|\rho_i|<1\),
\[
|\mathbb EY_k-S_{t,h}|
\le \frac{|t|}{2}\sum_i|\lambda_i|
\left[s_iq^{2k}+2|b_i(z_i-b_i)|q^k
 +(z_i-b_i)^2q^{2k}\right].
\]
This is stronger operationally than `Burn_k → 0` and needs little probability infrastructure.

## 5. Recommendation

Land A–D, including the \(k=0\) treatment and the stationary-limit interpretation. Add the fixed-\(\eta\) variance limit if scope permits; keep single-chain autocorrelation as a follow-up. Correct the prose about monotonic variance and stationary start dependence before landing.

**Vote: YES on A–D; prioritise the fixed-\(\eta\) limit and explicit burn bound, with independent-chain MSE optional and autocorrelation deferred.**