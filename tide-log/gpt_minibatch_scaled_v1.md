## 1. Correctness of A–D

**Yes, under the standing assumptions** \(\eta>0\), \(\lambda_i>0\), \(0<\eta\lambda_i<2\), and a finite-dimensional fixed eigenframe. For the covariance interpretation and D’s comparison, assume the noise covariance is positive semidefinite.

Write
\[
r_i=1-\eta\lambda_i,\qquad
d_{ij}=1-r_ir_j,\qquad
D_{ij}=\lambda_i+\lambda_j-\eta\lambda_i\lambda_j.
\]
Then \(|r_i|<1\), so
\[
d_{ij}>0,\qquad d_{ij}=\eta D_{ij}.
\]
Thus all your limiting denominators are correct and strictly positive.

### A. Anchored transcription

Correct, on the admissible/stable parameter range, with
\[
\rho_i(t)=1-\eta\lambda_i-\frac{\eta g}{t},
\qquad
\widehat m_i(t)=\frac{g\widehat w_i}{t\lambda_i+g}.
\]
For a theorem about a totalized long-run-variance definition, retain the distinction between the closed form and its **eventual equality** with the actual quantity.

### B. Fixed covariance

Correct:
\[
\widehat S_{ij}(t)\longrightarrow
S^\infty_{ij}:=\frac{\eta^2\widehat C_{ij}}{d_{ij}}
=\frac{\eta\widehat C_{ij}}{D_{ij}}.
\]
Since \(\widehat m_i(t)\to0\) and the limiting IAT factors are finite, the unscaled mean contribution tends to zero. Consequently,
\[
\tau^2_{\rm mb}(t)\longrightarrow
L_\infty
=\frac12\sum_{ij}\lambda_i\lambda_j
(S^\infty_{ij})^2
\frac{1+r_j^2}{1-r_j^2}.
\]

Moreover,
\[
L_\infty>0\iff \widehat C\ne0,
\]
because every coefficient multiplying \(\widehat C_{ij}^{\,2}\) is strictly positive. This algebraic equivalence does **not** require PSD.

Hence, for nonzero fixed covariance,
\[
t^2\tau^2_{\rm mb}(t)\longrightarrow+\infty,
\qquad
t^2\tau^2_{\rm mb}(t)\sim L_\infty t^2.
\]

**Qualification:** the mean contribution vanishes *unscaled* in B. Its \(t^2\)-scaled version need not vanish; it can have a finite nonzero limit. That does not affect the leading \(L_\infty t^2\) asymptotic.

### C. Linear batch growth

Correct. If \(\widehat C_t=\widehat C_0/t\), then
\[
t\widehat S_{ij}(t)\longrightarrow
A_{ij}:=\frac{2\eta\delta_{ij}+\eta^2\widehat C_{0,ij}}{d_{ij}},
\qquad
t\widehat m_i(t)\longrightarrow\frac{g\widehat w_i}{\lambda_i}.
\]
Also \(\widehat S_{ij}(t)\to0\). The scaled mean summand factors as
\[
(t\widehat m_i)(t\widehat m_j)\widehat S_{ij}
\frac{1+\rho_j}{1-\rho_j},
\]
and therefore tends to zero. Thus your \(L_{\rm lin}\) is exactly right.

### D. Baseline and comparison

Correct. At \(C_0=0\), only diagonal entries survive, and
\[
A_{ii}=\frac{1}{\lambda_i(1-\eta\lambda_i/2)}.
\]
This gives precisely
\[
L_{\rm lin}(0)
=\sum_i\frac{1+r_i^2}
{4\eta\lambda_i(1-\eta\lambda_i/2)^3}
=L_\eta.
\]

For PSD \(\widehat C_0\), diagonal entries are nonnegative, so the diagonal squares cannot decrease; off-diagonal terms are nonnegative additions. In fact,
\[
\boxed{\widehat C_0\succeq0,\quad \widehat C_0\ne0
\implies L_{\rm lin}(\widehat C_0)>L_\eta.}
\]
A nonzero PSD matrix has a positive diagonal entry.

## 2. Suggested E8+E5 wording and meaning of \(L_\infty\)

I would phrase the result as:

> At fixed stable scaled step \(\eta\), a nonzero, \(t\)-independent gradient-noise covariance gives the scaled statistic an asymptotic variance coefficient
> \[
> t^2\tau^2_{\rm mb}(t)\sim L_\infty t^2.
> \]
> Thus its stationary chain average has large-\(n\) Monte Carlo variance approximately \(L_\infty t^2/n\), requiring \(n=\Theta(t^2)\) to maintain fixed precision. If batch growth makes \(C_t=C_0/t\), the coefficient instead converges to \(L_{\rm lin}(C_0)\ge L_\eta\). For PSD \(C_0\), equality holds exactly when \(C_0=0\), and the exact-gradient coefficient is recovered as \(C_0\to0\).

Two qualifications are worth retaining:

* **Long-run variance is a large-\(n\) coefficient**, not an exact finite-\(n\) variance. The limit in \(t\) alone does not prove a simultaneous \((t,n(t))\) variance theorem; that requires finite-\(n\) remainder control. The fixed stable limiting contractions make such control plausible here.
* “Linear batch growth” presumes covariance really scales inversely with batch size. Also distinguish **chain iterations** from **gradient evaluations**: with batch size \(\Theta(t)\), the gradient-evaluation budget is batch size times iteration count.

### \(L_\infty\) has a natural standalone interpretation

Let \(R=\operatorname{diag}(r_i)\). Then \(S^\infty\) is the unique solution of the discrete Lyapunov equation
\[
S^\infty=RS^\infty R^\top+\eta^2\widehat C.
\]
Thus \(L_\infty\) is the quadratic-observable long-run variance associated with the limiting noise-driven linear chain. It measures the stationary noise floor left when the injected thermal noise vanishes.

Your proposed factorization is correct with
\[
w_j(\eta):=\frac{1+r_j^2}{\lambda_j(2-\eta\lambda_j)}:
\qquad
L_\infty=\frac{\eta}{2}\sum_{ij}
\frac{\lambda_i\lambda_j\widehat C_{ij}^{\,2}w_j(\eta)}
{D_{ij}^{\,2}}.
\]
Call this **\(\eta\) times an \(\eta\)-dependent Lyapunov-type quadratic functional**—not \(\eta\) times a step-independent functional.

## 3. Lean route and pitfalls

Your route is sound. The main improvement is to **normalize by \(t\) before applying limit lemmas**, rather than asking Lean to simplify divergent numerator and denominator expressions.

Set \(u(t)=1/t\). Eventually \(t\ne0\), and:
\[
\rho_i(t)=r_i-\eta g\,u(t),\qquad
\widehat m_i(t)=
\frac{g\widehat w_i\,u(t)}{\lambda_i+g\,u(t)},\qquad
t\widehat m_i(t)=
\frac{g\widehat w_i}{\lambda_i+g\,u(t)}.
\]
For fixed covariance,
\[
\widehat S_{ij}(t)=
\frac{2\eta\delta_{ij}u(t)+\eta^2\widehat C_{ij}}
{1-\rho_i(t)\rho_j(t)}.
\]
For linear scaling,
\[
t\widehat S_{ij}(t)=
\frac{2\eta\delta_{ij}+\eta^2\widehat C_{0,ij}}
{1-\rho_i(t)\rho_j(t)}.
\]
These are direct finite-limit calculations.

Recommended proof structure:

1. **Prove reusable denominator positivity**
   \[
   0<1-r_ir_j,\quad 0<1-r_j,\quad 0<1-r_j^2.
   \]
   Derive the nonzero facts for `Tendsto.div` from these. Avoid proving nonzeroness through the expanded polynomial.

2. **Separate entry limits from finite-sum assembly.**  
   Prove limits for \(\rho\), both IAT factors, \(m\), \(tm\), \(S\), and \(tS\); then use nested finite-sum limit lemmas.

3. **Prove the scaled algebraic identity first.**  
   Rewrite the \(t^2\)-scaled closed form using
   \[
   t^2S_{ij}^2=(tS_{ij})^2,\qquad
   t^2m_im_jS_{ij}=(tm_i)(tm_j)S_{ij}.
   \]
   Let `ring` handle these polynomial identities. Keep denominator cancellation in separate eventual-equality lemmas.

4. **Transfer to the actual LRV last.**  
   Use eventual positivity/stability/admissibility and `Tendsto.congr'`. For \(C_0/t\), PSD needs \(t>0\), which is only eventual on the real `atTop` domain.

5. **For divergence, use an eventual lower bound if library lookup gets awkward.**  
   From \(\tau^2(t)\to L_\infty>0\), obtain eventually
   \[
   \tau^2(t)\ge L_\infty/2.
   \]
   Compare \(t^2\tau^2(t)\) against \((L_\infty/2)t^2\to+\infty\). This avoids dependence on a particular mixed finite/infinite product lemma.

Other pitfalls:

* Derive positivity of \(\lambda_i\) using the separately stated \(\eta>0\); \(0<\eta\lambda_i<2\) alone is insufficient.
* For diagonal collapse, split on \(i=j\) explicitly; do not expect a large `simp` invocation to discover the intended sum reduction.
* Prove \(L_\infty>0\iff C\ne0\) entrywise, then bridge matrix nonzeroness with extensionality.
* Use the existing frame/entry simp set for A, but keep spectral-frame conversion separate from asymptotic algebra.

## 4. Cheap additions: priorities

**Highest value:**

1. **\(L_\infty>0\iff \widehat C\ne0\).**  
   This supplies the precise hypothesis for divergence and the \(\Theta(t^2)\) claim.

2. **Strictness in D**, if the PSD diagonal lemma is readily available:
   \[
   L_{\rm lin}(C_0)=L_\eta\iff C_0=0
   \quad(C_0\succeq0).
   \]

3. **A general scaled-covariance limit lemma**, rather than several power-law cases. If entrywise
   \[
   t\widehat C_t\longrightarrow B,
   \]
   then the same argument gives
   \[
   t\widehat S_{ij}(t)\longrightarrow
   \frac{2\eta\delta_{ij}+\eta^2B_{ij}}{d_{ij}},
   \qquad
   t^2\tau^2_{\rm mb}(t)\longrightarrow L_{\rm lin}(B),
   \]
   assuming eventual admissibility. Indeed, the normalized numerator is simply
   \(2\eta\delta_{ij}+\eta^2t\widehat C_{t,ij}\).

This single lemma covers linear scaling and all superlinear scalings satisfying \(tC_t\to0\). In particular, \(C_t=C_0/t^2\) recovers \(L_\eta\) with no real-power infrastructure. Merely \(C_t=O(1/t)\) supports boundedness, not a unique limiting constant without a convergence hypothesis.

The explicit \(\eta/2\) factorization is useful exposition, but lower priority as a formal theorem.

**Vote: land A–D plus \(L_\infty>0\iff C\ne0\); organize C around \(tC_t\to B\), take \(C_0/t^2\) as the cheap exact-gradient corollary, and defer real-power scaling.**