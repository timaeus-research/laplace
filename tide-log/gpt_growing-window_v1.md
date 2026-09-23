**Vote: approve**, with two wording qualifications: distinguish the MC error of the **scaled LLC estimator** from that of the unscaled average, and state that “bias-dominated” assumes \(b_\eta\ne0\). No coupling between \(n(t)\) and \(t\) is needed.

## 1. Correctness of the growing-window limit

Your argument works under the anchored-model bounds used in the proof plan: eventually, for every mode,
\[
|\rho_i(t)|\le r<1,\qquad
t\sigma_i^2(t)\longrightarrow \frac1{\lambda_i a_i},
\qquad \widehat m_i(t)=O(t^{-1}),
\]
with \(d_i(t)=\widehat x_{0i}-\widehat m_i(t)\) bounded. Finite dimension is understood.

### The sandwich is valid

For \(s\ge k\),
\[
0\le \rho_i^{2s}\le r^{2k},
\qquad
(1-r^{2k})^2\le (1-\rho_i^{2s})^2\le1.
\]
Every coefficient multiplying this factor in the quadratic covariance sum is nonnegative, including the lag factor \(\rho_i^{2\ell}\). Thus, exactly as proposed,
\[
(1-r^{2k})^2Q(t,n)
\le \text{quadratic part of }nt^2\operatorname{avgVar}
\le Q(t,n).
\]
Negative \(\rho_i\) cause no difficulty here.

The exact identity for \(nF_n\), together with \(0\le \rho_i(t)^2\le r^2\), gives the **uniform** estimate
\[
\left|nF_n(\rho_i^2)
-\frac{1+\rho_i^2}{1-\rho_i^2}\right|
\le \frac{2r^2}{n(1-r^2)^2}.
\]
This is the decisive point: the finite-window error is uniformly \(O(1/n)\), not something involving \(n/t\). Consequently, arbitrary \(n(t)\to\infty\) works.

The absolute-value bound on the mean part also works. In particular,
\[
t\bigl(|\widehat m_i|+r^k|d_i|\bigr)^2
\le 2t|\widehat m_i|^2+2tr^{2k}|d_i|^2\longrightarrow0.
\]
Its geometric lag sum is bounded independently of \(n\). This establishes (i).

For (ii), the clean logical formulation is
\[
\sup_{s\ge k(t)}
\left|tE_s q-t\langle L\rangle_{\rm loc}-b_\eta\right|
\longrightarrow0.
\]
Every nonempty window average inherits this bound. **Part (ii) does not even require \(n(t)\to\infty\)**—only eventual positivity of \(n(t)\).

### Identification of \(L_\eta\)

The limiting stationary covariance of the scaled quadratic observable is
\[
\Gamma_\eta(\ell)=\frac12\sum_i a_i^{-2}\alpha_i^{2\ell}.
\]
Therefore its discrete-time long-run variance is
\[
\Gamma_\eta(0)+2\sum_{\ell\ge1}\Gamma_\eta(\ell)
=\frac12\sum_i a_i^{-2}\frac{1+\alpha_i^2}{1-\alpha_i^2}
=\sum_i\frac{1+\alpha_i^2}{4\eta\lambda_i a_i^3}
=L_\eta.
\]
So this is exactly tide 103’s constant **if tide 103 uses this per-iteration, scaled-observable normalization**. A physical-time normalization would introduce an additional time-step factor; the displayed covariance-sum identity removes any ambiguity.

## 2. Cleaner statements, rates, and interpretation

Your sandwich is already a clean route. I would expose a quantitative, uniform-in-window bound as the main lemma.

Under the usual anchored-model estimates
\[
\rho_i(t)-\alpha_i=O(t^{-1}),\qquad
t\sigma_i^2(t)-(\lambda_i a_i)^{-1}=O(t^{-1}),
\]
your proof yields, uniformly over integers \(n\ge1\),
\[
\boxed{
\left|nt^2\operatorname{avgVar}(k(t),n)-L_\eta\right|
\le K\left(\frac1n+\frac1t+tr^{2k(t)}\right).
}
\]
The \(O(t^{-1})\) parameter rates should be cited explicitly; convergence alone gives the qualitative theorem but not this particular rate.

The stated bias bounds likewise give
\[
\boxed{
\sup_{n\ge1}\left|
\frac1n\sum_{a<n}
\bigl(tE_{k(t)+a}q-t\langle L\rangle_{\rm loc}\bigr)-b_\eta
\right|
\le K\left(\frac1t+tr^{2k(t)}\right).
}
\]
For example, the cross term \(r^k\) is absorbed using
\[
2r^k\le t^{-1}+tr^{2k}.
\]
Constants here may depend on the fixed model, \(\eta,r,x_0\), but not on \(n,t\).

### MC error: specify the scaling

Writing \(\bar q\) for the window average,
\[
\operatorname{SD}(\bar q)
\sim \frac{\sqrt{L_\eta}}{t\sqrt n}.
\]
For an LLC estimator whose random component is **\(t\bar q\)**, the corresponding MC standard error is instead
\[
\operatorname{SD}(t\bar q)\sim\sqrt{\frac{L_\eta}{n}}.
\]
These are variance/RMS statements. A normal confidence interval requires a separate CLT justification.

### \(C\) independent chains, \(N\) draws each

For independent chains satisfying the same assumptions, averaging their equal-length windows divides the variance by \(C\), but does not divide the bias:
\[
\operatorname{Var}(\bar q_{C,N})
\sim \frac{L_\eta}{CNt^2},
\qquad
\operatorname{SD}(t\bar q_{C,N})
\sim \sqrt{\frac{L_\eta}{CN}},
\]
when \(N(t)\to\infty\).

An important qualification: **\(CN\to\infty\) alone does not justify replacing the finite-window constant by \(L_\eta\)**. If \(N\) stays fixed and only \(C\) grows, the relevant constant is \(N W_{\eta,N}\), not \(L_\eta\).

### “Long windows are bias-dominated”

For fixed \(\eta>0\) and a nontrivial positive-definite model, \(b_\eta>0\), and your interpretation is correct:
\[
t^2\operatorname{MSE}(\bar q)
=t^2\operatorname{Var}(\bar q)
+\bigl(t(E\bar q-\langle L\rangle_{\rm loc})\bigr)^2
\longrightarrow b_\eta^2.
\]
More explicitly,
\[
t^2\operatorname{Var}(\bar q)=\frac{L_\eta+o(1)}{n},
\qquad
t(E\bar q-\langle L\rangle_{\rm loc})=b_\eta+o(1).
\]

I would say **“at fixed step-size parameter \(\eta\), sufficiently long averages are dominated by discretization bias.”** This avoids suggesting the same conclusion after bias correction or in a joint \(\eta\to0\) limit.

## 3. Suggested E4/E5 wording

**E4 — Monte Carlo uncertainty**

> For \(C\) independent chains with \(N\) sufficiently long post-burn-in draws per chain, the scaled LLC estimator has MC standard error asymptotic to \(\sqrt{L_\eta/(CN)}\). When modewise contributions are uniformly bounded above and below, this has the familiar \(\sqrt{d/(CN)}\) scaling. The prefactor reflects both stationary mode variances and their integrated autocorrelation times.

“MC standard error” is clearer than “covariance error,” unless you specifically mean error in estimating a covariance.

**E5 — Long-run variance and bias floor**

> In the anchored Gaussian model,
> \[
> L_\eta=\frac12\sum_i a_i^{-2}\tau_i,\qquad
> \tau_i=\frac{1+\alpha_i^2}{1-\alpha_i^2}.
> \]
> These are the integrated autocorrelation times of the quadratic mode observables. Under the stated burn-in condition, every growing window \(N(t)\to\infty\), with no additional restriction relative to \(t\), satisfies
> \[
> Nt^2\operatorname{Var}(\bar q)\to L_\eta.
> \]
> Averaging removes MC variance but leaves the scaled discretization bias \(b_\eta\), giving the limiting scaled MSE \(b_\eta^2\).

**Final vote: yes—formalise the candidate.** The strongest useful packaging is a uniform-in-\(n\) variance-error bound plus a uniform post-burn-in bias bound; the growing-window theorem then follows immediately.