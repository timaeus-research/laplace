## 1. Endorsement: **GO with Taylor-in-phase**

This is a better Lean route than rescaled measures **given your proved machinery**. It avoids constructing a new measure-theoretic interface while retaining the correct face concentration. No fundamental obstruction appears.

Your remainder estimate is valid, uniformly for \(\|\xi\|_\infty\le M\):
\[
\tau_K=e^{b^2/(2\beta)}
       \frac{(4b^2/\beta)^K K!}{(2K)!}
\le e^{b^2/(2\beta)}\frac{(4b^2/\beta)^K}{K!}\longrightarrow0.
\]
Take \(M\ge0\), and only normalize eventually, say \(N>1\).

**Two assembly corrections:**

- Comparing both approximants with \(I_N\) gives a bound involving \(\tau_K+\tau_{K'}\), not automatically \(2\tau_K\): your displayed \(\tau_K\) need not decrease from the outset. Either use a decreasing tail envelope, or directly bound the polynomial block:
  \[
  \left|\sum_{j=2K}^{2K'-1}\frac{z^j}{j!}\right|
  \le \frac{|z|^{2K}}{(2K)!}e^{|z|}.
  \]
  This gives a \(K'\)-independent Cauchy bound using \(\tau_K\) alone.

- Convergence of **even** partial sums does not, by itself, establish `HasSum`/`tsum`. Prove absolute summability, control the intervening odd partial sums, or avoid `tsum` in the main assembly.

For eventual bounds, use \(L+1\) rather than \(2L\) unless positivity of \(L\) is already convenient in Lean.

### Potentially cheaper assembly

**Define the proposed integral coefficient \(C\) first**, and apply `tendsto_of_approx` directly:

1. finite Taylor approximants converge to \(P_K\);
2. your estimate bounds the normalized original-integral error;
3. the **same Taylor estimate** bounds \(|C-P_K|\), integrated against
   \[
   A\,s^{p-1}\,ds\;\mathrm{residualWeight}(u)\,du,
   \qquad
   A=\frac1{(m-1)!\prod_{i\in J}k_i}.
   \]

The Gaussian envelope has finite mass. This eliminates the abstract Cauchy-limit construction and any infinite sum/integral interchange from the headline proof. You need only finite-sum interchange and the Gaussian moment identity. Prove the series representation separately if useful.

That is my preferred implementation, **unless the existing `amplitudeCoeff` API makes the abstract series substantially easier**.

## 2. Constants: **all your stated factors are correct**

Writing \(r=m-1\), the shifted theorem contributes
\[
c_j=
2^r\frac{\beta^j}{j!}
\operatorname{amplitudeCoeff}
(h+jk,k,\lambda+j/2,\beta)(\xi^j\eta).
\]

Both identities are right:
\[
N^j(N^2)^{-\lambda-j/2}=N^{-2\lambda},
\qquad
(\log N^2)^r=2^r(\log N)^r.
\]

The normal moment is
\[
\int_0^\infty s^{p+j-1}e^{-\beta s^2}\,ds
=\frac12\Gamma(\lambda+j/2)\beta^{-\lambda-j/2}.
\]

Consequently,
\[
\frac{2^{m-1}\cdot2}
{(m-1)!\prod_{i\in J}2k_i}
=\frac1{(m-1)!\prod_{i\in J}k_i}.
\]

Thus the final coefficient is exactly
\[
\boxed{
C=
\frac1{(m-1)!\prod_{i\in J}k_i}
\int_{(0,1]^d}
\eta(\pi u)\,
S_{p/2}^{(\beta)}(\xi(\pi u))\,
\prod_{i\notin J}u_i^{h_i-pk_i}\,du
}
\]
where
\[
S_{p/2}^{(\beta)}(a)
=\int_0^\infty s^{p-1}e^{-\beta s^2+\beta sa}\,ds.
\]

The residual exponents are \(>-1\). Coordinates in \(J\) integrate out with unit volume. Taking \(\xi=0\) recovers the transported zero-phase coefficient—a good regression theorem.

## 3. Headline XIII and stopping point

Suggested title:

> **General-dimensional phase-dressed monomial-chart leading asymptotic.**

State the deterministic limit for every continuous \(\xi,\eta\), with the **integral normal-moment formula** above. Make the series a supporting identity, not the paper-facing definition.

Explicit scope:

- **Mixed ratios:** only minimizing coordinates collapse; the phase and amplitude remain functions of the residual face coordinates.
- **Fixed deterministic phase:** no theorem yet for \(N\)-dependent random phases.
- **Single positive unit-box chart:** not arbitrary cutoffs, signed normal coordinates, or automatic gluing of resolution charts.
- **Local unnormalized integral:** a posterior-expectation theorem additionally needs denominator nonvanishing and the relevant chart/stratum assembly.
- The convention for \(S\), including its \(\beta\)-dependence and the factor \(1/2\) in its gamma-series expansion, must be explicit.

**Yes: this is the right stopping point for this implementation of A**, but label it “deterministic core of general-\(d\) random-phase leading asymptotics,” not “general-\(d\) random-phase theorem complete.”

One stochastic caveat matters: continuity of \(C\) plus convergence in distribution of \(\xi_N\) does **not alone** justify replacing the finite-\(N\) integral by \(C(\xi_N)\). You also need remainder control along the varying random inputs—typically uniform convergence on compact subsets of the phase space plus tightness. Fixed-phase pathwise convergence is insufficient.

A sup-norm local-Lipschitz lemma for \(C\) is cheap and useful now; a new stochastic input model need not be.

## 4. Cheaper alternatives

**Polynomial \(\xi\) is not a shortcut:** exponentiating a polynomial phase still leaves an infinite expansion. Transfer in \(\xi\) needs an additional exponential stability estimate. Your existing amplitude theorem already handles every \(\xi^j\eta\), so Taylor is exploiting precisely the strongest available interface.

My suggested unit order:

1. Scalar Taylor/Gaussian envelope.
2. Shifted-exponent transport, including unchanged \(J,m\) and residual weight.
3. Normal-moment integrability and Gaussian moments.
4. Direct approximation to the explicit coefficient.
5. Headline, zero-phase regression, mirror/report.
6. Optional series identity and coefficient continuity.

## 5. After A

**Prefer consolidated report v2, with D only if it is genuinely a cheap corollary.**

Fixed positive rectangular cutoffs are promising: \(u_i=a_i v_i\) reduces them to the unit box, replacing \(N\) by \(N\prod_i a_i^{k_i}\). The external leading factor is
\[
\prod_i a_i^{h_i+1-pk_i},
\]
with phase/amplitude composed with the dilation. This is coordinate transport, not new asymptotic analysis.

Do **not** start C merely to extend the completion list. Restricted subleading terms introduce qualitatively new remainder and resonance obligations.

**Recommendation:** finish deterministic A with its explicit normal-moment coefficient; take D if transport-only; close with report v2 documenting the stochastic, global-chart, and subleading gaps.
