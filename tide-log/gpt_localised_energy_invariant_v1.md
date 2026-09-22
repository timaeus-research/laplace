## 1. Correctness and coefficients

**A, B, C are correct**, with two qualifications about rates and normalisation.

- **A’s coupling sign is positive.** Set \(\delta=w_0-c\). Orthogonality gives
  \[
  g\langle\delta,m_1\rangle
  =-\sum_i\frac{a_i\alpha_i}{2\lambda_i^2},
  \qquad
  \frac{g^2}{2}\langle\delta,H^{-1}\delta\rangle
  =\sum_i\frac{a_i^2}{2\lambda_i}.
  \]
  Thus the proposed invariant coefficient is exactly right.

- **B’s limit and proposed \(O(1/t)\) rate are right.** With fixed \(g\) and anchor, localisation does not change the leading Gaussian energy variance:
  \[
  t^2\operatorname{Var}_{\rm loc}(\ell)=\frac12+O(t^{-1}).
  \]
  However, **even-moment envelopes alone do not immediately deliver this rate**: the \(x^5\) term needs signed cancellation, specifically \(\langle x^5\rangle_{\rm loc}=O(t^{-3})\). An absolute fifth-moment estimate gives only \(O(t^{-5/2})\).

- **The next variance coefficient is indeed \(2\sum_i e_{1i}\):**
  \[
  t^2\operatorname{Var}_{\rm loc}(L)
  =\frac d2+\frac{2\sum_i e_{1i}}t+O(t^{-2}).
  \]
  Numerically, your parameters give approximately **\(-1.58427\)**. Do **not** justify this by differentiating the landed remainder bound. Prove it independently through moments/covariances.

  A useful cancellation target in one dimension is
  \[
  t^2\langle\ell^2\rangle_{\rm loc}
  =\frac34+\frac{3e_1}{t}+O(t^{-2}),
  \qquad
  (t\langle\ell\rangle_{\rm loc})^2
  =\frac14+\frac{e_1}{t}+O(t^{-2}).
  \]
  For the first identity, you need fourth moment through \(t^{-3}\), fifth and sixth through \(t^{-3}\), **with \(O(t^{-4})\) remainders**, plus signed seventh moment \(O(t^{-4})\) and eighth moment \(O(t^{-4})\). The seventh-moment cancellation is an additional check on feasibility. Treat second-order variance as a stretch goal.

- **C is correctly scaled.** Writing
  \[
  C_1=\sum_i(e_{1i}+g/(2\lambda_i)),
  \]
  tide 73 gives \(t^2(\langle L\rangle-\tfrac12\operatorname{tr}(HS))=C_1+O(t^{-1})\); squaring gives exactly C.

**Explicit error in D:** it mixes scaled and unscaled predictors. If \(T(t)=\frac12\operatorname{tr}(tHS)\), then
\[
t^2T'(t)\longrightarrow\frac g2\sum_i\lambda_i^{-1}.
\]
Consequently D’s displayed expression tends to
\[
\frac d2-\frac g2\sum_i\lambda_i^{-1},
\]
not \(d/2\). An \(O(t^{-2})\) derivative changes the **constant** after multiplication by \(t^2\).

## 2. Wording against the note

Your interpretation of A is sound. Say explicitly:

> The discrepancy of the **scaled localised energy \(t\langle L\rangle_{\rm loc}\)** from the Gaussian trace prediction \(\frac12\operatorname{tr}(tHS)\) has \(1/t\) coefficient  
> \[
> E_1+\frac{g^2}{2}\langle w_0-w_*,H^{-1}(w_0-w_*)\rangle
> +g\langle w_0-w_*,m_1\rangle.
> \]

The three interpretations are correct. In particular, the quadratic term is the leading squared-mean energy omitted by the **trace-only** Gaussian predictor.

B is worth stating, preferably as:

> The same LLC \(d/2\) governs the leading energy fluctuation and temperature response:
> \[
> -\partial_t\langle L\rangle_{\rm loc}
> =\operatorname{Var}_{\rm loc}(L)
> =\frac{d}{2t^2}+O(t^{-3}).
> \]

This is a substantive fluctuation–response reading, not merely a restatement obtained by differentiating an asymptotic estimate.

## 3. Lean route for B

**Use covariance linearity if the required probe rates are available; otherwise use direct moments. Do not build a new IBP hierarchy just for this theorem.**

The exact reduction is
\[
t^2\operatorname{Var}(\ell)
=\frac{\lambda}{2}t^2\operatorname{Cov}(\ell,x^2)
+\frac{\alpha}{6}t^2\operatorname{Cov}(\ell,x^3)
+\frac{\gamma}{24}t^2\operatorname{Cov}(\ell,x^4).
\]
For B’s stated rate, precisely these estimates suffice:
\[
\left|t^2\operatorname{Cov}(\ell,x^2)-1/\lambda\right|\le K/t,
\quad
|t^2\operatorname{Cov}(\ell,x^3)|\le K/t,
\quad
|t^2\operatorname{Cov}(\ell,x^4)|\le K/t.
\]

The supplied inventory confirms the square-probe rate, **not cubic/quartic covK rates**. Mere convergence of those last two terms is insufficient for your quantitative conclusion.

If missing, the direct expansion is predictable:
\[
\ell^2=\frac{\lambda^2}{4}x^4+\frac{\lambda\alpha}{6}x^5
+\left(\frac{\lambda\gamma}{24}+\frac{\alpha^2}{36}\right)x^6
+\frac{\alpha\gamma}{72}x^7+\frac{\gamma^2}{576}x^8.
\]
For leading B, use the fourth-moment rate, signed fifth-moment bound, and higher-moment envelopes. Then subtract the square of the landed energy rate.

Finally:
1. split variance using product-measure cross-covariance vanishing;
2. sum the one-dimensional rates;
3. instantiate `hasDerivAt_localised_separable` with the energy probe, discharging polynomial integrability.

## 4. Bundle and next target

**Vote: A+B+C, with B committed only at leading order.** Prioritise A, then B; C is a cheap corollary. Do not make second-order variance a completion requirement.

A particularly useful inexpensive corollary is **matched anchor** \(w_0=w_*\): the trace-discrepancy coefficient reduces exactly to \(E_1\).

**Best next target:** second-order energy variance, followed by the *correctly normalised* derivative discrepancy. Put
\[
P(t)=\tfrac12\operatorname{tr}(HS(t)).
\]
Then the natural theorem is
\[
\left|t^3\bigl(\operatorname{Var}_{\rm loc}(L)+P'(t)\bigr)-2C_1\right|
\le K/t.
\]
This recovers **twice A’s invariant coefficient** in the derivative discrepancy, using genuine fluctuation estimates rather than unjustified differentiation of remainders.