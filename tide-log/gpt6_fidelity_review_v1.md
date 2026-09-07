## Overall verdict

The displayed statements support the **two-dimensional, single-chart expansion and conditional distributional consequences**, with consistent exponent normalisation. I find **no blocking mathematical mismatch in the displayed headline conclusions**.

Several descriptions should nevertheless be narrowed: the fluctuation-function identification needs explicit factors of \(2\); the Lipschitz headline proves a bound only for \(A_\alpha\); the averaging headline assumes more than joint measurability; and the posterior headlines do not establish the paper’s division formula or full posterior expansion.

This is a statement-level review of the supplied excerpts, not a compilation or proof audit. In particular, the definitions of `faceFPCoeff`, `canonicalM`, and the underlying proof bodies are not supplied, so their implementation cannot be independently certified here. Locations below use theorem names where source line numbers were not supplied.

## Findings, by headline theorem

1. **[cosmetic] `Laplace/Grammar/Headline.lean::headline_standard_integral` — correct integrand identification, with a parameter-domain qualification.**

   The right-hand side has exactly the paper’s chart integrand for
   \[
   \xi(u,v)=\mathrm{dblSum}\,x\,u\,v,\qquad
   \eta(u,v)=\mathrm{dblSum}\,y\,u\,v,\qquad N=\sqrt n.
   \]
   There is no sign restriction on `y`, consistently with the paper.

   The Lean identity is more general: it permits arbitrary real `β` and `N`, and zero `k₁` or `k₂`. That is harmless for the identity, but the description as the paper’s standard integral applies only after imposing the paper’s positive parameters and \(N=\sqrt n\geq0\). For negative \(N\), \(N=\sqrt{N^2}\) is false and the fluctuation term changes sign.

   The theorem identifies iterated integrals over \((0,b]^2\), not literally the paper’s product-domain integral over \([0,b]^2\). For the analytic inputs these agree by integrability, Fubini, and null boundaries; that bridge is not itself stated in this wrapper.

2. **[cosmetic] `Headline.lean::headline_taylor_tree`; `polesBelowGen`, supplied lines 327–329 — the normalisation and truncation are correct.**

   Under `hp₁`, `hp₂`, and positive `k₁`, `k₂`, the exponent progressions are
   \[
   \alpha=\frac{h_i+1+j}{k_i}=2\mu,\qquad j\in\mathbb N.
   \]
   The filter `α < 2 * T` therefore corresponds exactly to the paper’s \(\mu<T\).

   The finite ranges do not omit an exponent below the cutoff: writing
   \[
   q=\max(2T,p_1,p_2)+1,
   \]
   any \(p_i+j/k_i<2T\) satisfies
   \(j<k_i(q-p_i)\), hence is included before filtering. Thus `polesBelowGen` has the advertised meaning **under the headline’s hypotheses**; it does not have that meaning for arbitrary, unrelated arguments `p₁`, `p₂`.

   The expansion translates to
   \[
   Z(\beta,n)
   =\sum_{\mu<T}n^{-\mu}
      \left(\frac{A_{2\mu}}2\log n+B_{2\mu}\right)
     +O\!\left(n^{-T}(1+\log n)\right).
   \]
   This faithfully gives the \(d=2\) polynomial degree bound. Taking a larger cutoff than any requested retained exponent supplies the usual asymptotic interpretation.

   Using the entire candidate set with possibly zero coefficients is compatible with the paper’s existence of a subset \(\Lambda^*\subseteq\Lambda\): the theorem does not, however, identify a smaller combinatorial subset or the actual nonvanishing support.

   The weighted-summability input is a different presentation, not necessarily a genuinely stronger analytic assumption: holomorphic extension to \(D_R\) permits choosing \(b<\rho<R\) and obtaining weighted summability by Cauchy estimates. The headline does not formalise that passage from the paper’s hypotheses.

3. **[cosmetic] `Headline.lean::headline_taylor_tree_uniform` — faithful additional refinement, in the specified norm.**

   The statement really gives a constant independent of `a` throughout the ball `‖a‖ ≤ M`, for every \(N\geq1\). The exponents and coefficient identifications are the same as in item 2.

   Its explicit description as a refinement not stated in the paper is appropriate. “Bounded analytic families” must mean bounded in this fixed-radius weighted coefficient norm; it should not be read as a result for arbitrary families bounded in an unspecified \(C^\omega\) topology.

4. **[should-fix] `Headline.lean::headline_leading_coefficient` — the Lean formula is correct, but “the fluctuation function … in the \(s=\sqrt t\) variable” needs the Jacobian factor.**

   The exact change of variables is
   \[
   S_\lambda(a)
   =2\int_0^\infty s^{2\lambda-1}
       e^{-\beta s^2+\beta as}\,ds.
   \]
   Consequently,
   \[
   \operatorname{logMoment}\beta\,p\,0
      (s\mapsto e^{\beta as})
   =\frac12 S_{p/2}(a),
   \]
   and the displayed Lean formula means
   \[
   A_p=\frac{y_{00}}{2k_1k_2}S_{p/2}(x_{00}).
   \]
   Since \(A_p\) multiplies \(\log N\), the corresponding coefficient of
   \(n^{-p/2}\log n\) is
   \[
   C_{p/2,2}=\frac{A_p}{2}
      =\frac{y_{00}}{4k_1k_2}S_{p/2}(x_{00}).
   \]
   Thus there is **no factor error in the Lean formula**, but its prose should not identify the integral with \(S_{p/2}\) without the factor \(1/2\).

   The positivity conclusion is correct: the hypotheses imply \(p>0\), and \(S_{p/2}(a)>0\). The theorem is restricted to equal starting exponents and proves positivity only when \(y_{00}>0\). Without that condition, calling this the actual “leading coefficient” need not imply it is nonzero, consistently with the paper’s warning.

   **Related coefficient locations:** `CanonicalCoefficients.lean::canonC`, lines 185–188; `canonA`, lines 191–192; `canonB`, lines 195–198; `logMoment`, supplied lines 54–55.

   Their coefficient roles are consistent:
   \[
   A_\alpha=M_{\alpha,0}[C_\alpha],\qquad
   B_\alpha=M_{\alpha,0}[U_\alpha]
             +M_{\alpha,0}[V_\alpha]
             -M_{\alpha,1}[C_\alpha].
   \]
   The minus sign is the expected one from
   \(\log(N/s)=\log N-\log s\). More generally,
   \[
   M_{\alpha,\ell}[c]
   =2^{-(\ell+1)}
      \int_0^\infty t^{\alpha/2-1}(\log t)^\ell
                  e^{-\beta t}c(\sqrt t)\,dt.
   \]
   For \(c(s)=e^{\beta as}\), this is
   \(2^{-(\ell+1)}\partial_\lambda^\ell S_\lambda(a)|_{\lambda=\alpha/2}\),
   with differentiation under the integral justified analytically. Polynomial factors \(s^r\) similarly correspond to derivatives in \(a\), with
   \[
   M_{\alpha,0}[s^r e^{\beta as}]
      =\frac{1}{2\beta^r}
        \partial_a^r S_{\alpha/2}(a).
   \]
   These identities give the required normalisation for fluctuation-function derivative formulas. The exact boundary constants inside `canonU` and `canonV` cannot be checked fully without `faceFPCoeff`.

5. **[cosmetic] `Headline.lean::headline_taylor_data` — faithful Taylor-coefficient identification, not the full derivative-series claim.**

   The conclusion correctly states
   \[
   \partial_v^j\partial_u^i\xi(0,0)=i!\,j!\,x_{ij}.
   \]
   It assumes a local series representation and weighted summability; it does not derive those from an arbitrary holomorphic extension. It applies equally to the amplitude after instantiating the function and array accordingly.

   It identifies the input arrays with derivatives, but does not itself prove that every canonical asymptotic coefficient has the paper’s absolutely convergent derivative-series representation.

6. **[should-fix] `Headline.lean::headline_expectation` — correct averaging bound, but the parenthetical measurability claim overstates the hypotheses.**

   The conclusion is the advertised finite-truncation averaging estimate with a uniform constant. It is not the posterior expectation \(Z_n[\phi]/Z_n[1]\).

   The sentence “Only joint measurability of the data is assumed” is inaccurate without a qualification. Besides `hcm`, the theorem assumes:

   - continuity in \(s\) of every coefficient function (`hcc`);
   - continuity in \(s\) of the envelope (`hH`);
   - the coefficientwise weighted bound (`hc`);
   - a common deterministic polynomial-exponential envelope (`henv`);
   - the chart and positivity hypotheses.

   It is accurate that no continuity in the random parameter \(w\) is required. The domination assumptions are substantial and are not consequences of convergence in distribution alone.

7. **[should-fix] `Headline.lean::headline_coefficient_lipschitz` — the headline claims both canonical coefficients, but the theorem bounds only \(A_\alpha\).**

   The displayed conclusion contains only the difference of two `canonA` values. It supplies a local Lipschitz estimate for the log coefficient in weighted Taylor data, for \(\alpha>0\).

   There is no `canonB` estimate in this wrapper. Accordingly, “the canonical coefficients are locally Lipschitz” overclaims this theorem’s conclusion. The later distributional wrapper includes both coefficients, but that does not make this wrapper a Lipschitz theorem for \(B_\alpha\).

   Also, the supplied paper excerpts do not include `prop:convergence`; its attribution cannot be checked here. In any event, a weighted coefficient-norm result is not by itself an identification with the paper’s \(C^\omega\)-topology claim.

8. **[cosmetic] `Headline.lean::headline_coefficients_in_distribution` — faithful conditional coefficient convergence, not an empirical-process theorem.**

   The statement gives joint convergence of every finite vector of canonical coefficients, conditional on convergence in distribution of the coefficient-pair data. It even permits positive exponents outside the candidate set; that causes no mismatch.

   To identify these with the paper’s notation in dimension two, use
   \[
   C_{\mu,2}=A_{2\mu}/2,\qquad C_{\mu,1}=B_{2\mu}.
   \]
   Deterministic rescaling preserves convergence in distribution.

   The theorem does not show that the statistical hypotheses produce `hX`, nor that `Z` is Gaussian. It also permits random amplitudes, whereas an analytic observable and prior would usually supply a deterministic chart amplitude. That is a harmless generalisation of the conditional result.

9. **[cosmetic] `Headline.lean::headline_normalised_remainders` — faithful ordered chart-level limits, with the same factor-of-two translation.**

   The two conclusions correctly extract the log coefficient and then the constant coefficient:
   \[
   \frac{Z-L_{<\alpha}}{N^{-\alpha}\log N}\Rightarrow A_\alpha,
   \qquad
   \frac{Z-L_{<\alpha}-N^{-\alpha}A_\alpha(X_n)\log N}
        {N^{-\alpha}}\Rightarrow B_\alpha.
   \]
   In the paper’s \(n\)-normalisation, the first limit is \(A_{2\mu}/2\) when the denominator is \(n^{-\mu}\log n\); the second is \(B_{2\mu}\).

   This matches the paper provided its order processes smaller exponents first and, at a fixed exponent, higher log powers first. The excerpt does not define `<`; ordinary increasing lexicographic order in \((\mu,m)\) would not express that asymptotic order.

   The restrictions to measurable data on a common source probability space and a countably generated filter are additional formal hypotheses. They accommodate the usual sequential empirical-process setting. Membership in a chosen finite cutoff is not a substantive loss, since any candidate exponent can be retained by taking \(T>\alpha/2\).

10. **[should-fix] `Headline.lean::headline_far_phase` — the inequality is appropriate, but the headline’s exponential-negligibility claim needs \(\varepsilon>0\).**

    The bound follows the expected estimate
    \[
    M\sqrt{nK}\leq \frac{nK}{2}+\frac{M^2}{2}.
    \]
    Its hypotheses allow `ε = 0`; then the bound does not decay exponentially in \(n\). Exponential negligibility requires fixed \(\varepsilon>0\), together with suitable control of the amplitude integral and \(M\).

    There is also no measurability assumption on `K` or `ψ`, nor integrability assertion for the displayed integrand. Lean’s integral is total, so this does not invalidate the inequality as stated, but the theorem alone does not certify that the expression is an ordinary integrable partition-function contribution. Measurability of the exponential factor, together with the displayed domination, supplies that application bridge.

    For the paper’s random far-phase contribution, a suitable probabilistic bound on the fluctuation must still be supplied; this is a deterministic estimate, not that probabilistic step in full.

11. **[cosmetic] `Laplace/Grammar/HeadlinePosterior.lean::headline_approx_in_distribution` — accurately labelled generic tool.**

    The conclusion faithfully expresses stability under modifications whose probabilities can be made arbitrarily small, at both the approximating and limiting ends.

    It has no direct paper coefficient or exponent identification and proves no grammar-specific claim by itself. The measurability and filter hypotheses are explicit.

12. **[should-fix] `HeadlinePosterior.lean::headline_quotient_in_distribution` — correct quotient convergence, but not the paper’s division lemma.**

    Joint convergence and an almost-surely positive limiting denominator give exactly the displayed quotient convergence. Joint convergence, rather than merely separate marginal convergence, is the appropriate hypothesis.

    Positivity is stronger than the nonvanishing condition sufficient for this generic result, but is aligned with the posterior application. Finite-stage denominators need not be positive or nonzero under the displayed assumptions.

    The parenthetical “the division lemma of cor:empirical_expectation, probabilistic form” overclaims: this theorem contains no asymptotic series, recursive coefficient division, or index-set construction. It is a probabilistic quotient tool supporting a leading-limit argument, not the paper’s formal division formula.

13. **[cosmetic] `HeadlinePosterior.lean::headline_joint_normalised_pair` — faithful in the equal-starting-exponent case.**

    Since both progressions start at \(p\), there are no candidate exponents below \(p\). Therefore `lowerPart` vanishes at \(p\), and the displayed `normA` pair really is the pair of raw chart integrals divided by
    \[
    s_n=N_n^{-p}\log N_n.
    \]
    The common scale and joint convergence are correct. In the \(n\)-scale \(n^{-p/2}\log n\), both limiting coefficients would be divided by \(2\).

    `withY` correctly fixes the two amplitudes while retaining a common random phase. Formally, however, `hX` assumes convergence of the entire coefficient pair, including an amplitude component subsequently discarded by `withY`; this is sufficient but stronger than assuming convergence of the phase alone.

    This is the equal-starting-exponent, log-leading case, not the full range of chart leading behaviours.

14. **[should-fix] `HeadlinePosterior.lean::headline_chart_posterior_limit` — correct special-case ratio limit, but not a general “leading term” result.**

    For equal starting exponents,
    \[
    A_p(x;y)=\frac{y_{00}}{2k_1k_2}S_{p/2}(x_{00}),
    \]
    so the common strictly positive fluctuation factor cancels. The deterministic ratio limit is therefore correct under the stated assumptions.

    Its scope needs three qualifications:

    - **Equal starting exponents are essential to the stated result.** Unequal starting exponents and general multi-chart leading terms are not covered.
    - **The numerator corner coefficient may vanish.** If `yφ (0,0) = 0`, the conclusion is a zero limit, not an identification of the numerator’s true leading index, the posterior’s first nonzero term, or its decay rate.
    - **The denominator amplitude need only be positive at the corner.** The theorem does not assume a positive density throughout the chart and does not assert positivity of every finite-stage denominator. Lean’s total division is used. Thus “posterior” here denotes the chart quotient under these hypotheses, not automatically an everywhere-defined Bayesian expectation.

    The equality with \(\phi(0,0)\) additionally requires the amplitude-product identification \(\eta_\phi=\phi\eta_1\); that relation is explanatory prose, not a hypothesis or conclusion of this wrapper.

## Paper claims not covered by these headlines

The supplied headlines do **not** establish:

- The Taylor-tree theorem for general \(d\), including log degrees above one.
- Resolution of singularities, chart construction, multi-chart assembly, or the global partition-function decomposition.
- The formal passage from arbitrary holomorphic chart functions to weighted coefficient data, or identification of the paper’s analytic-function topology with the coefficient-space topology.
- An explicit smaller combinatorial set \(\Lambda^*\), or the actual nonvanishing support and leading indices.
- The complete claim that every coefficient is an absolutely convergent series explicitly expressed through derivatives of \(\xi,\eta,S_\lambda\). The displayed definitions and Taylor-data theorem support parts of that identification, but the full representation-and-convergence assertion is not a headline conclusion.
- The functional CLT from hypothesis I and relative finite variance, Gaussianity of the limit, or verification that the empirical process satisfies the assumed coefficient-space convergence.
- The full random/global far-phase negligibility argument.
- The full posterior-ratio expansion, its discrete index sets, recursive division coefficients, or distributional convergence of all those quotient coefficients.
- General leading posterior behaviour for unequal starting exponents, cancellations, different numerator/denominator leading indices, or multiple contributing charts.
- Convergence of numerical expectations from convergence in distribution without additional domination. `headline_expectation` is a separate dominated averaging result.

## Proposed exact one-sentence `\leanref` caveats

**§4.2**

> The Lean formalisation covers the single-chart \(d=2\) finite-truncation expansion for weighted absolutely summable Taylor data, with \(N=\sqrt n\), \(\alpha=2\mu\), and \(P_\mu(t)=\tfrac12A_{2\mu}t+B_{2\mu}\), but does not formalise the general-dimensional theorem, the passage from arbitrary holomorphic inputs, or the full absolutely convergent derivative-series representation of all coefficients.

**§4.3**

> The Lean formalisation proves single-chart \(d=2\) coefficient and ordered-remainder convergence conditional on convergence in distribution of weighted Taylor data, together with a deterministic far-phase bound and an equal-starting-exponent chart quotient limit, but does not derive the empirical-process CLT, assemble the resolved charts, or prove the full recursive posterior-ratio expansion.
