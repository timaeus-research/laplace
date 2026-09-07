## Recommendation

The highest-value continuation is **to remove u150’s deterministic support bound, then use that upgrade to prove a one-chart posterior-ratio theorem**. These close an actual gap between the current library and the paper’s probabilistic conclusions.

I would defer general \(d\). The constant-Gaussian calculation is worthwhile, but it is an illustrative expectation theorem rather than infrastructure needed by the main convergence results.

In parallel, start the paper-facing theorem inventory now; make the final `Headline.lean` wrappers after localisation and division land.

---

## (a) Localisation: expose tightness, but derive it in the main corollary

I recommend **both formulations, at different layers**:

1. **Reusable perturbation lemma:** assume eventual norm-tightness and uniform-on-balls error bounds.
2. **Paper-facing theorem:** assume \(X_n\Rightarrow Z\), derive norm-tightness, and conclude the normalised-remainder convergence without a bounded-support hypothesis.

This avoids making the analytic localisation lemma depend on portmanteau while avoiding an unnecessary hypothesis in the final theorem.

### Suggested abstraction

For measurable errors \(e_n\), assume:

\[
\forall \eta>0\;\exists M\ge1,\quad
\forall^{\mathrm{eventually}} n,\quad
\mu\{\|X_n\|>M\}\le \operatorname{ofReal}(\eta),
\]

and, for every \(M\ge1\), a deterministic sequence \(r_M(n)\to0\) such that eventually

\[
\|X_n(\omega)\|\le M\implies \|e_n(\omega)\|\le r_M(n).
\]

Then \(e_n\to0\) in probability.

For fixed \(\delta>0\), eventually \(r_M(n)<\delta\), so simply use

\[
\{\|e_n\|\ge\delta\}\subseteq\{\|X_n\|>M\}.
\]

This is cleaner in Lean than introducing an indicator term into an ENNReal inequality. Allowing the ball estimate **eventually in \(n\)** also absorbs conditions such as \(N_n>1\).

The abstract lemma need not mention convergence in distribution at all. Afterwards apply it to u148/u149 and use the perturbation theorem you found.

### Deriving norm-tightness

Yes: portmanteau on

\[
F_M=\{a:M\le\|a\|\}
\]

is sufficient. Choose \(M\) with

\[
\mathbb P(\|Z\|\ge M)<\eta/2.
\]

Then portmanteau, followed by the strict slack \(\eta/2<\eta\), gives eventually

\[
\mathbb P(\|X_n\|>M)
\le \mathbb P(\|X_n\|\ge M)
<\eta.
\]

Important terminology: this proves **norm-boundedness in probability**, not compact tightness of the CoeffPair-valued laws. Infinite-dimensional balls are not compact. Norm-boundedness is exactly what your ball estimates need.

Of the facts you listed, **`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` is the relevant downstream portmanteau theorem**. The remaining API issue is the bridge from `TendstoInDistribution` to convergence of the pushforward `ProbabilityMeasure`s. I would inspect that bridge before committing to an exact invocation; the supplied declaration name alone does not settle the argument types.

An alternative is:

- transfer \(X_n\Rightarrow Z\) through `norm`;
- prove the scalar tail statement.

That can simplify topology, though it does not necessarily simplify the measure bookkeeping.

### Cost

- Norm-tightness from distributional convergence: **1–2 units**, mostly API.
- Generic localisation plus A/B instantiations: **1–2 units**.
- Joint finite-vector version: ideally included, otherwise **one small additional unit**.

Keep u150 as the elementary bounded-support theorem; add the unrestricted version rather than replacing it.

---

## (b) Constant-Gaussian model: use an ENNReal core, then recover expectation

Your formula is correct under the essential assumptions

\[
\beta>0,\qquad p>0,\qquad v=\sigma^2\ge0.
\]

The best foundational object is the nonnegative moment **without the amplitude prefactor**:

\[
J_p(x)=\int_0^\infty s^{p-1}e^{-\beta s^2+\beta sx}\,ds.
\]

First prove the Tonelli identity in ENNReal:

\[
\mathbb E_{\!+}[J_p(X)]
=
\int_0^\infty
s^{p-1}e^{-(\beta-\beta^2v/2)s^2}\,ds.
\]

Here the formal version either uses a lintegral-defined \(J_p^+\), or proves
`ENNReal.ofReal (J_p x) = J_p⁺ x` using the already-available moment integrability.

Then prove

\[
\mathbb E_{\!+}[J_p(X)]
=
\begin{cases}
\operatorname{ofReal}\!\left(
J_p(0)(1-\beta v/2)^{-p/2}
\right),&\beta v<2,\\[2mm]
\infty,&\beta v\ge2.
\end{cases}
\]

### Why isolate the prefactor?

The \(+\infty\) claim for \(A_p\) requires

\[
\frac{y_{00}}{k_1k_2}>0.
\]

If \(y_{00}=0\), the expectation is zero, even in the supercritical regime. If \(y_{00}<0\), a nonnegative lintegral is not the appropriate expectation object. Separating the positive moment avoids contaminating the core theorem with these cases.

Also distinguish:

- \(J_p(x)\) is finite for every finite \(x\);
- its expectation can be infinite.

That distinction is exactly the point of the example.

### Proof economy

Use `mgf_gaussianReal`, which you have located, together with the relevant integrability facts around it. Do not treat a bare real-integral MGF identity as sufficient for a lintegral conversion without establishing integrability.

No Gamma evaluation is required. In the subcritical case, rescale the quadratic coefficient relative to \(J_p(0)\). At and above criticality, compare on \(s\ge1\) with \(s^{p-1}\), whose integral diverges for \(p>0\).

**Cost:** approximately **3–5 units**, depending on the existing moment substitution API.

**Value:** high as a precise formalisation of `rem:pop_vs_emp`, particularly because it captures the integrability threshold. Below localisation and posterior division in priority.

---

## (c) General \(d\): prove a universal product-density lemma, not Mellin inversion

Your formula is correct for \(d\ge1\), \(k_i>0\), and common ratio \(\lambda>0\):

\[
I_d(N)=
\frac{\prod_i(2k_i)^{-1}}{(d-1)!}
\int_0^1 z^{\lambda-1}(-\log z)^{d-1}e^{-\beta Nz}\,dz.
\]

I would not use Mellin inversion.

### Minimal useful architecture

**1. One-dimensional power substitution.**

For nonnegative measurable \(g\), prove the weighted substitution

\[
\int_0^1 u^{h_i}g(u^{2k_i})\,du
=
\frac1{2k_i}\int_0^1 t^{\lambda-1}g(t)\,dt.
\]

A nonnegative formulation avoids integrability prerequisites during iteration. Working on \((0,1]\) can simplify logarithms and real powers; transfer back to the closed box by null endpoints.

**2. Universal multiplicative integration formula.**

For nonnegative measurable \(g\), prove

\[
\int_{(0,1]^d}
g\!\left(\prod_i t_i\right)\prod_i t_i^{\lambda-1}\,dt
=
\frac1{(d-1)!}
\int_0^1 g(z)z^{\lambda-1}(-\log z)^{d-1}\,dz.
\]

Alternatively prove the unweighted product law first and absorb \(z^{\lambda-1}\) into the test function. Either is a reusable pushforward theorem.

**3. Induction using scalar substitution and Tonelli.**

The induction reduces to

\[
\int_z^1
\frac{(-\log(z/t))^{d-1}}{t}\,dt
=
\frac{(-\log z)^d}{d}.
\]

This elementary identity is the core calculation. Isolate it.

**4. Bridge iterated integrals to the finite-dimensional box.**

Use finite-product measures and the equivalence separating one coordinate. I would prove the analytic induction with iterated integrals first, then discharge the `Fin d → ℝ` box packaging separately.

Search around `Measure.pi`, finite-product integration, `volume_pi`, and coordinate equivalences. **I would not assume Mathlib already has the product-of-coordinates pushforward theorem.** The generic `Measure.map` infrastructure packages your result; it does not supply the density computation.

**5. Specialise \(g(z)=e^{-\beta Nz}\), then prove the asymptotic.**

The leading term is

\[
I_d(N)\sim
\frac{\Gamma(\lambda)\beta^{-\lambda}}
{(d-1)!}\left(\prod_i(2k_i)^{-1}\right)
N^{-\lambda}(\log N)^{d-1}.
\]

This is a strong, honest general-\(d\) milestone—but still a special monomial model.

### Cost and comparison

- Exact product-density identity and box conversion: **5–8 units**.
- Leading asymptotic: **2–4 more**, depending on moment/log infrastructure.

The existing `iterChart` and projection lemmas help with algebra and asymptotics, but do not remove the multidimensional change-of-variables work.

Be careful with “\(\Lambda=\lambda+\mathbb N/(2k)\)”:

- For this **bare monomial model**, the expansion is at \(N^{-\lambda}\) with a log polynomial; a full arithmetic ladder is not the natural conclusion.
- Taylor amplitudes introduce shifted exponents.
- If the \(k_i\) differ, there is no single \(k\) without choosing a common denominator, and a lattice containment is not the same as identifying the actual nonzero support.

A leading-term-only theorem is substantially cheaper than general grammar, but still needs the analytic reduction above.

---

## (d) Posterior ratio: very valuable; the key is jointness and a nonzero limit denominator

I rank this **second as a programme, immediately after localisation**.

Use a joint input encoding the shared field and both amplitudes, for example

\[
W_n=(\xi_n,\eta_{\varphi,n},\eta_{1,n}).
\]

Do not infer the required joint convergence from separate convergence of two CoeffPair-valued inputs. Shared \(\xi_n\) must be represented in the theorem.

Set

\[
s_n=N_n^{-\alpha_0}\log N_n.
\]

For the equal-start leading log regime, prove jointly

\[
\left(
\frac{Z_n[\varphi]}{s_n},
\frac{Z_n[1]}{s_n}
\right)
=
\left(A^\varphi(W_n),A^1(W_n)\right)+o_{\mathbb P}(1).
\]

Then, if \(W_n\Rightarrow W\) and

\[
\mathbb P(A^1(W)=0)=0,
\]

obtain

\[
\frac{Z_n[\varphi]}{Z_n[1]}
\Rightarrow
\frac{A^\varphi(W)}{A^1(W)}.
\]

### Positivity

For the canonical equal-start coefficient, prove

\[
y_{00}>0\implies
\frac{y_{00}}{k_1k_2}
\int_0^\infty s^{p-1}e^{-\beta s^2+\beta sx_{00}}\,ds>0.
\]

Use integrability plus strict positivity on a positive-measure subinterval.

Notice that “positive in the interior of the box” need not imply \(y_{00}>0\). State positivity at the relevant corner explicitly, or deduce it from positivity on the **closed** box.

### Two versions worth exposing

1. **Deterministic division:** on a ball and under \(A^1\ge c>0\), derive a quantitative error bound.
2. **Probabilistic division:** require only \(A^1(W)>0\) almost surely.

The second requires localisation away from zero, or an almost-everywhere-continuous mapping theorem. Global `continuous_comp` alone cannot handle division at zero.

A stronger and particularly paper-faithful conclusion is

\[
\frac{Z_n[\varphi]}{Z_n[1]}
-
\frac{A^\varphi(W_n)}{A^1(W_n)}
\longrightarrow 0
\quad\text{in probability},
\]

followed by convergence in distribution. This captures the empirical leading coefficient evaluated at the **current** input.

**Cost after localisation:** approximately **3–4 units**, including positivity and the joint-error wrapper. The numerator’s leading coefficient may vanish; only the denominator needs nonvanishing.

---

## (e) Consolidation: yes, and make the scope impossible to misread

Create both:

- `Headline.lean`: thin, paper-facing theorem wrappers;
- a theorem inventory in the README or `grammar_lean.tex`.

Do not use the headline file to re-prove results or manufacture one enormous conjunction.

### Appropriate `\leanref` claims

The annotations should identify precise restricted statements:

- **Two-dimensional chart expansion:** the actual assumptions on \(h,k,\beta,b,\rho\), amplitude regularity/representation, truncation, and exponent range.
- **Uniform remainder on coefficient-norm balls:** explicit dependence of the remainder constant.
- **Coefficient continuity and finite-dimensional distributional transfer.**
- **Normalised A/B-slot convergence:** explicitly mention subtraction of lower terms and, in the B-slot, the **current** \(A_\alpha(X_n)\log N_n\) contribution.
- **Localised versions:** only once the bounded-support hypothesis has actually been removed.
- **Far-phase estimate:** under the stated deterministic lower bound for \(K\), upper bound for \(|\psi|\), and integrability of the amplitude.
- **Expectation statements:** only the specific theorem proved, with its integrability or domination assumptions.

For each item, display: paper statement, Lean declaration, scope restriction, and extra hypotheses.

### Explicitly do not claim

- General-\(d\) grammar from the existing general-\(d\) algebraic identities.
- A global resolution-of-singularities or multi-chart theorem from one-chart results.
- Automatic convergence of expectations from convergence in distribution.
- Uniform-in-\(\omega\) far-phase decay without control of the random bound \(M\).
- A full posterior-ratio expansion from first-order division.
- Full-function/process convergence from finite coefficient-vector convergence.
- The paper’s appendix tightness result for its original random fields unless the map into CoeffPair and the required convergence have also been verified.

**Cost:** roughly **one wrapper/documentation unit**, potentially two if the hypothesis audit exposes missing bridges. This is unusually high-value work at 151 units.

---

## (f) Next five units

| Rank | Suggested unit | One-line specification |
|---|---|---|
| **1** | `NormBoundedInProbability` | Derive eventual norm-tail control from `TendstoInDistribution`, with the current filter and probability-space assumptions. |
| **2** | `LocalisedNormalisedRemainder` | Abstract uniform-on-balls perturbation lemma; remove u150’s deterministic support bound for A, B, and the joint pair needed for division. |
| **3** | `LeadingCoeffPositive` | Prove canonical equal-start denominator positivity, plus a quantitative lower bound under bounded field input and \(y_{00}\ge c>0\). |
| **4** | `PosteriorLeadingRatio` | Shared-input, two-amplitude leading-ratio approximation in probability and distributional convergence under an almost-surely nonzero limiting denominator. |
| **5** | `Headline` | Paper-facing wrappers and an audited `\leanref` inventory separating proved \(d=2\) statements from deferred claims. |

These are target units, not guarantees of one-file effort: ranks 2 and 4 are the likely split points.

**Next after those:** the constant-Gaussian Tonelli/dichotomy theorem. **After that:** the general-\(d\) product-density milestone, if arbitrary dimension remains the paper’s highest-priority uncovered claim.
