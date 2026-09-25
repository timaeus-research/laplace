## Q1. Closure audit

**Yes—at the round-13 criterion you quote, I would call the Euclidean active-truth and mixed-truth layer closed.**

Items 1–5 now provide the previously missing chain:

- exact transport from the resolution;
- certification of the phase and density factors consumed by the analysis;
- the general-unit boundary asymptotic;
- its interpretation as a chart-level limiting measure, including positivity;
- extraction of that measure as the certificate’s leading term.

I would **not** move the goalposts by making either parked log-face question a prerequisite.

Two qualifications delimit that verdict:

1. This does not yet assert that an arbitrary certified **general-truth** export automatically packages into the existing Euclidean phase/term machinery. That is Q2’s interface extension, rather than a remaining gap in the Euclidean claims.
2. Exact push-forward identifies densities **almost everywhere**. If the note identifies a particular pointwise conditional-density version, rather than the exported kernel or the resulting measure, that identification needs continuity or another version-selection argument. Transport alone does not identify arbitrary versions pointwise.

Subject to those distinctions, I see no missing statement in the stated closure criterion.

## Q2. A general-truth `Phase`

**Yes: a `TruthChartsData.Phase` is the right next consumer interface. Hand instances should remain regression tests, not the permanent interface.**

There is no mathematical reason for the asymptotic machinery to distinguish a coordinate truth from a nonlinear truth once it has the same chart-level monomialisation and solved-coordinate bridge.

### The actual abstraction boundary

I would separate two layers.

**A. Monomial truth geometry**

This supplies, per chart:

- the monomial truth identity;
- a chosen index `k` with positive truth exponent;
- `solvedCoord`, its domain, and `bridgePt`;
- the identity `T (rep (bridgePt y t)) = t`;
- the box-membership and truncation conditions;
- the exact fibre-Jacobian factor;
- the measurability/continuity facts needed downstream.

**B. Phase and density data**

This supplies:

- `kF`, `a`, `ma`, `Ma`;
- `hJ`, `bJ`, `mb`, `Mb`, `wt`;
- their identities and bounds;
- the derived exponent bookkeeping;
- the model-kernel identity connecting A and B.

Then the term theorems consume these layers, rather than a distinguished ambient coordinate functional.

In particular, compactness supplies a positive lower bound for `|a|` and `|bJ|` **if continuity and nonvanishing hold on the closed box**. Nonvanishing only on the open box would not suffice. No positive lower bound should be imposed on `wt`.

### Does `bridgePt` go through unchanged?

If the certified normal form is
\[
T(\operatorname{rep}u)=S\prod_j u_j^{q_j}
\]
with `S` a nonzero **chart scalar**, then yes: on a chosen sign chamber,
\[
u_k=
\left(\frac{t}{S\prod_{j\ne k}u_j^{q_j}}\right)^{1/q_k},
\]
and the same construction applies. Branch/sign handling and the box cutoff are part of the interface, not new asymptotic analysis.

If `S` is instead a **variable unit** `S(u)`, the construction is not literally unchanged: this formula becomes an implicit equation in `u_k`. One must first absorb the unit into coordinates, or provide a separately certified solution and Jacobian. That is the principal mathematical distinction to check.

Charts on which all truth exponents vanish also need their existing treatment—typically exclusion from sufficiently small truth levels or a separate nonsingular contribution—rather than an invented solved coordinate.

### Which theorems really used `ℓ`?

I cannot certify a Lean dependency audit from the theorem names alone. The mathematical dependency I expect is:

- `vertex/tied/partial`: the model integral and its exponent data;
- `activeTruth/activeTruthDegenerate`: additionally, the bridge path and its limiting geometric interpretation through `rep`.

None should need ambient linearity of truth **after** those identities have been abstracted. The likely coordinate-specific dependencies lie in construction lemmas for `bridgePt`, `modelKernelOf`, and their chart identities—not in the fibre asymptotics themselves.

Thus I would generalise the common chart API, and have the current Euclidean `Phase` instantiate it. Avoid maintaining two nearly identical analytic implementations.

## Q3. The exported mixed instance

**Yes, `T(x,y)=xy` is the right integration test.** But it is important that this is a *crossing* test: its zero set is singular at the corner. A nonlinear truth with regular zero set generally tests the ordinary coarea regime, not the logarithmic corner mechanism.

### Minimal target

On the positive unit square, with unweighted density and a continuous observable `θ`, prove from the exported charts that
\[
\frac{K_\theta(t)}{\log(1/t)}
\longrightarrow \theta(0,0)
\qquad(t\downarrow0).
\]

Taking `θ = 1` tests the coefficient. Allowing continuous `θ` tests the limiting measure:
\[
\frac{K_{\bullet}(t)}{\log(1/t)}
\longrightarrow \delta_{(0,0)}.
\]

Here \(K_\theta\) is the **exported** kernel. One need not initially add a nontrivial Laplace phase; use a constant nonzero phase if the interface requires a phase certificate.

### Which theorem fires?

For a truth-only monomial chart
\[
T=S\prod_j u_j^{q_j},\qquad
\mathrm{dens}\sim c\prod_j u_j^{h_j},
\]
the diagnostic quantities are
\[
\alpha_j=\frac{h_j+1}{q_j}\quad(q_j>0).
\]
The smallest ratio determines the truth power; multiplicity of that minimum determines the logarithmic degree.

For the identity chart of `xy`, both ratios are \(1\). This is the **two-way tied logarithmic regime**, not the new degenerate-boundary theorem merely because the truth is nonlinear.

A useful explicit resolved model is the two sector charts
\[
(u,v)\mapsto(u,uv),\qquad (u,v)\mapsto(uv,u).
\]
Each has
\[
T=u^2v,\qquad |\det D\operatorname{rep}|=u,
\]
hence ratios \(2/2=1\) and \(1/1=1\). Each sector contributes
\[
\int_{\sqrt t}^{1}\frac{du}{u}
=\frac12\log(1/t),
\]
so the total coefficient is \(1\).

That is an excellent calibration for the tied-log consumer. The precise Lean constructor may be `TermData.tied` or its truth-endpoint wrapper, depending on its hypotheses; I would not promise that constructor name without checking the parameter conventions.

### What an arbitrary export changes

Do **not** require an arbitrary resolution to produce those two charts or make every chart tied. Instead:

1. construct a phase for each exported chart;
2. classify its exponent data;
3. apply the applicable term theorem;
4. discard subleading terms at the mixed normalisation;
5. sum all dominant chart measures.

Partition weights can distribute the coefficient among charts. The invariant target is the **sum**, not a prescribed coefficient per chart.

For a minimal first test, it is reasonable to identify the aggregate coefficient using the existing identity-chart result plus exact transport. There is a subtlety: transport gives equality of kernels only a.e. But **once both normalised limits have been proved to exist**, a.e. equality suffices to identify those limits. It does not, by itself, transfer pointwise limit existence.

That makes this a genuine interface test without requiring an additional resolution-invariance calculation of every chart constant.

## Q4. The parked items

I would distinguish a precise model statement from an assertion about the exact normalisations in your files, which I cannot recover from the summary alone.

### A. Exact log-face constant

The natural statement is:

> Replace the upper/lower constants in the logarithmic endpoint by an actual limit, whose coefficient is the face-volume factor times the integral of the transverse limiting profile, with all Jacobian and measure-normalisation factors included.

For example, consider the clean logarithmic model
\[
I(L)=\int_{\mathbb R_{\ge0}^n}
e^{-c\cdot x}
\exp\!\left(-\sum_i a_i e^{L-\alpha_i\cdot x}\right)\,dx,
\qquad a_i>0,\ c_j>0.
\]
Let
\[
P=\{p\ge0:\alpha_i\cdot p\ge1\},\qquad
\lambda=\min_P c\cdot p,
\]
and let \(F\) be the optimal face, of dimension \(d\). Assume \(P\) is nonempty. Put
\[
V=\operatorname{span}(F-F),\qquad N=V^\perp,
\]
and define
\[
J_0=\{j:p_j=0\ \text{throughout }F\},\qquad
A_0=\{i:\alpha_i\cdot p=1\ \text{throughout }F\}.
\]
The expected exact formula, with induced Euclidean measures, is
\[
\lim_{L\to\infty}e^{\lambda L}L^{-d}I(L)
=
\operatorname{vol}_d(F)
\int_N
\mathbf1_{\{z_j\ge0,\ j\in J_0\}}
e^{-c\cdot z}
\exp\!\left(-\sum_{i\in A_0}a_i e^{-\alpha_i\cdot z}\right)\,dz.
\]

Nonorthogonal coordinates introduce the corresponding determinant/coarea factor. Nonconstant units or amplitudes may require an integral over the face of a face-dependent transverse profile rather than a simple product.

**Belief:** true under the appropriate hypotheses. But a sandwich alone does not identify this coefficient.

**Recommendation:** worth a bounded round only after pinning down the exact model and measure conventions. The first task should be the precise constant statement and the missing convergence lemma, not another broad asymptotic framework.

### B. LP uniqueness ⇔ profile integrability

The word **profile** is decisive.

For an optimal point \(p_*\), define the **unquotiented anchored profile**
\[
\Psi_{p_*}(z)=
\mathbf1_{\{z_j\ge0\text{ when }p_{*,j}=0\}}
e^{-c\cdot z}
\exp\!\left(
-\sum_{\alpha_i\cdot p_*=1}
a_i e^{-\alpha_i\cdot z}
\right).
\]
In the same finite-dimensional positive-coefficient setting, the intended equivalence is
\[
p_*\text{ is the unique LP minimiser}
\quad\Longleftrightarrow\quad
\Psi_{p_*}\in L^1(\mathbb R^n).
\]

**I believe this version is true.** The geometric criterion is strict positivity of the cost on every nonzero recession direction of the active tangent polyhedron. A second optimum supplies a zero-cost feasible direction along which the profile fails to decay sufficiently; uniqueness removes those directions.

But the following superficially similar assertion is **false**:

> The profile transverse to the optimal face is integrable iff the optimum is unique.

After quotienting out the face directions, the transverse profile should be integrable also for positive-dimensional optimal faces. That is precisely what allows a finite exact logarithmic coefficient.

Likewise, arbitrary vanishing amplitudes or partition weights can destroy the equivalence. State it for the positive model profile, or for amplitudes bounded above and below by positive constants.

**Recommendation:** a bounded theorem-design round is worthwhile now; a full formalisation is not yet the highest-priority integration task. First fix “anchored, unquotiented profile” explicitly and prove the recession-cone criterion. If the note intended a different profile, revisit the conjecture before formalising it.

## Q5. Ranking

1. **General-truth chart/phase consumer interface.**  
   This converts the certified export into reusable asymptotic input and removes the remaining hand-instance bottleneck.

2. **Exported `xy` mixed regression, initially with `θ = 1`, then continuous observables.**  
   It tests transport, exponent bookkeeping, tied logarithms, chart summation, and the limiting measure in one small example.

3. **A reusable a.e.-transport/limit-identification lemma, if absent.**  
   Small infrastructure that prevents pointwise-version mistakes in the integration test and future applications.

4. **Precise anchored-profile/recession-cone statement for LP uniqueness.**  
   A bounded conceptual task that distinguishes a plausible theorem from the false quotient-profile formulation.

5. **Exact log-face constant.**  
   Valuable, but broader than the interface work; schedule it once its normalisation and transverse-integrability dependencies are explicit.

6. **A richer nonlinear truth example.**  
   Only after `xy`; otherwise geometric complexity can obscure a simple consumer-interface defect.

**Bottom line:** close the Euclidean chapter, build the general-truth consumer once, and make exported `xy` the acceptance test. Keep the exact-constant programme separate from that closure.