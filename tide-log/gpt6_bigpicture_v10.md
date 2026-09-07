Querying gpt-6-astra (timeout: 560s)...
Response received in 168.0s
**My recommendation is: close parameter integration first, then prove coefficient continuity.** The integration adapter is now a short consequence of R5; it should not wait for a complete measurability API. Prove it with `AEStronglyMeasurable` hypotheses, then discharge those hypotheses in separate lemmas.

Two distinctions should remain explicit:

- Averaging \(Z\) is linear; averaging \(\log Z\) is a substantially different problem.
- Continuity of the canonical coefficients as functions of \(c\) is linear; continuity as functions of \((\eta,\xi)\) additionally requires continuity of the nonlinear amplitude-coefficient map.

## (a) Parameter integration

### 1. Use direct integration, not `param_integration`

For \(t_w\equiv1\), your existing `param_integration` is not the right abstraction: it solves the harder small-scale problem, but only for one exponent. Here the proof is simply
\[
\left|\int R_N(w)\varrho(w)\,d\mu(w)\right|
\leq \int |R_N(w)|\varrho(w)\,d\mu(w)
\leq K_T N^{-2T}(1+\log N)\int\varrho\,d\mu.
\]

There is no need to isolate a leading pole or iterate a single-exponent theorem.

I would first prove an **abstract finite-expansion integration lemma**, with no analytic machinery in its statement. Let \(P\) be a finite index set, \(a:P\to\mathbb R\), and assume:

- \(\varrho\geq0\) a.e. and \(\varrho\in L^1(\mu)\);
- \(A_j,B_j\) are a.e. strongly measurable and have a.e. constant bounds;
- for each \(N\geq1\), \(Z(\cdot,N)\) is a.e. strongly measurable;
- a.e. in \(w\),
  \[
  \left|Z(w,N)-\sum_{j\in P}N^{-a_j}
          (A_j(w)\log N+B_j(w))\right|
  \leq K\,r(N),
  \]
  where \(K,r(N)\geq0\).

Then all the weighted integrals exist and
\[
\begin{aligned}
\left|\int Z(w,N)\varrho(w)\,d\mu
-\sum_{j\in P}N^{-a_j}\left[
  \left(\int A_j\varrho\,d\mu\right)\log N+
  \int B_j\varrho\,d\mu
\right]\right|
\leq Kr(N)\int\varrho\,d\mu.
\end{aligned}
\]

**You do not need a separate integrability hypothesis for \(Z\).** For fixed \(N\), the finite coefficient bounds and the remainder estimate give a constant bound on \(|Z(w,N)|\). Multiply by the integrable density.

For a signed weight, replace the right-hand factor by \(\int|\varrho|\).

### 2. Then specialize immediately to the Taylor tree

The chart-facing theorem should say:

> For a measurable coefficient family satisfying a common analytic envelope a.e., and a nonnegative integrable weight, the averaged chart integral has the same finite Taylor tree, with averaged canonical coefficients and remainder constant multiplied by the mass of the weight.

Use `twoD_taylor_tree_uniform` and the existing canonical envelope bounds. No new estimates are needed.

It is also clean to formulate the abstract lemma first for a **finite measure \(\nu\)**:
\[
\left|\int Z_N\,d\nu-\sum_{\alpha\in P}
N^{-\alpha}\left[(\int A_\alpha\,d\nu)\log N+\int B_\alpha\,d\nu\right]\right|
\leq K_T\,\nu(\Omega)\,N^{-2T}(1+\log N).
\]
The weighted statement is then a change to the measure with density \(\varrho\). If your library is already organized around real-valued weights, however, direct multiplication avoids `ENNReal` bookkeeping.

### 3. Yes: initially assume measurability

I would explicitly allow the first specialization to assume:

- `AEStronglyMeasurable (fun w => Z w N) μ`, for each \(N\geq1\);
- `AEStronglyMeasurable Aα μ` and the corresponding assertion for \(B_\alpha\).

That is a useful, honest theorem—not an evasion. Keep “common envelope” and “measurability” separate in the API.

One important qualification: for the follow-up lemmas, measurability of
\[
w\mapsto c_{ij}(w,s)
\quad\text{for every fixed }s
\]
is not by itself the right hypothesis. Assume **joint measurability**
\[
(w,s)\mapsto c_{ij}(w,s).
\]
For concrete `ampCoeff` families, coordinatewise measurability of \(x,y\) should imply this through their explicit coefficient formulas.

### 4. Least painful measurability routes

#### For \(Z\): use partial sums and the original integral representation

Prove jointly measurable rectangular partial sums of `anaAmp`, then pass to their limit on the convergence region. Compose with
\[
(w,u,v)\longmapsto (w,u,v,Nu^{k_1}v^{k_2}),
\]
multiply by the elementary kernel, and apply parameterized-integral measurability.

The fallback is robust even if the exact real-valued `tsum` measurability theorem is inconvenient:

1. finite rectangular sums are measurable;
2. your absolute-convergence theorem identifies their limit;
3. measurable limits give measurability.

With only a.e. envelope assumptions, either use a.e. limit theorems or first restrict to a **measurable full-measure good set**, defining the amplitude to be zero elsewhere. Avoid building a proof around a nonmeasurable “set of good parameters.”

#### For \(A_\alpha,B_\alpha\): use the series formulas

Here units 125–126 are likely the cleaner route. For example, a representation of the schematic form
\[
U_\alpha(w,s)=\sum_j q_{\alpha j}\,c_{i_\alpha j}(w,s)
\]
reduces measurability to measurable summands and convergence. Then `logMoment` requires just one parameterized integral.

**Do not interchange the sum and `logMoment` merely to prove measurability.** Joint measurability of the series followed by measurability of its integral is enough. Interchanging them is more useful later for R6.

For all exact `tsum` and parametric-integral lemma names: **grep first**. I would not commit an implementation plan to the spelling of `Measurable.integral_prod_right` versus its strongly-measurable variants.

### 5. Where a genuine scale occurs

In the normal form you quoted,
\[
e^{-\beta n u^{2k}+\beta\sqrt n\,u^k\xi_n(u,v)},
\]
the noncritical variable \(v\) enters the amplitude/random field, not the large-parameter scale. Thus \(t_v=1\).

A scale appears if the phase retains a positive unit:
\[
e^{-\beta N^2q(v)u^{2k}+\beta Nu^k\xi(u,v)}.
\]
Then \(t_v=\sqrt{q(v)}\), together with the field renormalization
\[
\xi'(u,v)=\xi(u,v)/\sqrt{q(v)}.
\]
Whether that unit has already been absorbed by the resolution coordinates is a paper-specific question. Do not manufacture a scale solely because there are noncritical parameters.

Your `param_integration` becomes valuable precisely when such scales can approach zero and inverse-scale integrability matters.

## (b) R6: bounded linear coefficient functionals

### The weighted-\(\ell^1\) statement is worth proving

For a finite set \(F\subset(0,\infty)\), put
\[
W_F(s)=e^{-\beta s^2}\sum_{\gamma\in F}
s^{\gamma-1}(1+|\log s|),
\]
and
\[
\|c\|_{r,F}
=\sum_{i,j}r^{i+j}\int_0^\infty W_F(s)|c_{ij}(s)|\,ds.
\]

For \(b<r<\rho\), the useful target is
\[
|A_\alpha(c)|+|B_\alpha(c)|
\leq K_{\alpha,F,r}\|c\|_{r,F},
\qquad \alpha\in F,
\]
or one simultaneous bound after summing over \(F\).

Two qualifications:

1. On raw pointwise coefficient arrays this is a **seminorm**. It becomes a norm after quotienting by a.e. equality, or by working in an appropriate weighted \(\ell^1(L^1)\) space.
2. Linearity of Bochner integrals requires integrability. Prove linearity on the admissible finite-norm class, not on arbitrary arrays using totalized integrals.

It is perfectly reasonable initially to prove the boundedness and difference estimates without constructing a `ContinuousLinearMap`.

### Why the series formulas should make this manageable

The face-series multipliers have the general behavior
\[
q_j\sim \frac{b^j}{\text{affine function of }j},
\]
with resonances removed and handled separately. For fixed geometric data and a finite pole set:

- the nonzero denominators have a positive lower bound;
- factors polynomial in \(j\), if present, are absorbed by \((b/r)^j\);
- resonant correction terms are finite.

Thus prove deterministic multiplier bounds such as
\[
|q_j|\leq C r^j,
\]
then integrate absolute values and sum. This proves an operator bound directly, instead of trying to extract one from a sup-envelope theorem.

Also stage the difference form:
\[
|A_\alpha(c)-A_\alpha(d)|
+|B_\alpha(c)-B_\alpha(d)|
\leq K\|c-d\|_{r,F}.
\]
That is the form later users will actually apply.

### What topology is needed for the SLT application?

Without the paper’s convergence theorem in front of us, I would not claim that it proves convergence in this topology. The necessary bridge is:

\[
\xi_n\Rightarrow G
\quad\Longrightarrow\quad
c(\eta,\xi_n)\Rightarrow c(\eta,G)
\text{ in a topology controlling the canonical coefficients.}
\]

A particularly compatible choice is a coefficient Banach-algebra norm
\[
\|y\|_r=\sum_{i,j}|y_{ij}|r^{i+j}.
\]
For the amplitude coefficient map, the Banach-algebra exponential estimate gives, on bounded sets,
\[
\|c_s(x,y)-c_s(x',y')\|_r
\leq
e^{\beta s M_y}
\left(\|x-x'\|_r+\beta s M_x\|y-y'\|_r\right),
\qquad s>0.
\]
Integrating against \(W_F\) gives local Lipschitz continuity into your weighted moment space, since the Gaussian absorbs \(e^{\beta sM_y}\) and the extra factor \(s\).

That provides the clean chain
\[
(x,y)\longmapsto c\longmapsto(A_\alpha,B_\alpha)_{\alpha\in F}.
\]

Uniform convergence of holomorphic extensions on a **larger** closed polydisc can control a coefficient norm on a smaller one by Cauchy estimates. Uniform convergence only on a real rectangle does not give that conclusion.

**Ranking:** (a) first, because it is nearly free now; then this R6 package. R6 is the more important bridge to convergence in law.

## (c) R7: Taylor-data identification

### Reuse unit 102 before introducing multivariate analytic infrastructure

The desired one-variable lemma is:

> If \(r>0\) and \(\sum_n|a_n|r^n<\infty\), then the represented power series is smooth near zero and
> \[
> \operatorname{iteratedDeriv}_m
> \left(x\mapsto\sum_n a_nx^n\right)(0)=m!\,a_m.
> \]

The crucial part is not coefficient uniqueness alone: you must also establish that the represented function has the required derivatives. Check whether unit 102 already packages that implication.

For the double series, proceed exactly as you suggest:

1. Fix \(|v|<r\), set \(a_i(v)=\sum_jc_{ij}v^j\).
2. Absolute summability gives
   \[
   \sum_i r^i|a_i(v)|\leq\sum_{i,j}|c_{ij}|r^{i+j}.
   \]
3. Deduce, locally in \(v\),
   \[
   \operatorname{iteratedDeriv}_i
      (u\mapsto\Phi(u,v))(0)
   =i!\sum_jc_{ij}v^j.
   \]
4. Differentiate that identity \(j\) times at \(v=0\).

This yields
\[
\operatorname{iteratedDeriv}_j
\left(v\mapsto
\operatorname{iteratedDeriv}_i(u\mapsto\Phi(u,v))(0)\right)(0)
=i!j!c_{ij}.
\]

This avoids mixed Fréchet derivative bookkeeping entirely.

### Mathlib names: grep first

I am confident about the central objects `FormalMultilinearSeries`, `HasFPowerSeriesOnBall`, `HasFPowerSeriesAt`, and `iteratedDeriv`. I am **not** sufficiently confident about the exact constructor/derivative lemma spellings in your checkout to recommend the candidate names in the question as verified.

A useful search is:
```text
rg 'ofScalars|iteratedDeriv|iteratedFDeriv.*zero|summable.*radius' \
  Mathlib/Analysis/Analytic Mathlib/Analysis/Calculus

rg 'hasFPowerSeriesOnBall|HasFPowerSeriesAt' Mathlib/Analysis
```

Choose between that API and unit 102 only after checking what the latter already proves.

### Two paper-facing cautions

For your application, the identification is pointwise in \(s\):
\[
c_{ij}(s)=\frac{1}{i!j!}
\partial_v^j\partial_u^i
\bigl[\eta(u,v)e^{\beta s\xi(u,v)}\bigr]_{(0,0)}.
\]
Identifying the coefficients of \(\eta,\xi\) themselves then makes this a finite expression in their rectangular jets, with the expected exponential constant term.

But **do not conclude that every canonical \(A_\alpha,B_\alpha\) depends on finitely many corner derivatives**. A face coefficient generally uses a fixed normal derivative and an entire transverse function, represented by an infinite series in the other index. R7 identifies the input Taylor data; it does not turn all finite-part face functionals into finite corner jets.

## (d) R9: expectation

For \(E[Z_N]\), nothing substantial remains beyond (a). A probability measure is simply the finite-measure version with total mass one; no density need be introduced.

Useful immediate corollaries are
\[
|E[R_N]|\leq K_TN^{-2T}(1+\log N),
\qquad
E[|R_N|]\leq K_TN^{-2T}(1+\log N).
\]
Indeed the same deterministic bound gives an \(L^p\) remainder bound for every finite \(p\geq1\).

For \(E[\log Z_N]\), positivity is only the first step. You also need control of the lower tail of the normalized integral, or suitable uniform integrability of its logarithm. A small absolute error in \(Z_N\) does not control its logarithm near zero.

Even a chart-positivity lemma should have the correct hypothesis: a nonnegative amplitude that is strictly positive on a set of positive measure, with a strictly positive kernel, suffices. A partition-of-unity chart amplitude need not be strictly positive everywhere.

I cannot identify the paper’s §4.3 “fluctuation function” from the supplied information. **Read the definition before choosing between a ratio, log ratio, or centered free-energy quantity.** I would not spend a unit on a guessed definition.

## (e) Next five units

| Priority | Suggested unit | Deliverable |
|---|---|---|
| 1 | `finite_tree_integration` | Abstract finite-sum integration lemma; Taylor-tree specialization with explicit a.e.-measurability hypotheses; probability corollary |
| 2 | `twoDAmp_parameter_measurable` | Jointly measurable coefficient family ⇒ measurable chart integral, using partial sums |
| 3 | `canonical_parameter_measurable` | Series-based measurability of canonical coefficients; discharge the hypotheses in unit 1 |
| 4 | `canonical_weighted_l1_bound` | Linearity on the admissible class, weighted moment bound, and coefficient difference estimate |
| 5 | `ampCoeff_continuous` | Local Lipschitz/continuity from analytic coefficient data into the weighted moment space |

I would place R7 immediately afterward, unless unit 102 makes it a genuinely short corollary. The fifth unit is especially valuable because it prevents R6 from stopping one map short of the stochastic application.

### Paper-facing statements already worth staging from R5

1. **Uniform Taylor-tree remainder on bounded analytic families.**
   The constant depends only on the stated geometric and envelope parameters, not on the individual amplitude.

2. **Translation to the paper’s \(n\)-variable.** If \(N=\sqrt n\), then
   \[
   Z_c(\sqrt n)
   =
   \sum_{\alpha<2T}n^{-\alpha/2}
   \left(\tfrac12 A_\alpha(c)\log n+B_\alpha(c)\right)
   +O_{\mathrm{uniform}}\!\left(n^{-T}(1+\log n)\right).
   \]
   Keep the factor \(1/2\) on the logarithmic coefficient explicit.

3. **Uniformity from analytic bounds on \(\eta,\xi\).**
   State this after composing R5 with the existing amplitude-envelope theorem, specifying exactly which analytic bounds produce \(C_0,L,D\).

4. **Averaging preserves the canonical tree.**
   Finite-mass parameter integration changes coefficients by integration and multiplies the remainder constant by the mass.

5. **Triangular-array applicability.**
   The uniform estimate applies to \(c_N\), including random \(N\)-dependent amplitudes, whenever they satisfy the same envelope. The coefficients may then depend on \(N\); their convergence is a separate R6/CMT assertion.

6. **Intrinsic truncation.**
   The retained exponents are exactly \(\Lambda\cap(-\infty,2T)\), independently of the auxiliary cutoffs used to prove the estimate.

The strongest new paper-facing message is therefore: **the Taylor tree is uniform on bounded analytic families, commutes with finite-mass averaging, and is ready for a separate continuity argument—not yet an automatic logarithmic expectation theorem.**
