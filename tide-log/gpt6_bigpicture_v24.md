**Recommendation: one bounded end-to-end application, not another general extension.** XVIII–XIX plus the hand-off meet the original stop gate. Continuing should now demonstrate applicability, not merely enlarge the theorem catalogue.

Estimates below are **additional units**, conditional on the existing interfaces.

## Ranking and gates

| Rank | Programme | Estimate | Go/no-go gate |
|---|---|---:|---|
| **1** | **H2-lite: concrete normal-crossing statistical model** | **4–8** | Within one reconnaissance unit, identify the exact posterior identity, all measurability/integrability obligations, and the existing headline that supplies its limit. No general resolution machinery. |
| **2** | **E2: leading Mellin/Abelian coefficient** | **2–4** | First write the exact Mellin convention and coefficient. Proceed only if the proof reduces to concentration of product power measures plus existing integration lemmas. |
| **3** | **K: freeze, index, CI, hand-off** | **1–2** | Always GO. Make this the fallback if H2-lite fails reconnaissance. |
| **4** | **J: compact observable families** | **1–3** | Specify the observable topology and one common random environment. GO for a finite-net upgrade using an established uniform continuity estimate; not for an unspecified “functional convergence” claim. |
| **5** | **F: random amplitudes/observables** | **2–4** | Require a precise function-space topology, joint convergence there, and continuity of the limiting quotient on an almost-surely admissible set. Otherwise NO-GO. |
| **6** | **I: polynomial second-order terms** | **reconnaissance 1; implementation 4–8+** | GO only after deriving the actual second term, including logarithmic corrections and a remainder smaller than it. Leading shifted-monomial equivalents alone do not suffice. |
| **7** | **H2-full: genuine blow-up atlas and partition** | **10–20+; high variance** | Defer unless an explicit atlas, Jacobians, overlap treatment, and admissible weights are already worked out on paper. The change-of-variables theorem alone is not the missing bridge. |

### Recommended concrete application

Take
\[
Y_i\stackrel{\mathrm{iid}}{\sim}N(0,1),\qquad
Y_i\mid(x,y)\sim N(xy,1),\qquad (x,y)\in[-1,1]^2,
\]
with a continuous strictly positive prior. Then the likelihood ratio is **exactly**
\[
\exp\!\left(\sqrt n\,Z_nxy-\frac n2x^2y^2\right),
\qquad Z_n=n^{-1/2}\sum_iY_i.
\]

This buys three things:

* no likelihood remainder;
* no geometric resolution assumption: the four-quadrant decomposition is explicit;
* no unproved phase CLT: \(Z_n\) is standard normal for every \(n\), once the finite Gaussian-sum law is supplied.

Use a **bounded nonconstant observable of \(\sqrt n\,xy\)** if XIX supports that normal-variable observable. An ordinary continuous parameter observable in this equal-ratio example can have only the uninteresting point-evaluation limit.

**Success gate:** a named theorem about the actual normalized posterior of this model, with no chart-decomposition or empirical-phase-convergence hypothesis left to discharge. It may retain the explicit model/prior assumptions. Call it an **end-to-end normal-crossing example**, not a demonstration of resolution of singularities.

**Abort gate:** if the required observable interface or Gaussian-law infrastructure forces a substantial new framework, stop and hand off. Do not escalate automatically to a blow-up example.

## E2: relevant, but label it correctly

**Yes, paper-relevant:** it identifies the leading Mellin singular coefficient underlying the pole/multiplicity interpretation. It is an **Abelian real-axis statement**, not a Tauberian theorem and not, by itself, meromorphic continuation.

For the convention
\[
M(z)=\int u^{kz}\eta(u)u^h\,du,\qquad
p=\min_{k_j>0}\frac{h_j+1}{k_j},
\]
your proposed coefficient is correct under the usual continuity and integrability assumptions, with \(J\) the minimizing coordinates.

A direct proof may be cleaner than reusing the mixed-ratio Laplace theorem: each critical-coordinate measure
\[
s\,u_j^{k_js-1}\,du_j
\]
has total mass \(1/k_j\) and concentrates at zero.

**Convention gate:** if the paper instead takes the Mellin transform of \(K=u^{2k}\), the pole is at \(-p/2\), and
\[
s^m M_K(-p/2+s)\longrightarrow 2^{-m}C.
\]
Do this audit before coding.

## Why not I next?

Polynomial amplitudes remove the amplitude-regularity objection, **but not the asymptotic-order objection**. A single monomial integral can itself contribute
\[
n^{-\lambda}(\log n)^{m-1},\quad
n^{-\lambda}(\log n)^{m-2},\ldots
\]
before any different power of \(n\) appears. Summing leading equivalents of shifted monomials does not establish these corrections, especially after cancellation. Separate:

* **finite polynomial reduction:** potentially cheap;
* **certified next-order expansion:** materially new work.

## Hand-off audit

The listed qualifications sound appropriate; I cannot certify the source statements from this summary. I would check/add:

1. **Scaling ambiguity in this consultation:** with \(N=\sqrt n\), the model Laplace factor is ordinarily \(e^{-\beta N^2u^{2k}}\). The expression \(e^{-\beta Nu^{2k}}\) uses a different Laplace parameter. State the transform parameter explicitly.
2. **What “chart decomposition assumed” contains:** exact integral identity, coverage up to null sets, multiplicities/overlaps, absolute Jacobians, transformed support, and transformed phase—not just existence of charts.
3. **Nonvanishing leading denominator:** positive interior densities do not alone ensure positive restrictions to the dominant face. Vanishing partition weights can remove nominally dominant contributions. State positivity of the actual assembled leading denominator.
4. **Remainders at the required topology:** scalar \(o(S_*)/o_P(S_*)\) is sufficient only for the scalar claims actually proved. Uniform-observable claims require correspondingly uniform remainder control.
5. **Phase convergence topology and measurability:** name the function space, topology, and measurable limit object. “Induced joint law” must not suggest independence or a proved empirical-process limit.
6. **Mode of probabilistic conclusion:** distinguish convergence in distribution of posterior observables/random measures from in-probability, almost-sure, or stable convergence.
7. **Parameter scope:** fixed versus varying temperature, fixed prior, and any restriction to sample sizes \(n\ge1\).
8. **Mellin language:** a real-axis leading coefficient is not yet a complex pole theorem.

**Operational direction:** authorize one H2-lite reconnaissance unit now. If it passes, finish that example and freeze. E2 is the best small optional appendix; none of F/I/J is needed to call the present programme complete.
