**My recommendation: publish the addendum, take the cheap unequal-exponent quadratic closure, then make (A) the next substantial mathematical programme.** Do not turn the success of u194 into a reason to reopen TaylorTree or Mellin continuation.

The estimates below are **additional theorem-bearing units**, not build jobs. They assume the interfaces you describe are reusable; I have not inspected the pinned checkout.

## Ranking

| Rank | Programme | Estimate | Why now |
|---|---|---:|---|
| **1** | **(E) Second author report / addendum** | **0** theorem units | The stochastic theorem closes an explicitly advertised gap. That deserves communication now, independently of further mathematics. |
| **2** | **(B) Zero-phase unequal-exponent quadratic charts** | **1–2**; possibly **+1–2** for general mixed \(d\) | Highest-confidence mathematical closure: an exact dictionary plus asymptotic transport, not a new analytic mechanism. |
| **3** | **(A) General-\(d\) random-phase leading term** | **4–7** with a suitably reusable integral interface; **7–10** if measure infrastructure must be built | Best next substantial extension. It addresses nonconstant phase without claiming TaylorTree. |
| **4** | **(D) Rectangular cutoffs / product-measure tangential presentation** | **1–2** | Useful interface polish, especially if it removes a concrete obstacle for (A). Otherwise optional. |
| **5** | **(C) Restricted subleading coefficient** | **2–4** | Sound and tractable, but introduces a different asymptotic direction rather than closing the current general-\(d\) leading-term gap. |
| **6** | **(F) TaylorTree, Mellin continuation, \(\Delta\)-boundary, SLT** | Require separate scoping | Nothing in these successes removes their principal missing dependencies. Still unsuitable as autonomous follow-ons. |

Thus the operational sequence is **E → B → gate A**. Stopping after E, or after E+B, would be entirely natural.

## Top mathematical pick: (B), with a deliberately narrow first unit

I would make the first unit a **two-dimensional, zero-phase, strict-mixed-ratio cross-validation**, in the style of u193.

For the convention
\[
Q_N=\int_0^1\!\int_0^1
x^{h_1}y^{h_2}
e^{-\beta(Nx^{k_1}y^{k_2})^2}\,dy\,dx,
\]
assume
\[
\beta>0,\qquad k_1,k_2>0,\qquad h_1,h_2>-1,
\qquad
p:=\frac{h_1+1}{k_1}<\frac{h_2+1}{k_2}.
\]
Then the first-unit statement should be
\[
\boxed{
N^pQ_N\longrightarrow
\frac{\Gamma(p/2)}
 {2k_1\,\beta^{p/2}\,(h_2+1-pk_2)}.
}
\]

Use the repository’s actual exponent types and hypotheses; the displayed real inequalities describe the mathematics, not a demand to generalise the existing API.

A schematic Lean shape is:

```lean
-- Schematic: use the existing quadratic integral and constant definitions.
theorem quadratic_zeroPhase_mixed_tendsto
    (hβ : 0 < β)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hmixed : (h₁ + 1) / k₁ < (h₂ + 1) / k₂) :
    Tendsto
      (fun N : ℕ =>
        (N : ℝ) ^ p * quadraticBoxIntegral β k₁ k₂ h₁ h₂ N)
      atTop
      (𝓝 quadraticMixedConst)
```

I would package three things together:

1. **Exact integral dictionary:** quadratic exponents \(k_i\) become monomial exponents \(2k_i\), with monomial scale \(\beta N^2\), or its equivalent under the existing \(\beta\)-parameter API.
2. **Exact constant dictionary:** identify `noLogConst` with the displayed gamma expression.
3. **Transported limit/equivalence:** invoke the mixed seabed theorem; do not reprove domination.

The reversed strict inequality should follow by coordinate exchange or the corresponding existing theorem, not by duplicating the analysis.

### Two cautions for this unit

**First, audit the factor of two explicitly.** Substituting \(N^2\) changes both the power and, when present, the logarithmic coefficient. This is exactly where cross-validation earns its keep.

For the unit-box general-\(d\) model, put
\[
p=\min_i\frac{h_i+1}{k_i},\qquad
J=\left\{i:\frac{h_i+1}{k_i}=p\right\},\qquad m=|J|.
\]
The expected zero-phase coefficient in
\[
Q_N\sim C\,N^{-p}(\log N)^{m-1}
\]
is
\[
C=
\frac{\Gamma(p/2)}
 {2\beta^{p/2}(m-1)!}
\prod_{i\in J}\frac1{k_i}
\prod_{i\notin J}\frac1{h_i+1-pk_i}.
\]
That is a useful constant audit even if the first unit only treats \(d=2\).

**Second, distinguish “the dictionary is free” from “the general mixed theorem is free.”** General mixed \(d\) follows immediately only if the seabed already exposes the required arbitrary-dimensional mixed asymptotic. Units 52–53 alone, if genuinely restricted to one dominated coordinate in two dimensions, do not establish that. Make this an API inspection, not an assumed deliverable.

## Why (A) is the next substantial programme

(A) offers the largest advance without changing the project’s proof architecture beyond recognition. But I would **gate it on a concrete testing theorem before investing in a general rescaled-measure framework**.

The rescaled measures are
\[
\mu_N(F)=
\frac{N^p}{(\log N)^{m-1}}
\int_{[0,1]^d}
F\!\left(N\prod_i u_i^{k_i},u\right)
\prod_i u_i^{h_i}\,du.
\]

The first gate is convergence for continuous tests with compact support in the \(s\)-variable. Its limiting functional should be
\[
\frac{\prod_{i\in J}k_i^{-1}}{(m-1)!}
\int_{[0,1]^{J^c}}\int_0^\infty
F(s,\iota_J(v))\,s^{p-1}\,ds\,
\prod_{i\notin J}v_i^{h_i-pk_i}\,dv,
\]
where \(\iota_J(v)\) sets precisely the critical coordinates \(J\) to zero.

Two essential points:

- This is naturally **local/vague convergence**, not weak convergence of finite measures with bounded total mass.
- In a mixed chart, concentration is onto a **face**, not necessarily the origin. The limiting phase remains \(\xi(\iota_J(v))\).

Then the remaining programme is:

1. Compact-\(s\) testing / face concentration: **1–3 units**.
2. Uniform integrability near \(s=0\) and Gaussian tail control: **1–2 units**.
3. Extension to
   \[
   F(s,u)=e^{-\beta s^2+\beta s\xi(u)}\eta(u):
   \]
   **1 unit**.
4. Public theorem, constant dictionary, zero-phase cross-check: **1 unit**.

For bounded \(\xi\), the basic domination is uncomplicated:
\[
-\beta s^2+\beta s\xi(u)
\le -\frac{\beta}{2}s^2+\frac{\beta}{2}\|\xi\|_\infty^2.
\]
The hard part is making that domination work uniformly against the rescaled measures.

**Go/no-go criterion:** if compact testing becomes a large measure-theory construction, retreat to a direct integral-testing interface. The deliverable is the leading-term theorem, not an abstract convergence library.

## Positioning (C)

(C) is worthwhile, but label it carefully. In the proposed \(d=1\), \(C^1\)-amplitude model, the derivative term is generally a **new power of \(N\)**—a next-pole correction—not the same-logarithmic-scale \(B\)-slot used in the stochastic theorem.

It is a good restricted second-order theorem. It is not yet a general deterministic `canonB` construction. That distinction matters in the mirror and author report.

## Report policy: keep the frozen report; issue an addendum

**Do not supersede the frozen report now.** It was communicated as a stable artifact at `2503f0a`; preserving that reference is valuable.

Issue a short addendum covering u194–197, based on `39f34d6` **if that remains the reviewed snapshot**, with:

- Headline X: exact stochastic hypotheses, normalisation, and limit;
- the mechanism: identically vanishing leading numerator coefficient plus the existing B-slot remainder;
- Headline XI: signed-reflection reduction and the proved amplitude/parity consequences;
- dictionary and mirror updates;
- explicit scope exclusions: no TaylorTree, general Mellin continuation, or unrestricted second-order expansion.

Wait for review v8 to finish before marking the whole addendum review-clean. There is no need to block drafting.

A consolidated v2 makes sense later, after a substantial block such as (A), or if the authors ask for one document. **Right now, an immutable base report plus a short addendum gives the clearest audit trail—and a clean stopping point.**
