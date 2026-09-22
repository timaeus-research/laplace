## Executive recommendation

1. **First fix the hypotheses:** (G1)–(G3) are not consequences of the record as stated, even in dimension one. The prior and the region being integrated matter.
2. **Rank R1 first for exponent/multiplicity constancy.** Reuse the sublevel-volume machinery, but expose a **data-preserving finite-family readout**, not merely an existential exponent theorem.
3. **Rank a local `d = 1, p = 1` R2 bridge second.** This is a sensible milestone for coefficients and expectations.
4. **Treat general-dimensional leading coefficients as a separate campaign.** The present one-active-variable consumer does not handle normal crossings with several active variables and logarithmic factors.
5. Put the bridge in **greybook**, keeping laplace’s core hironaka-free.

Below, “cheap” means routine once the relevant existing interfaces are available; it does not mean that I have checked an exact Mathlib declaration or built these repositories.

---

## 1. Routes, missing statements, and ranking

### First: the goals need additional hypotheses

A fixed relative modification does **not** make weighted exponents locally constant for every compactly supported nonnegative prior.

Take
\[
f(x,s)=(x-s)^2,\qquad \varphi(x)=x^2\eta(x),
\]
where \(\eta\) is a smooth nonnegative compactly supported cutoff equal to \(1\) near \(0\). The identity modification has perfectly uniform relative coordinates \(u=x-s\), with
\[
k=1,\quad h=0,\quad a=b=1.
\]

Nevertheless, near \(s=0\),
\[
Z_0(t)\sim \frac{\sqrt\pi}{2}t^{-3/2},
\qquad
Z_s(t)\sim \sqrt\pi\,s^2t^{-1/2}\quad(s\ne0).
\]
Thus **(G1) fails on a producer generic set containing \(0\)**. Shrinking the parameter set by deleting \(0\) is an additional operation, not a consequence of constancy on the original `S'`.

Also, (G2) needs regularity of the prior. With the same loss and a continuous compactly supported prior equal to \(1+|x|\) near zero, the leading coefficient is
\[
C(s)=\sqrt\pi(1+|s|),
\]
which is not differentiable at zero.

The useful corrected setting is:

- localization to a fixed compact subset of `V`;
- at least one zero seen by the prior;
- the prior is strictly positive at every zero in its support at the reference parameter;
- continuity for Θ results, and sufficient smoothness for coefficient differentiation.

These conditions exclude support-boundary and amplitude-vanishing transitions.

### R1: the missing finite-family interface

The intermediate statements I would want are:

#### A. `exists_uniform_relativeChartCover_near`

Given:

- a relative modification;
- a compact spatial localization;
- a reference parameter `s₀`;

produce:

- a parameter neighborhood `T` of `s₀`;
- finitely many relative charts based at points of the fibre over `s₀`;
- smaller chart boxes;
- coverage of all relevant lifted zeros for every `s ∈ T`;
- fixed chart data `k i`, `h i`.

**Difficulty: medium.** Properness gives compactness over a compact spatial/parameter block. A finite cover of the reference lifted zero set then extends to a parameter neighborhood by a compactness argument.

Properness is important here: it rules out relevant lifted zeros escaping every chosen chart as `s → s₀`.

#### B. `relativeChartCover.slice_logResolutionData`

Turn that same family into the finite-family input required by the readout, for each `s ∈ T`, with explicit equalities preserving `k` and `h`.

**Difficulty: cheap to medium**, given the fibre specialization already listed. The remaining work is likely domain, coverage, and finite-index packaging rather than new geometry.

#### C. `hasLLCExponentsOn_of_logResolutionData_comb`

The important interface is morally:

```lean
HasLLCExponentsOn μ K F
  (combLam data)
  (combTheta data)
```

with positivity and dimension bounds separately available.

For ordinary centered normal-crossings charts with a positive unit amplitude, the combinatorics are
\[
\lambda_i=\min_{j:k_{ij}>0}\frac{h_{ij}+1}{2k_{ij}},\qquad
\theta_i=\#\left\{j:\frac{h_{ij}+1}{2k_{ij}}=\lambda_i\right\},
\]
followed by
\[
\lambda=\min_i\lambda_i,\qquad
\theta=\max_{\lambda_i=\lambda}\theta_i.
\]

This describes the required mathematical interface; the exact existing definitions may package it differently.

**Difficulty: cheap if the current proof already proves precisely this before existentially packaging it. Otherwise it is a readout refactor, potentially substantial.**

From the information supplied, the answer to “does the readout expose it?” is:

- the reported construction computes the witnesses using `combLam`/`combTheta`;
- the displayed **public existential theorem does not expose that equality**;
- I cannot infer the existence of a reusable public data-preserving theorem from that signature.

An existential API does not make constancy mathematically unprovable. It makes the intended direct argument unavailable through that API. **Reopen the proof or export a stronger theorem.** Uniqueness alone does not relate unrelated witnesses on different fibres.

#### D. `weighted_compact_readout_of_positive_on_zeroSet`

The stated consumer of the current readout concerns unweighted small balls. Your goal concerns a weighted compact localization. You therefore also need:

- finite-cover gluing of sublevel Θ estimates;
- comparison with a prior bounded above and bounded below near the relevant zeros;
- removal of the compact region on which `f ≥ δ > 0`.

**Difficulty: medium, possibly a campaign depending on the existing readout API.** This is a real gap, not merely an Abelian-transfer application.

Finally:

```text
uniform relative cover
→ sliced finite data with fixed combinatorics
→ weighted LLC with fixed (λ, θ)
→ Abelian transfer
→ local constancy, by uniqueness.
```

This route proves **Θ-form exponents**, not a leading coefficient.

### R2: realistic, and no intrinsic manifold measure is necessary

R2 is realistic. The shortest route is to do integration entirely in Euclidean charts, avoiding the construction of a canonical measure on the resolution manifold.

A practical lemma list is:

1. **`sliceChartMap_injective_off_phaseZero`**  
   The coordinate representative of `fibreBlowDown` is injective away from the exceptional zero set, using `isoOff`.

2. **`sliceChartMap_abs_det`**  
   Identify its Jacobian density:
   \[
   |\det DF_s(u)|=|b(u,s)|\prod_j |u_j|^{h_j}.
   \]
   Much of this should be a wrapper around `slice_jacobian`.

3. **`chartZeroSet_volume_zero`**  
   The source exceptional locus in a zero chart lies in a finite union of coordinate hyperplanes. Combine this with the existing target zero-set nullity.

4. **`integral_chart_pushforward_off_zero`**  
   Apply the Euclidean change-of-variables theorem on the chart domain minus the exceptional locus. Remove the null sets afterward.

5. **`exists_local_finite_chart_partition`**  
   A nonnegative smooth finite partition on the relevant compact lifted region, subordinate to chart boxes.

6. **`integral_eq_sum_chartIntegrals_add_remainder`**  
   Sum chartwise identities using the partition. Extend compactly supported coordinate amplitudes by zero.

7. **`remainder_exp_bound`**, and later **`deriv_remainder_exp_bound`**  
   On the remaining compact region, `f ≥ δ`, giving an exponentially small remainder. For differentiation, prove the corresponding derivative estimate, not just the original estimate.

Items 1–3 are comparatively cheap. Items 4–6 are the **measure-theoretic bridge campaign**. Item 7 is routine once localization and regularity are correct.

Crucially, for general `d`, this produces **multi-active monomial integrals**, not the current `RelativeChartDecomposition`.

### Which route gives which goal?

| Goal | R1 | R2 |
|---|---|---|
| Corrected G1 | Best first route | Also possible with positive leading contributions |
| G2 | No: Θ does not determine `C` | Yes, after appropriate leading-asymptotic and differentiation theorems |
| G3 | No | Yes, with numerator/denominator and derivative control |

For G3, pointwise coefficient asymptotics are insufficient to pass to parameter derivatives. For example,
\[
R(s,t)=t^{-\lambda-1}\sin(t^2s)
\]
satisfies `t^λ R(s,t) → 0`, but its parameter derivative at zero does not have the corresponding negligible behavior.

---

## 2. The `d = 1, p = 1` milestone

**Yes: it is a good first milestone.** It isolates the change-of-variables and parameter-localization work without adding multivariate monomial asymptotics.

At a genuine zero-chart center, `k = 0` is impossible in dimension one:
\[
0=f(gP)=a(\phi P)\,0^{2k}
\]
and `a > 0`; for `k=0`, the right side is positive. Thus active zero charts have `k ≥ 1`.

Off-zero regions should go into the exponentially small remainder, rather than being forced into `chartExp`.

Several charts meeting is normal. A partition of unity handles this; summing their contributions does not overcount after weighting.

### The actual decomposition is local in the parameter

For a neighborhood `J` of `s₀`, the expected shape is
\[
Z_s(t)=
\sum_{i:\mathrm{Fin}\,N}
\int_{\mathbb R}
A_i(s,u)|u|^{h_i}e^{-t\,a_i(s,u)u^{2k_i}}\,du
+R(s,t),
\qquad s\in J.
\]

Here:

- `N`, `k i`, and `h i` are fixed on `J`;
- `A_i` contains the pulled-back prior, partition weight, and `|b_i|`;
- each term has compact coordinate support inside its chart;
- `R` comes from a compact region uniformly away from the zero locus.

The record’s closed product box is a **domain-control reserve**, not the integration domain itself. Choose smaller supports strictly inside it and shrink `J` inside its parameter ball.

### Parameter-dependent partition weights are a genuine adapter issue

A partition on the total-space resolution normally has coordinate weights
\[
\psi_i(u,s),
\]
not parameter-independent weights.

You can often fit the existing decomposition by absorbing these weights, and the pulled-back prior, into the parameter-dependent amplitude `b i s`. But then that amplitude:

- may vanish;
- need not be an analytic unit;
- has derivatives containing cutoff and prior terms.

Do not confuse it with the producer’s nowhere-zero Jacobian unit.

Alternatively, add a decomposition interface allowing parameter-dependent cutoffs. That may be cleaner than forcing the current API.

A parameter partition can also be used to construct local weights. It should equal one on the final smaller neighborhood; there is no reason to expect one globally finite family over all of `S'`.

---

## 3. Positivity, identification of λ, and logarithms

### “Positive on V” and compact support are incompatible here

For nonempty open `V ⊆ ℝ^d`, `d > 0`, a function strictly positive everywhere on `V` cannot have compact support contained in `V`.

The useful replacement is:

> The prior is positive on the relevant zero set, and its compact support stays inside `V`.

For a local theorem, it suffices to impose this at the reference parameter and then use compactness and continuity to shrink the parameter neighborhood.

### When is the leading sum positive?

In the one-active-variable setting, yes, provided:

- the coordinate amplitude uses `|b|`, not the signed determinant;
- the prior is positive at an attaining divisor point;
- the partition is nonnegative;
- some partition weight is positive there;
- `λ` is computed from genuinely contributing charts.

The condition `b ≠ 0` alone does not establish positivity if the signed `b` is used in the integral.

Also, **the minimum over an arbitrary chart list is not automatically the weighted exponent**. One can include a low-exponent chart whose amplitude vanishes identically. The chart family/readout must encode contribution or prove it.

With a positive leading limit,
\[
t^\lambda Z_s(t)\longrightarrow C(s)>0,
\]
the decomposition alone identifies the exponent and gives `θ = 1`. The Θ route is unnecessary for that identification.

But specify the domain: this identifies the **weighted/localized RLCT**. It need not equal a purported global RLCT on all of `V`, where other zeros or boundary behavior may matter.

### Where logarithms arise

They arise from **several active coordinates with tied minimal ratios**. For example,
\[
f(x,y)=x^2y^2
\]
on a neighborhood of the origin with positive amplitude gives
\[
Z(t)\asymp t^{-1/2}\log t.
\]

A finite sum of the currently supported pure-power chart asymptotics does not reproduce this mechanism. You need a multivariate monomial leading theorem, or a sector/Mellin-style reduction with its own analysis.

Under the corrected localization and positivity conditions, `θ` is locally constant for the same fixed-combinatorics reason as `λ`: fixed ratios, fixed ties, and persistence of the relevant intersections. Fixed `(k,h)` alone is insufficient if the amplitude ceases to see those intersections.

For general G2, the leading coefficient can involve critical intersections of divisors, not merely an integral over one divisor. Its differentiated formula must also include variation of pulled-back priors and localization weights.

---

## 4. Recommended first bridge theorem

I would first prove a **local weighted Θ theorem in `d = p = 1`**, not a leading-coefficient theorem. It verifies the uniform-cover and readout architecture while avoiding the new change-of-variables campaign.

Here is a Lean-flavoured specification. Names and measure notation are schematic; this is not claimed to compile against the current APIs.

```lean
abbrev X := Fin 1 → ℝ
abbrev Param := Fin 1 → ℝ

/-- Weighted one-dimensional exponents are constant near a parameter
    where the prior is positive at every zero in its support. -/
theorem exists_local_weightedLLC_of_relativeModification
    {f : X → Param → ℝ}
    {V : Opens X} {S' : Opens Param}
    (M : RelativeWatanabeModificationOn f V S')
    (hf_nonneg :
      ∀ x ∈ (V : Set X), ∀ s ∈ (S' : Set Param), 0 ≤ f x s)
    (φ : X → ℝ)
    (hφ_cont : Continuous φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x)
    (hφ_compact : IsCompact (tsupport φ))
    (hφ_support : tsupport φ ⊆ (V : Set X))
    {s₀ : Param}
    (hs₀ : s₀ ∈ (S' : Set Param))
    (hzero :
      ∃ x ∈ tsupport φ, f x s₀ = 0)
    (hφ_pos :
      ∀ x ∈ tsupport φ, f x s₀ = 0 → 0 < φ x) :
    ∃ (λ : ℚ) (T : Opens Param),
      0 < λ ∧
      s₀ ∈ (T : Set Param) ∧
      (T : Set Param) ⊆ (S' : Set Param) ∧
      ∀ s ∈ (T : Set Param),
        HasLLCExponentsOn
          (volume.withDensity (fun x ↦ ENNReal.ofReal (φ x)))
          (V : Set X)
          (fun x ↦ |f x s|)
          λ 1
```

If the record does not expose the continuity needed away from its zero charts, add the ambient analyticity hypothesis already available in the intended application.

A short Abelian-transfer corollary then supplies a common `HasLaplaceTheta` pair `(λ, 1)` on `T`.

### Sublemmas to assign

1. `exists_uniform_relativeChartCover_near`
2. `relativeChartCover.slice_logResolutionData`
3. `combLam_slice_eq`, `combTheta_slice_eq`
4. `hasLLCExponentsOn_of_logResolutionData_comb`
5. `weightedLLC_of_positive_near_zeroSet`
6. `weighted_sublevel_away_zero_eventually_eq_zero`
7. final assembly and Laplace Θ corollary

Require the finite-family readout to retain the formula for `λ` internally, even though the public conclusion existentially packages it.

### Size estimate

Conditional estimates:

- **A few hundred lines** for the fibre/data adapters if the readout already has the required explicit interface.
- **Roughly 1,000–2,500 lines total** for the first weighted local Θ bridge if finite-cover gluing is largely reusable.
- More if the existing readout is tightly specialized to small balls and does not expose its finite-family argument.

For the subsequent one-dimensional R2 bridge, budget **another several-thousand-line campaign**, principally for chartwise integration and partitions. General-dimensional leading coefficients are a separate project, not an incremental adapter.

---

## 5. Repository placement

**Use greybook `Extras/Germbij` as the integration layer.**

Reasons:

- It already connects hironaka to sublevel and Laplace statements.
- R1 requires no dependency on laplace.
- The new bridge is geometric/measure-theoretic integration infrastructure, not part of laplace’s analytic core.
- Keeping laplace hironaka-free preserves a useful dependency boundary.

Suggested split:

```text
hironaka
  relative geometry
  fibre specialization
  explicit finite-family/readout interfaces

laplace
  chart asymptotics
  parameter differentiation
  eventually multi-active monomial asymptotics

greybook/Extras/Germbij
  uniform relative covers
  weighted local Θ bridge
  chartwise change of variables
  adapters to laplace consumers
```

For R2, prefer a **toolchain-aligned laplace dependency in greybook**, without adding hironaka to laplace. Temporarily restating a tiny definition is acceptable, but copying the coefficient and differentiation theory would create unnecessary synchronization work.

Finally, make the pin update, clean build, and axiom audit explicit prerequisites. A sorry-free proof twin is useful evidence, but the bridge should be developed against the audited declarations at the exact producer revision being consumed.