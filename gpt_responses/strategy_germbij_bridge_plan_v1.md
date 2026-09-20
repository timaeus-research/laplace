## Recommendation

**Take route 2: put the forward bridge in `GreyBook/Extras/Germbij/`.** It uses an existing, axiom-clean resolution theorem without disturbing laplace’s dependency graph. The note can legitimately cite two formal developments.

I would not make a toolchain/dependency migration a prerequisite for this mathematical milestone. Revisit route 1 when laplace independently needs the newer toolchain or more resolution results. Route 3 currently buys little beyond another package to maintain.

Suggested files:

```text
GreyBook/Extras/Germbij/ThetaBounds.lean
GreyBook/Extras/Germbij/AbelianTheta.lean
GreyBook/Extras/Germbij/AnalyticLaplace.lean
```

Below, Lean declarations are **proposed interfaces**, not claims about existing Mathlib theorem names. Where greybook already fixes the type of `lam`, preserve its convention; I display real exponents in the transfer layer and rational exponents in the resolution conclusion.

---

# A. The forward bridge

## A1. Statement set

### Predicate

Reuse greybook’s scales rather than introducing another power/log convention.

```lean
def HasLaplaceTheta (Z : ℝ → ℝ) (lam : ℝ) (m : ℕ) : Prop :=
  Z =Θ[Filter.atTop] laplaceScale lam m
```

Here the intended scale is

```lean
fun t : ℝ => Real.rpow t (-lam) * (Real.log t) ^ (m - 1)
```

with **natural-number subtraction and natural-number log power**.

Define the partition function once:

```lean
def laplaceMass
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K : α → ℝ) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-t * K x) ∂μ
```

### Generic norm-to-order conversion

The reusable core should work for arbitrary filters:

```lean
theorem isTheta_iff_eventually_twoSided
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x)
    (hg : ∀ᶠ x in l, 0 ≤ g x) :
    (f =Θ[l] g) ↔
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ᶠ x in l, c₁ * g x ≤ f x ∧ f x ≤ c₂ * g x
```

Nonnegativity is important: `IsTheta` is a norm comparison, not an order comparison.

Then expose two convenient wrappers.

```lean
theorem hasRLCTTheta_iff_small_bounds
    {V : ℝ → ℝ} {lam : ℝ} {m : ℕ}
    (hV : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ V ε) :
    HasRLCTTheta V lam m ↔
      ∃ c₁ c₂ ε₀ : ℝ,
        0 < c₁ ∧ 0 < c₂ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
        ∀ ε, 0 < ε → ε ≤ ε₀ →
          c₁ * powerLogScale lam m ε ≤ V ε ∧
          V ε ≤ c₂ * powerLogScale lam m ε
```

```lean
theorem hasLaplaceTheta_iff_large_bounds
    {Z : ℝ → ℝ} {lam : ℝ} {m : ℕ}
    (hZ : ∀ᶠ t in Filter.atTop, 0 ≤ Z t) :
    HasLaplaceTheta Z lam m ↔
      ∃ C₁ C₂ T : ℝ,
        0 < C₁ ∧ 0 < C₂ ∧ 1 < T ∧
        ∀ t, T ≤ t →
          C₁ * laplaceScale lam m t ≤ Z t ∧
          Z t ≤ C₂ * laplaceScale lam m t
```

These conversions do not need `0 < lam` or `1 ≤ m`; the **transfer theorem does** need the appropriate restrictions.

### Θ transfer

Use greybook’s **strict** sublevel mass throughout:

```lean
theorem hasLaplaceTheta_of_hasRLCTTheta
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (K : α → ℝ)
    (hKmeas : AEMeasurable K μ)
    (hKnonneg : ∀ᵐ x ∂μ, 0 ≤ K x)
    {lam : ℝ} {m : ℕ}
    (hlam : 0 < lam)
    (hm : 1 ≤ m)
    (hV : HasRLCTTheta (sublevelMass μ K) lam m) :
    HasLaplaceTheta (laplaceMass μ K) lam m
```

An a.e.-measurability interface is preferable to global `Measurable K`: the eventual application knows analyticity only near the ball.

If greybook’s existing layer-cake theorem has stronger measurability hypotheses, either generalize that elementary interface or use a measurable representative. Do not silently strengthen the final analytic theorem to global analyticity.

### Analytic composition

For example, take

```lean
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
```

and expose:

```lean
theorem exists_hasLaplaceTheta_closedBall_of_analytic
    {d : ℕ} {K : E d → ℝ} {U : Set (E d)} {w : E d}
    (hU : IsOpen U)
    (hw : w ∈ U)
    (hK : AnalyticOnNhd ℝ K U)
    (hzero : K w = 0)
    (hnonneg : ∀ᶠ x in 𝓝 w, 0 ≤ K x)
    (hnontriv : ¬ (∀ᶠ x in 𝓝 w, K x = 0)) :
    ∃ lam : ℚ, ∃ m : ℕ, ∃ r₀ : ℝ,
      0 < lam ∧ 1 ≤ m ∧ m ≤ d ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        HasLaplaceTheta
          (fun t => ∫ x in Metric.closedBall w r,
            Real.exp (-t * K x))
          (lam : ℝ) m
```

Match the imported RLCT theorem’s actual hypotheses where possible. Shrink its radius to ensure the closed balls lie inside the analytic/nonnegative neighborhood.

**Quantifier discipline:** `lam` and `m` are common to all sufficiently small radii. The Θ constants and eventual threshold may depend on the radius.

---

## A2. Strict sublevels and closed balls

### Do not cross the strict/non-strict bridge unnecessarily

Greybook already provides:

1. strict-sublevel RLCT existence;
2. strict-sublevel layer cake.

Thus the new proof should remain strict from start to finish. Port the *argument* from laplace, not its set convention.

For the lower bound, strictness causes no problem:

\[
Z(t)\ge e^{-1}\mu\{K<1/t\}.
\]

No assertion about the measure of `{K = ε}` is needed.

### Optional compatibility lemma

If useful for later interoperability, prove:

```lean
theorem hasRLCTTheta_strict_iff_nonstrict ...
```

using

\[
F_{\le}(\varepsilon/2)
 \le F_<(\varepsilon)
 \le F_{\le}(\varepsilon)
 \le F_<(2\varepsilon).
\]

Together with fixed-dilation comparability of `powerLogScale`, this proves the equivalence. It does **not** require level sets to have measure zero.

### Closed balls

Use `μ := volume.restrict (closedBall w r)`.

The required facts are:

- the closed ball is measurable;
- its volume is finite;
- `K` is measurable and nonnegative a.e. for this restricted measure;
- restricted-measure sublevel mass agrees with the intersection formulation.

Keep the last item as a small adapter lemma. Check intersection order and the use of `.toReal` versus `Measure.real`; avoid repeatedly unfolding these definitions in the main theorem.

If a global measurable function is required downstream, define a local extension equal to `K` on the ball and zero outside. This is a technical adapter, not an additional mathematical hypothesis.

---

## A3. Transfer proof decomposition and traps

A compact decomposition is:

1. `powerLogScale_pos` for `0 < ε < 1`.
2. `laplaceScale_pos` for `1 < t`.
3. `powerLogScale_fixed_dilation_isTheta`, if compatibility is wanted.
4. The two eventual-bound conversions.
5. A lower Laplace bound from `F(1/t)`.
6. An upper Laplace bound from local power-log bounds.
7. `hasLaplaceTheta_of_hasRLCTTheta`.
8. The analytic composition.

For the upper bound, separate the small-sublevel portion from the tail. Finiteness of `μ` controls the latter exponentially. Reuse greybook’s exponential/polylog integrability machinery for the rescaled integral.

Main traps:

- `ε ^ lam` and `t ^ (-lam)` mean `Real.rpow`; log powers remain `^ (m - 1 : ℕ)`.
- Establish `1 ≤ m` before rewriting an index as `k + 1`.
- On the small side, work below a fixed threshold `< 1`; on the large side, above `1`.
- Rewrite `-log ε` and `log (1/ε)` only under the appropriate positivity assumptions.
- A local asymptotic bound must not be applied to the entire layer-cake integral.
- Do not confuse `atTop` on `ℝ` with an integer or natural parameter.
- State a real-parameter theorem even if an existing lemma happens to call the parameter `n`.

### Precise constants

**The exported Θ conclusion of E5 does not supply a leading constant.** In general, a positive monotone function can be Θ-equivalent to a power-log scale while its quotient by that scale oscillates.

For example, a suitably localized function of the form

\[
\varepsilon^\lambda\bigl(2+\sin(\log\log(1/\varepsilon))\bigr)
\]

is eventually increasing and Θ-equivalent to `ε^λ`, but has no limiting quotient.

For analytic sublevel volumes, a precise leading constant may indeed exist, but that requires more information than the record theorem exports. A partition-of-unity resolution argument with exact transformed densities and controlled overlaps is one route. It is not logically the only route, but **some stronger asymptotic theorem is necessary**. Once `HasPreciseRLCT` is obtained, greybook’s existing precise Abelian theorem should finish the job.

---

# B. Remaining research questions

## Q1. Loss-independent singular sufficient families

There are two distinct questions here.

### 1. The unrestricted family is already loss-independent

“All `ψ · polynomial`, with arbitrary `ψ ∈ C_c^\infty`” contains every test function by taking the polynomial to be `1`. Likewise, a derivative-closed algebra containing every bump is not a genuine reduction.

The existing full-test theorem already gives an unknown-independent family in that sense.

The useful target is a **fixed, explicitly indexed family**, such as monomials times one cutoff.

### 2. A concrete theorem: one cutoff and all monomials at an isolated zero

This is a strong and plausible next theorem, without resolution machinery.

Fix a nonnegative smooth compactly supported cutoff `χ`, equal to `1` near `p`. Assume on its support that

\[
L_1(x)\ge c\lVert x-p\rVert^\nu,\qquad c,\nu>0.
\]

Use the countable family

\[
S=\{\chi(x)(x-p)^\alpha:\alpha\in\mathbb N^d\}.
\]

Then projective superpolynomial agreement on `S` should imply germ equality, under the smoothness/analyticity/common-zero assumptions of the existing theorem.

An abstract interface is:

```lean
theorem normalized_families_force_germ_eq_at_of_cutoff_monomials
    ...
    (hcoercive :
      ∀ x ∈ Function.support χ,
        c * Real.rpow ‖x - p‖ ν ≤ L₁ x)
    (hdata :
      ∀ α : Fin d → ℕ,
        SuperPoly
          (fun t =>
            cutoffMonomialIntegral χ p α L₂ t -
              C t * cutoffMonomialIntegral χ p α L₁ t)) :
    L₁ =ᶠ[𝓝 p] L₂
```

The omitted hypotheses include positivity of `c,ν`, the cutoff properties, and local nonnegativity on its support.

#### Proof mechanism

1. The degree-zero test controls the normalization.
2. The coercive lower bound gives arbitrarily strong decay of sufficiently high radial moments under the `L₁` Gibbs measure.
3. Monomial agreement transfers those radial-moment bounds to the `L₂` measure.
4. Taylor approximation of any fixed smooth test by a polynomial has remainder bounded by a high power of `‖x-p‖`.
5. For each requested decay order, choose a sufficiently high Taylor degree.
6. Recover the full projective test hypothesis locally and invoke the existing theorem.

This avoids the invalid inference “polynomials are dense, therefore superpolynomial agreement extends by density.” **Ordinary density gives no control over asymptotic rates.** The high-moment bounds supply the missing control.

Suggested intermediate interface:

```lean
theorem all_monomial_agreement_implies_smooth_agreement
    ...
    (hconcentration : ...)
    (hmoments : ∀ α, SuperPoly (moment₂ α - moment₁ α)) :
    ∀ f, ContDiff ℝ ∞ f →
      SuperPoly (expectation₂ f - expectation₁ f)
```

First formalize the theorem with the displayed coercivity assumption. Deriving that assumption for an isolated analytic zero is a separate Łojasiewicz task.

**Limitation:** this argument does not cover nonisolated zero sets. Concentration is then toward a set, not toward `p`, so Taylor remainders at `p` need not decay. I would leave the fixed-cutoff, nonisolated case explicitly open rather than claim that the same argument works.

---

## Q2. Finite families and full expansions

I would **not** claim that the current leading-rate kernel theorem answers this question. Nor would I commit to a general recursive reconstruction from finitely many probes without a new argument.

There is, however, a particularly attractive intermediate theorem.

### Two radial observables distinguish a quadratic germ from every nonquadratic analytic germ

Let the reference loss be

\[
L_0(x)=\tfrac12|x|^2,
\]

and let `L` have the same minimum and Hessian. Use a fixed local cutoff in the normalization. Suppose

\[
\begin{aligned}
\langle |x|^2\rangle_{L,t}-d/t&=\operatorname{SuperPoly},\\
\langle |x|^4\rangle_{L,t}-d(d+2)/t^2&=\operatorname{SuperPoly}.
\end{aligned}
\]

Then `L = L₀` near the minimum.

This is **reference rigidity**, not pairwise injectivity among arbitrary analytic losses.

### Why it works

Let `Q_k` be the first nonzero homogeneous perturbation, `k ≥ 3`, and rescale by `q=t^{-1/2}`.

At first order, the radial second-moment data forces

\[
\mathbb E_\gamma Q_k=0.
\]

At order `q^{2k-4}`, write `R=Q_{2k-2}` for the possible higher Taylor term. The two relevant corrections are

\[
\begin{aligned}
A_2 &=
 k\,\mathbb E Q_k^2-(2k-2)\mathbb E R,\\
A_4 &=
 k(2d+2k+2)\mathbb E Q_k^2
 -(2k-2)(2d+2k)\mathbb E R.
\end{aligned}
\]

Consequently,

\[
A_4-(2d+2k)A_2=2k\,\mathbb E Q_k^2.
\]

Vanishing of both coefficients forces `Q_k = 0`, a contradiction.

This directly demonstrates how a leading-rate blind direction becomes visible nonlinearly—and why allowing later Taylor coefficients to compensate does not defeat these two probes at the quadratic reference.

### Cheap formal pieces

Start with Gaussian algebra, independently of the full asymptotic theorem:

```lean
theorem gaussian_cov_radiusSq_homogeneous
    (hQ : HomogeneousPolynomial Q k) :
    gaussianCov radiusSq Q = (k : ℝ) * gaussianMean Q
```

```lean
theorem gaussian_cov_radiusFourth_homogeneous
    (hQ : HomogeneousPolynomial Q k) :
    gaussianCov radiusFourth Q =
      (k : ℝ) * (2 * d + k + 2) * gaussianMean Q
```

Then the coefficient elimination:

```lean
theorem radial_second_order_detects_square
    ...
    (hmean : gaussianMean Q = 0) :
    A₄ - (2 * d + 2 * k) * A₂ =
      2 * k * gaussianMean (fun x => Q x ^ 2)
```

Finally:

```lean
theorem quadratic_germ_rigid_of_two_radial_full_expansions
    ...
    (hsecond : SuperPoly (fun t => localExpectation L radiusSq t - d / t))
    (hfourth :
      SuperPoly (fun t =>
        localExpectation L radiusFourth t - d * (d + 2) / t ^ 2)) :
    L =ᶠ[𝓝 p] quadraticLoss H p
```

For general positive-definite `H`, use `radiusSq x = ⟪x-p, H(x-p)⟫`.

Your cubic example fits this phenomenon. Be explicit about scaling: the `45 ε² q²` correction is for the **rescaled** second moment; the unscaled second moment has the corresponding extra factor `q²`. Also localize or stabilize the cubic loss, since a bare cubic perturbation is not a globally nonnegative confining loss.

The general finite-family pairwise-identifiability problem remains a genuine research question after this theorem.

---

## Q3. Singular recovery: avoid coarea for the first complete result

There are two economical endpoints.

### Endpoint 1: separable monomial losses

For

\[
L(x)=\sum_i a_i x_i^{2k_i},\qquad a_i>0,\quad k_i\ge1,
\]

the fixed `d` observables `x_i²` determine all `k_i,a_i` from their asymptotics:

\[
\langle x_i^2\rangle_t
 =
 \frac{\Gamma(3/(2k_i))}{\Gamma(1/(2k_i))}
 (a_i t)^{-1/k_i}.
\]

Thus superpolynomial agreement of these `d` expectation functions forces equality of the losses.

```lean
theorem separable_monomial_identifiable_of_coordinate_second_moments
    ...
    (hdata :
      ∀ i, SuperPoly
        (fun t => secondMoment a k i t - secondMoment b l i t)) :
    a = b ∧ k = l
```

If the exact weighted moment laws are already close to this interface, this may be the cheapest complete singular identifiability theorem available.

### Endpoint 2: finite sufficient statistics for a known weighted-homogeneous class

For fixed positive rational weights, the monomials of weighted degree `1` form a **finite** set. Write

\[
P_a=\sum_{\alpha\in A}a_\alpha x^\alpha.
\]

The normalized Gibbs expectations of those same monomials determine `P_a`, modulo constants. In the positive weighted-homogeneous class, the constant ambiguity is absent.

This is ordinary finite-dimensional exponential-family identifiability. It needs neither coarea nor Gelfand–Leray forms.

A general lemma is:

```lean
theorem gibbs_identifiable_of_sufficient_moments
    {ι : Type*} [Fintype ι]
    (f : ι → X → ℝ) (a b : ι → ℝ)
    ...
    (hmoments :
      ∀ i, gibbsExpectation μ (energy f a) (f i) =
        gibbsExpectation μ (energy f b) (f i)) :
    ∃ c : ℝ, energy f a - energy f b =ᵐ[μ] fun _ => c
```

Include explicitly the finiteness, positivity, and integrability assumptions needed for the partition functions and energy expectations.

A proof can use nonnegativity and the equality case of symmetric relative entropy. For a smaller foundational footprint, formulate the equivalent strict-monotonicity argument directly with the two positive densities.

Then specialize:

```lean
theorem positive_weightedHomogeneous_eq_of_sufficient_moments
    ...
    (hmoments :
      ∀ α ∈ weightedDegreeOneMonomials weights,
        gibbsMoment P α = gibbsMoment Q α) :
    P = Q
```

Polynomial continuity upgrades a.e. equality to pointwise equality; `P 0 = Q 0 = 0` removes the constant.

Weighted scaling connects these Gibbs moments to leading rescaled expectation coefficients. This gives a complete recovery theorem for the leading polynomial from a **finite family depending only on the known weights**.

### Semi-quasi-homogeneous induction

After that, the next steps are conceptually clean but appreciably larger:

1. positive rational weights imply finitely many monomials below each weighted-degree bound;
2. at each new grade, the unknown correction lies in a finite-dimensional polynomial space;
3. leading discrepancies are covariance pairings against that correction;
4. use all monomials in that grade, giving an injective covariance map modulo constants;
5. induct through the discrete weighted grades;
6. use analyticity to upgrade jet equality to germ equality.

The finite-dimensional Gibbs lemma establishes the leading-model determination; it does not by itself formalize this induction.

### Does E5 help?

Only indirectly.

- A scalar RLCT exponent does **not** determine the weight vector.
- For the separable class, it gives `λ = Σ_i 1/(2k_i)`, losing the individual `k_i`.
- Θ information alone does not recover amplitudes.
- Coordinate-weighted moments can expose individual scaling exponents, but require their own weighted asymptotic statements.

E5 is valuable for the general forward theorem, not a replacement for the recovery machinery.

---

# Priority and value-per-line

| Priority | Item | Assessment |
|---|---|---|
| **1** | **A: greybook Θ bridge** | Highest certainty and immediate note-level payoff; no dependency migration |
| **2** | **Q3: complete separable recovery**, if the moment interfaces are ready | Small closure theorem turning fragments into a complete singular result |
| **3** | **Q3: finite Gibbs sufficient-statistics theorem** | Broad reusable payoff; bypasses coarea for leading-model recovery |
| **4** | **Q2: two-radial-probe quadratic rigidity** | Strong conceptual result; Gaussian algebra is cheap, second-order asymptotic assembly less so |
| **5** | **Q1: cutoff monomials under explicit isolated-zero coercivity** | Meaningful unknown-independent family; requires a careful rate-preserving approximation layer |
| **6** | Full weighted-jet induction | Worthwhile after the leading-model and one-grade interfaces are stable |
| **7** | General finite-family full-expansion injectivity; nonisolated fixed-family sufficiency | Research first, formalization second |

**Suggested next arc:** finish A, close the separable singular theorem, and build the finite Gibbs-identifiability lemma. In parallel, test and formalize the Gaussian coefficient identity behind the two-radial-observable rigidity theorem. That gives one unconditional forward milestone, one complete singular inverse theorem, and one genuinely new clarification of the finite-family question—without claiming that the hardest open questions are already resolved.