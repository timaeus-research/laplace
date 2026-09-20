## Recommendation

Proceed with Milestone 1, but separate it into three layers:

1. **A localized comparison engine**, independent of weighted polynomials.
2. **Weighted polynomial algebra and a certified polynomial comparison step.**
3. **A short induction and a temperature-data adapter.**

Then undertake Milestone 2 in two parts: weighted Taylor algebra first, analytic domination second.

Your mathematical plan is sound, subject to four important corrections:

- **The existing engine cannot directly accept an indicator.** A real-valued `V` cannot encode a zero density outside the cutoff.
- **Use a common cutoff for the first implementation.** Different cutoffs introduce boundary terms that need separate superpolynomial tail estimates.
- **Stage C/D gives equality of polynomial functions, not coefficient equality.** You need a monomial-coefficient uniqueness bridge.
- **Weighted Taylor regrouping does not, by itself, discharge the analytic comparison hypotheses.** Uniform divided-difference domination and the bridge from diagonal Taylor polynomials to full derivative jets remain genuine tasks.

Also, what the proposed comparison argument immediately proves is **uniqueness of recovery**. An explicit reconstruction algorithm needs one additional finite-dimensional covariance-matrix inversion theorem.

All Lean below is architectural pseudocode, not a claim about exact Mathlib identifiers.

---

# 1. Exponents: use integerized weights for the first complete theorem

For the rational-weight development, make the core representation

```lean
structure IntegralWeights (ι : Type*) where
  D : ℕ
  D_pos : 0 < D
  a : ι → ℕ
  a_pos : ∀ i, 0 < a i
```

and define

```lean
def weightDegree (W : IntegralWeights ι) (α : ι → ℕ) : ℕ :=
  ∑ i, W.a i * α i

def realWeights (W : IntegralWeights ι) (i : ι) : ℝ :=
  (W.a i : ℝ) / W.D

def dilation (W : IntegralWeights ι) (ε : ℝ) (u : ι → ℝ) :=
  fun i ↦ ε ^ W.a i * u i
```

The leading polynomial has integer degree `D`. Set

\[
t=\varepsilon^{-D}.
\]

Then

\[
tL(\delta_{1/t}u)
=P(u)+\sum_\alpha c_\alpha
  \varepsilon^{\,\operatorname{wdeg}(\alpha)-D}u^\alpha.
\]

Thus a grade `k > D` uses exactly the existing engine with

```lean
ρ := k - W.D
```

and all induction is ordinary strong induction on `ℕ`.

This is your option **(a), with (c) as an input adapter**. The correction to the wording is: the rates become **integer powers of the new parameter**, not integer multiples of `1/N`.

### Should you generalize the engine anyway?

Yes, but preferably to an arbitrary rate function rather than specifically to `rpow`:

```lean
theorem tendsto_normalized_difference_div_rate
    (r : ℝ → ℝ)
    (hrpos : ∀ᶠ h in 𝓝[>] 0, 0 < r h)
    ...
    (hdiff :
      ∀ᵐ x ∂μ,
        Tendsto (fun h ↦ (V₂ h x - V₁ h x) / r h)
          (𝓝[>] 0) (𝓝 (Q x))) :
    ...
```

The natural-power and real-power versions are then wrappers.

However, this generalization is **not on the critical path** for rational weights.

### Real weights are mathematically legitimate

Positive real weights still give local finiteness:

\[
\ell(\alpha)\le B \implies \alpha_i\le B/q_i.
\]

So rationality is not required for either local finiteness or weighted-jet uniqueness. It merely makes the Lean indexing much easier. Do not advertise the rational-weight theorem as covering arbitrary positive real weights without an additional argument.

---

# 2. First refactor: localize outside the exponential

Keep `Set.indicator`. Do not introduce extended-real potentials.

For a common mask, define something like

```lean
def maskedDensity
    (E : ℝ → Set X) (P : X → ℝ)
    (V : ℝ → X → ℝ) (h : ℝ) : X → ℝ :=
  (E h).indicator (fun x ↦ Real.exp (-(P x + V h x)))

def normalizedKernelMoment
    (K : ℝ → X → ℝ) (A : X → ℝ) (h : ℝ) : ℝ :=
  (∫ x, A x * K h x ∂μ) / ∫ x, K h x ∂μ
```

For weighted localization,

```lean
E ε := {u | W.dilation ε u ∈ U}
```

and assume `U ∈ 𝓝 0`, not merely `0 ∈ U`.

You need the lemma

```lean
theorem eventually_dilation_mem
    (hU : U ∈ 𝓝 (0 : ι → ℝ)) :
    ∀ u, ∀ᶠ ε in 𝓝[>] 0, W.dilation ε u ∈ U
```

This gives the required pointwise limit of the indicators.

## Recommended engine split

The quotient algebra should not know about exponentials at all:

```lean
theorem tendsto_normalizedKernel_difference_div_rate
    (K₁ K₂ : ℝ → X → ℝ) (K₀ : X → ℝ)
    (A Q : X → ℝ) (r : ℝ → ℝ)
    -- limits of numerator and denominator differences:
    (hΔN : Tendsto
      (fun h ↦ ((∫ x, A x * K₂ h x ∂μ) -
                 ∫ x, A x * K₁ h x ∂μ) / r h)
      atZeroRight (𝓝 (-∫ x, A x * Q x * K₀ x ∂μ)))
    (hΔZ : ...)
    (hN₁ : ...)
    (hZ₁ : ...)
    (hZ₂ : ...)
    (hZpos : 0 < ∫ x, K₀ x ∂μ) :
    ...
```

Then provide a localized exponential/DCT wrapper.

This avoids duplicating the delicate normalized quotient proof and makes future cutoff variants much easier.

### Different localization regions

With different `U₁`, `U₂`,

\[
1_{E_2}e^{-E_2^\mathrm{energy}}
-
1_{E_1}e^{-E_1^\mathrm{energy}}
\]

contains a mask-difference term. Eventual pointwise entry does **not** provide domination after division by a small rate.

For Milestone 1, require the same `U`. Later prove that replacing either region by a common smaller neighborhood changes moments superpolynomially. That is a separate tail theorem.

---

# 3. Domination: separate the reference model from the localized perturbation

I would not put all of the following into one large `WeightedLaplaceDomain`.

Use three independent interfaces:

1. Reference integrability and polynomial moments.
2. Localized energy lower bounds.
3. Weighted expansion or remainder information.

## 3.1 Reference integrability interface

For the comparison engine, the most useful reusable conclusion is:

```lean
def HasPolynomialExponentialMoments (P : (ι → ℝ) → ℝ) : Prop :=
  ∀ α : ι → ℕ, ∀ c : ℝ, 0 < c →
    Integrable (fun u ↦
      |mvMonomial α u| * Real.exp (-c * P u))
```

Or use norm powers as the primitive conclusion:

```lean
∀ n : ℕ, ∀ c > 0,
  Integrable (fun u ↦ (1 + ‖u‖) ^ n * Real.exp (-c * P u))
```

Either formulation supplies the integrability needed for products of finitely many monomials.

Keep the geometric theorem constructing this interface separate.

## 3.2 Your scaling argument for exponential moments works

Assuming appropriate measurability, exact quasi-homogeneity, `P ≥ 0`, and `Integrable (exp ∘ (-P))`, scaling gives integrability of

\[
e^{-cP}\qquad(c>0).
\]

Then

\[
(1+P)^N e^{-cP}
\le C_{N,c} e^{-(c/2)P}
\]

gives all the desired polynomial-in-`P` moments.

The measure-map convention deserves care: your `ScalesMeasure` has the inverse Jacobian because it describes a pushforward. The resulting integral identity is indeed

\[
\int e^{-cP(u)}\,du
=c^{-\sum_iq_i}\int e^{-P(u)}\,du.
\]

I would prove **integrability under scaling first**, then the integral identity. This avoids accidentally using an equality of totalized integrals as an integrability argument.

## 3.3 Coercivity

The gauge

\[
g_q(u)=\sum_i |u_i|^{1/q_i}
\]

is appropriate: it satisfies `g_q (δ_s u) = s * g_q u`.

Under

\[
P(u)\ge \kappa g_q(u),
\]

you obtain

\[
|u^\alpha|\le g_q(u)^{\ell(\alpha)}.
\]

But I would not make that exact real-power inequality the engine’s interface. Derive the simpler consequence

```lean
theorem monomial_growth_of_coercive ...
    (α : ι → ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ u, |mvMonomial α u| ≤ C * (1 + P u) ^ N
```

This hides almost all `rpow` manipulation from the rest of the development.

Alternatively, a particularly convenient intermediate interface is coordinate growth:

```lean
∀ i, ∃ C : ℝ, ∃ n : ℕ,
  ∀ u, |u i| ≤ C * (1 + P u) ^ n
```

Products then yield every monomial bound using natural powers alone.

### Positivity away from zero is not enough without regularity

For a **continuous** quasi-homogeneous `P`, positivity on the gauge-unit sphere gives a positive minimum and hence coercivity.

For a merely measurable `P`, pointwise positivity away from zero does not supply that uniform lower bound. Your proposed statement should therefore either:

- assume coercivity directly; or
- assume continuity and strict positivity, and prove coercivity.

## 3.4 The actual divided-difference bound

Suppose both localized energies satisfy

\[
P+V_j\ge cP.
\]

By the mean value theorem for the exponential,

\[
\frac{|e^{-(P+V_2)}-e^{-(P+V_1)}|}{r}
\le
\frac{|V_2-V_1|}{r}\,e^{-cP}
\]

for `r > 0`, on the common cutoff.

After lower coefficients agree, for `0 < ε ≤ 1`,

\[
\frac{|V_2-V_1|}{\varepsilon^{k-D}}
\le
\sum_{\alpha\in S,\ \operatorname{wdeg}\alpha\ge k}
 |c_2(\alpha)-c_1(\alpha)|\,|u^\alpha|.
\]

**The dominating polynomial involves all remaining grades, not just `Qₖ`.**

Multiplying by the observable gives a finite sum of absolute monomial products, covered by the reference interface. This is the main concrete analytic lemma for Milestone 1.

---

# 4. Algebra and induction: make the step theorem substantial and the induction trivial

## 4.1 Finite grade support

Define

```lean
def gradeSupport
    (W : IntegralWeights ι)
    (S : Finset (ι → ℕ)) (k : ℕ) :=
  S.filter (fun α ↦ W.weightDegree α = k)
```

For the later infinite jet, define a full grade finset

```lean
noncomputable def weightedGrade (W : IntegralWeights ι) (k : ℕ) :
    Finset (ι → ℕ) := ...
```

using the fact that `weightDegree α ≤ k` implies `α i ≤ k`, since `a i ≥ 1`.

The key specifications are

```lean
α ∈ W.weightedGrade k ↔ W.weightDegree α = k

α ∈ W.weightedBelow k ↔ W.weightDegree α ≤ k
```

This simultaneously proves local finiteness and handles collisions.

There is no need initially to formalize an abstract finite-dimensional polynomial subspace: the finset is already the finite-dimensional coordinate system the recovery theorem uses.

## 4.2 Add coefficient uniqueness

You need:

```lean
theorem coefficients_zero_of_monomialCombo_eq_zero
    (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hzero : ∀ u, ∑ α ∈ S, c α * mvMonomial α u = 0) :
    ∀ α ∈ S, c α = 0
```

I would prove this through `MvPolynomial`, converting exponent functions to finitely supported exponents. Over `ℝ`, equality of polynomial evaluation functions implies polynomial equality.

Do not try to obtain coefficient equality merely by evaluating at a few obvious points. The `MvPolynomial` bridge is reusable for Milestone 2.

## 4.3 The step theorem

The central theorem should look like:

```lean
theorem coefficients_eq_at_grade_of_lower_eq
    (W : IntegralWeights ι)
    (P : (ι → ℝ) → ℝ)
    (S : Finset (ι → ℕ))
    (c₁ c₂ : (ι → ℕ) → ℝ)
    (k : ℕ)
    (hk : W.D < k)
    (hS : ∀ α ∈ S, W.D < W.weightDegree α)
    (hlower :
      ∀ α ∈ S, W.weightDegree α < k → c₁ α = c₂ α)
    (hreference : ...)
    (hlocalization : ...)
    (hdata :
      ∀ α ∈ gradeSupport W S k,
        Tendsto
          (fun ε ↦
            (rescaledMoment₂ (mvMonomial α) ε -
             rescaledMoment₁ (mvMonomial α) ε) /
            ε ^ (k - W.D))
          atZeroRight (𝓝 0)) :
    ∀ α ∈ gradeSupport W S k, c₁ α = c₂ α
```

Its proof should actually build:

1. `Vⱼ → 0`;
2. the divided correction limit;
3. the divided density domination;
4. the unscaled numerator/partition limits;
5. the covariance limit;
6. grade-function equality;
7. coefficient equality.

A step theorem that merely assumes all of `hlim` from `GradeRecovery` is useful as an intermediate abstraction, but is not yet the substantive polynomial milestone.

## 4.4 Outer induction

For integerized weights:

```lean
have hgrade :
    ∀ k, ∀ α ∈ S,
      W.weightDegree α = k → c₁ α = c₂ α := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro α hα hdeg
      have hk : W.D < k := by
        simpa [hdeg] using hS α hα

      have hlower :
          ∀ β ∈ S, W.weightDegree β < k → c₁ β = c₂ β := by
        intro β hβ hβk
        exact ih (W.weightDegree β) hβk β hβ rfl

      exact coefficients_eq_at_grade_of_lower_eq
        ... hk ... hlower ... α
        (by simp [gradeSupport, hα, hdeg])

exact fun α hα ↦ hgrade (W.weightDegree α) α hα rfl
```

That is the wrapper I recommend.

### If retaining real weights

For finite `S`, either:

- induct on the number of distinct attained degrees below a grade; or
- argue by a minimum-degree nonzero coefficient difference.

The second is probably shortest for finite-polynomial uniqueness. For the infinite jet, positivity of the weights gives finite lower sections, so induction by finite rank is still available. None of this requires a successor operation on arbitrary real numbers.

---

# 5. State the core data assumption at the rescaled level

For the core theorem, use the exact limit needed:

```lean
def SameWeightedGradeRates ... : Prop :=
  ∀ k, W.D < k →
    ∀ α ∈ gradeSupport W S k,
      Tendsto
        (fun ε ↦ ΔRescaledMoment α ε / ε ^ (k - W.D))
        atZeroRight (𝓝 0)
```

This is easier to apply than repeatedly unpacking `IsLittleO`. Provide an `IsLittleO` wrapper if desired.

For the public theorem, use temperature-level `SuperPoly`.

## Important observable rescaling

Let `Mⱼ,α(t)` denote the original localized normalized moment of `x^α`. Then

\[
M_{j,\alpha}(\varepsilon^{-D})
=
\varepsilon^{\operatorname{wdeg}\alpha}
\mathcal M_{j,\alpha}(\varepsilon).
\]

Therefore,

\[
\frac{\Delta\mathcal M_\alpha(\varepsilon)}
     {\varepsilon^{k-D}}
=
\frac{\Delta M_\alpha(\varepsilon^{-D})}
     {\varepsilon^{\operatorname{wdeg}\alpha+k-D}}.
\]

For a support observable at the same grade `k`, the exponent is `2*k - D`.

Thus the temperature adapter must account for the **observable’s scaling degree**, not only the correction’s degree.

`SuperPoly` absorbs this fixed shift. A finite-order data theorem must state the shifted order explicitly.

No exact moment law for the perturbed `L` is needed, but you do need a **change-of-variables identity for the localized perturbed moment**. That identity is distinct from the exact quasi-homogeneous reference moment law.

---

# 6. Milestone 2: feasible, but split algebra from analysis

I agree with the basic reduction to ordinary Taylor bounds, with two qualifications.

## 6.1 The weighted remainder argument

Let `g` be a degree-one weighted gauge. On `g(x) ≤ 1`,

\[
\|x\|\le C g(x)^{q_{\min}}.
\]

An ordinary Taylor remainder of order `M` consequently obeys

\[
|R_M(x)|\le C' g(x)^{Mq_{\min}}.
\]

Choose `M` with `M q_min ≥ ν'`.

However, after truncating by weighted degree, the remainder contains both:

1. the ordinary Taylor remainder;
2. the finitely many ordinary Taylor monomials discarded because their weighted degrees exceed the threshold.

You must bound both. The discarded monomials have degree at least the next weighted grade, so the same gauge estimate applies.

For integerized weights, there is no need to compute the next *attained* degree: after integer grade `k`, use `(k+1)/D`. Empty grades are harmless.

Be explicit about indexing: truncation through ordinary degree `M` normally gives remainder order `M+1`; truncation over `range M` gives remainder order `M`.

## 6.2 Do not initially build multi-index differentiation

Use the existing word expansion to construct ordinary Taylor polynomials as `MvPolynomial`s.

Schematically:

```lean
noncomputable def taylorPolynomial
    (L : (ι → ℝ) → ℝ) (n : ℕ) : MvPolynomial ι ℝ :=
  ∑ m : Fin n → ι,
    MvPolynomial.C
      (((n.factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ n L 0 (fun j ↦ basisVector (m j))) *
      ∏ j, MvPolynomial.X (m j)
```

Its evaluation is the ordinary homogeneous Taylor term.

Then define the canonical coefficient of exponent `α` by taking the coefficient in ordinary degree `∑ i, α i`:

```lean
def weightedTaylorCoeff (L) (α : ι → ℕ) : ℝ :=
  (taylorPolynomial L (∑ i, α i)).coeff (toFinsupp α)
```

Finally,

```lean
def weightedTaylorComponent (W) (L) (k : ℕ) :
    MvPolynomial ι ℝ :=
  ∑ α ∈ W.weightedGrade k,
    MvPolynomial.monomial (toFinsupp α) (weightedTaylorCoeff L α)
```

This avoids formalizing the formula `∂^α L / α!` at the outset. That formula can be a later theorem, not the definition.

## 6.3 Two bridges remain

### Analytic comparison bridge

You still need uniform estimates for

\[
\frac{V_2(\varepsilon,u)-V_1(\varepsilon,u)}
     {\varepsilon^{k-D}}
\]

on the moving domain.

If Taylor bounds hold throughout the chosen fixed `U`, the gauge remainder estimate supplies polynomial growth in `u`. If bounds hold only on a smaller ball, split into:

- the Taylor region;
- an exterior region controlled by superpolynomial tails.

This is analysis beyond finite weighted regrouping.

### Full derivative-jet bridge

Your existing analytic theorem expects equality of `iteratedFDeriv`, not merely equality of diagonal Taylor polynomials.

You need either:

- a symmetric-multilinear diagonal-extensionality/polarization bridge; or
- a direct analytic germ theorem from equality of all homogeneous Taylor polynomial functions.

Do not silently conflate these.

If the existing theorem is Euclidean-space-specific, also isolate the transport between `ι → ℝ` and the appropriate finite-dimensional Euclidean model.

## Where I would stop

I would merge Milestone 1 first. Then implement the **weighted Taylor polynomial and regrouping API** before committing to the all-orders localized analytic theorem.

That algebraic API is independently valuable and exposes whether the remaining obstacle is the analytic remainder package or the derivative-jet bridge.

---

# 7. Ranked lemma list and estimated retained line counts

These are rough retained-code estimates, including useful helper lemmas but excluding exploratory code. Exact counts depend strongly on how much quotient algebra and polynomial evaluation infrastructure can be reused.

| Priority | Lemma/module | Main statement | Estimated lines |
|---|---|---|---:|
| 1 | `WeightedDegree.lean` | Integerized weights, degree additivity, dilation of monomials, finite lower sections and grade finsets | 100–180 |
| 2 | `monomialCombo_coefficients_unique` | Vanishing finite monomial combination implies all support coefficients vanish, via `MvPolynomial` | 80–160 |
| 3 | `tendsto_normalizedKernel_difference_div_rate` | Quotient comparison independent of exponential form; existing engine becomes a wrapper | 60–130 |
| 4 | `LocalizedGradeComparison.lean` | Common-mask exponential comparison, eventual entry, masked DCT hypotheses | 130–230 |
| 5 | `WeightedReferenceMoments.lean` | Scaling integrability; polynomial-in-`P` exponential integrability; monomial growth from coercivity | 180–330 |
| 6 | `weightedPolynomial_difference_div_pow` | Lower coefficients equal ⇒ pointwise leading-grade limit and uniform polynomial bound | 100–180 |
| 7 | `weightedPolynomial_comparison_limits` | Build all localized one-grade hypotheses from polynomial expansion and lower bounds | 120–220 |
| 8 | `coefficients_eq_at_grade_of_lower_eq` | Apply covariance recovery and coefficient uniqueness | 40–80 |
| 9 | `weightedPolynomial_coefficients_eq_of_rates` | Strong induction on integer weighted degree | 25–50 |
| 10 | `weightedPolynomial_coefficients_eq_of_superPoly` | Localized change of variables and observable-rate shift | 100–180 |
| 11 | Rational-weight adapter | Positive rational weights ⇒ common integer denominator representation | 40–90 |
| 12 | Optional `recover_grade_by_covarianceMatrix` | Positive-definite covariance matrix on a positive-degree monomial basis ⇒ unique linear reconstruction | 100–220 |

A realistic Milestone 1 budget is roughly **1,100–1,900 retained lines**, rather than “the induction is ten lines.” The induction really is short; localization, domination, and coefficient extraction are the work.

For Milestone 2:

| Priority | Lemma/module | Main statement | Estimated lines |
|---|---|---|---:|
| 13 | `WeightedTaylorPolynomial.lean` | Word-based Taylor polynomial, coefficients, weighted projection, evaluation/regrouping | 200–350 |
| 14 | `weightedTaylor_remainder_bound` | Ordinary remainder plus discarded monomials ⇒ weighted remainder | 150–280 |
| 15 | `weightedTaylor_comparison_limits` | Weighted bounds ⇒ localized all-grade comparison certificates | 180–350 |
| 16 | `weightedJet_eq_of_rates` | All-order strong induction, assuming common leading weighted jet | 40–80 |
| 17 | `iteratedFDeriv_eq_of_weightedJet_eq` | Coefficient equality ⇒ ordinary Taylor equality ⇒ full derivative equality | 100–250 |
| 18 | `analytic_germ_eq_of_weighted_data` | Apply the existing analytic germ theorem, modulo constants | 25–70 |
| Separate | `localizedMoments_superPoly_of_cutoff_change` | Different admissible cutoffs give the same asymptotic data | 150–300 |

I would keep cutoff independence separate from the first successful theorem.

---

# 8. Sanity checks and precise scope

### Constants are invisible

Normalized expectations do not recover `L(0)` or any additive constant. State the analytic conclusion for

```lean
L₁ x - L₁ 0 = L₂ x - L₂ 0
```

near zero, unless both energies are normalized in advance.

### Only the grade-support observables are needed

At grade `k`, the monomials in that grade supporting the candidate discrepancy suffice. You do not need every observable of degree `≤ k`.

For a candidate-independent analytic statement, use the entire finite `weightedGrade k`.

### Odd terms and collisions cause no obstruction

The covariance form is positive definite on the finite span of positive-degree monomials: zero variance gives a constant, and evaluation at zero removes the constant. Collisions simply enlarge this finite span.

Observable-degree collisions with correction degrees do not alter the covariance argument. They only affect the conversion between physical and rescaled rates.

### The same reference model is essential to this phase

Your theorem assumes the leading model and weights have already been identified. The analytic package must also say that all weighted terms below the leading degree vanish and that the leading component is the common `P`.

### Analyticity really is needed only for germ equality

Smooth functions can differ by a nonzero flat perturbation while having the same full Taylor jet and beyond-all-orders differences in suitably controlled localized moments. Thus smooth jet recovery is the correct intermediate conclusion; smooth germ recovery would be false.

### Constructive recovery versus uniqueness

The comparison proof establishes injectivity without explicitly calculating the nonlinear contributions of lower grades. That is an excellent first formal target.

For actual grade-by-grade reconstruction, prove separately that the covariance matrix on each positive-degree monomial basis is invertible, then solve the linear system whose right-hand side is the measured coefficient after known lower-order contributions are removed.

---

## Bottom line

**Keep the integer-grade induction simple and put the effort into a reusable masked comparison engine.** Use a common cutoff, derive domination from a separate reference-moment interface, and add the missing polynomial coefficient-uniqueness bridge early.

After that, Milestone 1 is a clean, substantive theorem. Milestone 2 is feasible, but its remaining work is not merely regrouping: it includes uniform weighted remainder domination and an explicit bridge from recovered polynomial coefficients to the derivative jet expected by your analytic germ theorem.