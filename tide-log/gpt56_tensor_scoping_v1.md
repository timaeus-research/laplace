## 1. Recommended programme

I would separate the programme into eight stages, `J0`–`J7`. The main genuinely multivariate additions are `J1`–`J3`; the Taylor, DCT, and induction architecture should closely parallel the 1D smooth-germ development.

Throughout, use

```lean
abbrev EuclidD (d : ℕ) := Fin d → ℝ
abbrev AtZeroPlus := 𝓝[Set.Ioi (0 : ℝ)] 0
```

and initially represent a degree-\(k\) term by a function `Q : EuclidD d → ℝ` with certificates, not by `MvPolynomial`.

A convenient normalized quadratic-Gaussian expectation is

```lean
noncomputable def gaussianExpectation
    (H : Matrix (Fin d) (Fin d) ℝ) (f : EuclidD d → ℝ) : ℝ :=
  (∫ x, f x * quadKernel H x) / ∫ x, quadKernel H x

noncomputable def gaussianCovariance
    (H : Matrix (Fin d) (Fin d) ℝ)
    (f g : EuclidD d → ℝ) : ℝ :=
  gaussianExpectation H (fun x => f x * g x) -
    gaussianExpectation H f * gaussianExpectation H g
```

A probability measure could be introduced later, but weighted integrals will initially fit the existing seabed better.

---

### J0. Polynomial-growth integrability adapter

#### Purpose

Package the existing norm-moment estimates into a reusable API:

> every measurable function of polynomial growth is integrable against `quadKernel H`.

You do **not** need monomial-moment formulas. In particular, no `MvPolynomial` or multi-index enumeration is needed for the analytic argument.

A minimal certificate is:

```lean
def HasPolynomialGrowth (f : EuclidD d → ℝ) : Prop :=
  ∃ C : ℝ, ∃ n : ℕ, 0 ≤ C ∧
    ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ n)
```

#### Minimal statements

```lean
theorem integrable_mul_quadKernel_of_polynomialGrowth
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {f : EuclidD d → ℝ}
    (hf_meas : AEStronglyMeasurable f)
    (hf_growth : HasPolynomialGrowth f) :
    Integrable (fun x => f x * quadKernel H x)
```

and closure lemmas:

```lean
theorem HasPolynomialGrowth.add
theorem HasPolynomialGrowth.mul
theorem HasPolynomialGrowth.const
theorem HasPolynomialGrowth.norm_pow
```

For continuous multilinear diagonal forms:

```lean
theorem ContinuousMultilinearMap.hasPolynomialGrowth_diag
    (A : EuclidD d [×k]→L[ℝ] ℝ) :
    HasPolynomialGrowth (fun x => A (fun _ => x))
```

#### Load-bearing Mathlib API

- `Continuous.aestronglyMeasurable`
- `AEStronglyMeasurable.mul`
- `Integrable.mono'`
- `ContinuousMultilinearMap.le_opNorm`
- `norm_mul`
- `pow_add`
- existing `quadKernel_integrable` and norm-power integrability theorem

#### Likely mismatch

The current theorem named `quadKernel_integrable_pow` should be checked carefully: if it means powers of the **kernel**, rather than `‖x‖ ^ n * quadKernel H x`, first add the actual norm-moment theorem by whitening from `stdKernel_integrable_pow`.

No monomial-specific theorem is needed. Abstract continuous `P,Q` of polynomial growth suffice because only the integrals of `P`, `Q`, `P*Q`, and `Q^2` occur.

---

### J1. Positive Gaussian density and continuous rigidity

#### Purpose

Prove the full-support fact in the exact form needed later:

> a continuous nonnegative function with zero quadratic-Gaussian integral vanishes everywhere.

This is preferable to committing immediately to Mathlib’s support/probability-measure API.

#### Minimal statement

```lean
theorem continuous_eq_zero_of_integral_mul_quadKernel_eq_zero
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {f : EuclidD d → ℝ}
    (hf_cont : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : Integrable (fun x => f x * quadKernel H x))
    (hzero : ∫ x, f x * quadKernel H x = 0) :
    f = 0
```

A useful square-specialization is:

```lean
theorem continuous_eq_const_of_integral_sq_mul_quadKernel_eq_zero
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {f : EuclidD d → ℝ} {c : ℝ}
    (hf : Continuous f)
    (hint : Integrable (fun x => (f x - c)^2 * quadKernel H x))
    (hzero : ∫ x, (f x - c)^2 * quadKernel H x = 0) :
    f = fun _ => c
```

#### Proof shape

If `f x₀ > 0`, continuity gives a ball on which `f ≥ ε`. Since `quadKernel H` is continuous and pointwise positive, possibly shrink the ball so that `quadKernel H ≥ δ`. The integral over that ball is then positive, contradicting `hzero`.

This proves exactly the needed “full support” result without first constructing a normalized measure.

#### Load-bearing Mathlib API

Stable names likely to be useful:

- `quadKernel_pos`
- `quadKernel_continuous`
- `Continuous.isOpen_preimage`
- `Metric.isOpen_ball`
- `MeasureTheory.integral_mono_measure`
- `MeasureTheory.integral_pos_iff_support_of_nonneg` if its hypotheses fit
- positivity of volume on nonempty open sets / balls

The broader API may involve:

- `Measure.IsOpenPosMeasure`
- `Measure.IsFull`
- `MeasureTheory.Measure.withDensity`

#### Likely mismatch

The exact namespace and instance names around “every nonempty open set has positive volume” are historically somewhat awkward. A direct ball argument is likely more stable than proving that the normalized Gaussian measure has `support = Set.univ`.

Also, `integral_eq_zero_iff_of_nonneg_ae` only gives an a.e. conclusion. One still needs continuity plus full support to upgrade it to pointwise equality.

---

### J2. Variance rigidity and covariance-Gram injectivity

#### Purpose

Establish the analytic heart of the pairwise-difference route, independently of Taylor expansions and posterior data.

#### Minimal variance statement

```lean
theorem gaussianCovariance_self_eq_zero_iff
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {Q : EuclidD d → ℝ}
    (hQ_cont : Continuous Q)
    (hQ_growth : HasPolynomialGrowth Q) :
    gaussianCovariance H Q Q = 0 ↔
      ∃ c : ℝ, Q = fun _ => c
```

The forward direction is the important one. Algebraically rewrite covariance as

\[
E[(Q-EQ)^2].
\]

The denominator is positive by `integral_quadKernel_pos`.

For positive-degree homogeneous functions:

```lean
def IsHomogeneousOfDegree (k : ℕ) (Q : EuclidD d → ℝ) : Prop :=
  ∀ (a : ℝ) (x : EuclidD d), Q (a • x) = a ^ k * Q x
```

```lean
theorem eq_zero_of_gaussianCovariance_self_eq_zero
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {k : ℕ} (hk : 0 < k)
    {Q : EuclidD d → ℝ}
    (hQ_cont : Continuous Q)
    (hQ_growth : HasPolynomialGrowth Q)
    (hQ_hom : IsHomogeneousOfDegree k Q)
    (hvar : gaussianCovariance H Q Q = 0) :
    Q = 0
```

Then the abstract Gram-injectivity lemma is almost immediate:

```lean
theorem eq_zero_of_covariance_vanishes_on_homogeneous_tests
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {k : ℕ} (hk : 0 < k)
    {Q : EuclidD d → ℝ}
    (hQ_cont : Continuous Q)
    (hQ_growth : HasPolynomialGrowth Q)
    (hQ_hom : IsHomogeneousOfDegree k Q)
    (hcov :
      ∀ P : EuclidD d → ℝ,
        Continuous P →
        HasPolynomialGrowth P →
        IsHomogeneousOfDegree k P →
        gaussianCovariance H P Q = 0) :
    Q = 0
```

The proof instantiates `P := Q`.

An even more minimal downstream interface is simply:

```lean
theorem homogeneous_eq_zero_of_self_covariance_eq_zero ...
```

because the recovery theorem can choose the test `P = Q` directly.

#### Load-bearing Mathlib API

- `integral_quadKernel_pos`
- `field_simp` or `div_eq_iff`
- `ring_nf`
- `integral_add`, `integral_sub`, `integral_const_mul`
- J0 and J1

#### Likely mismatch

Mathlib’s existing probability `variance` API may require a probability measure and `MemLp` hypotheses and may not simplify well for the weighted-integral representation. Proving the square identity locally is probably shorter than adapting that API.

---

### J3. Diagonal homogeneous forms determine symmetric multilinear forms

#### Purpose

Variance rigidity recovers the diagonal function

```lean
fun x => A (fun _ => x)
```

where `A` is the difference of the \(k\)-th derivatives. To recover the actual Taylor tensor, one needs:

> a symmetric \(k\)-linear form over `ℝ` is determined by its diagonal.

This is genuinely new compared with 1D.

#### Minimal statement

Depending on the symmetry API used for `iteratedFDeriv`, aim for:

```lean
theorem ContinuousMultilinearMap.eq_zero_of_diag_eq_zero
    (A : EuclidD d [×k]→L[ℝ] ℝ)
    (hA_symm : A.IsSymm)
    (hdiag : ∀ x, A (fun _ => x) = 0) :
    A = 0
```

or directly:

```lean
theorem iteratedFDeriv_eq_of_diag_eq
    {L₁ L₂ : EuclidD d → ℝ}
    (h₁ : ContDiff ℝ k L₁)
    (h₂ : ContDiff ℝ k L₂)
    (hdiag :
      ∀ x,
        iteratedFDeriv ℝ k L₁ 0 (fun _ => x) =
        iteratedFDeriv ℝ k L₂ 0 (fun _ => x)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0
```

#### Proof route

Use the real polarization identity. Avoid coordinates and monomials. A finite-difference version over subsets of `Fin k` is likely the easiest Lean proof:

\[
k!\,A(x_1,\dots,x_k)
=
\sum_{S\subseteq\{1,\dots,k\}}
(-1)^{k-|S|}
A\!\left(\sum_{i\in S}x_i,\ldots,\sum_{i\in S}x_i\right).
\]

#### Load-bearing Mathlib API

- `ContinuousMultilinearMap`
- `iteratedFDeriv`
- symmetry of iterated derivatives, likely in the `ContDiff`/Schwarz theorem API
- `Finset.powerset`
- `Finset.sum_bij`
- `Nat.factorial_ne_zero`
- multilinear expansion over finite sums

#### Likely mismatch

There may be no ready-made theorem named `ContinuousMultilinearMap.eq_of_diag_eq`. Expect this stage to require a local polarization lemma.

The precise symmetry predicate for a `ContinuousMultilinearMap` should be inspected before fixing the public signature. Mathlib has changed parts of this API between releases.

---

### J4. \(k\)-th radial Taylor coefficient

#### Purpose

Generalize the existing quadratic/ray-rescaling work to arbitrary degree.

Define the diagonal Taylor term:

```lean
noncomputable def taylorHomogeneousTerm
    (k : ℕ) (L : EuclidD d → ℝ) : EuclidD d → ℝ :=
  fun x =>
    (k.factorial : ℝ)⁻¹ *
      iteratedFDeriv ℝ k L 0 (fun _ => x)
```

For the cubic milestone:

```lean
noncomputable def cubicTerm
    (L : EuclidD d → ℝ) : EuclidD d → ℝ :=
  taylorHomogeneousTerm 3 L
```

#### Minimal pointwise cubic statement

```lean
theorem rescaled_loss_cubic_tendsto
    {L : EuclidD d → ℝ}
    (hL : ContDiff ℝ 3 L)
    (hgrad : fderiv ℝ L 0 = 0) :
    ∀ x,
      Tendsto
        (fun q =>
          (((L (q • x) - L 0) / q^2) -
              (2 : ℝ)⁻¹ * hess L x x) / q)
        AtZeroPlus
        (𝓝 (cubicTerm L x))
```

More robustly, formulate the unscaled Peano statement:

```lean
theorem taylor_peano_diag
    {L : EuclidD d → ℝ}
    (hL : ContDiff ℝ k L) :
    (fun x =>
      L x -
        ∑ j ∈ Finset.range (k + 1),
          taylorHomogeneousTerm j L x)
      =o[𝓝 0] fun x => ‖x‖ ^ k
```

The exact indexing should avoid claiming an order-\(k\) remainder after including the \(k\)-th term unless the available regularity supports that formulation. For coefficient extraction, it is often cleaner to compare two losses whose derivatives agree below \(k\):

```lean
theorem pairwise_rescaled_loss_tendsto
    {L₁ L₂ : EuclidD d → ℝ}
    (hL₁ : ContDiff ℝ k L₁)
    (hL₂ : ContDiff ℝ k L₂)
    (hlower :
      ∀ j < k,
        iteratedFDeriv ℝ j L₁ 0 =
        iteratedFDeriv ℝ j L₂ 0) :
    ∀ x,
      Tendsto
        (fun q =>
          ((L₁ (q • x) - L₁ 0) -
             (L₂ (q • x) - L₂ 0)) / q^k)
        AtZeroPlus
        (𝓝
          (taylorHomogeneousTerm k L₁ x -
           taylorHomogeneousTerm k L₂ x))
```

#### Load-bearing Mathlib API

- `iteratedFDeriv`
- `ContDiff`
- `HasFDerivAt`
- `Filter.IsLittleO`
- Taylor/Peano remainder API, likely involving names around:
  - `ContDiff.taylor_mean_remainder`
  - `HasFTaylorSeriesUpTo`
  - `ContDiff.iteratedFDeriv`
- existing `ray_taylor_eval`, `quadratic_peano`, and ray derivative machinery

#### Likely mismatch

Mathlib’s finite-dimensional Fréchet Taylor API is less ergonomic than its one-variable API. Reusing the existing “restrict to the ray `t ↦ t • x`” method may be substantially easier than proving a fully multivariate Taylor theorem.

A ray proof naturally produces the diagonal derivative, which is exactly what the covariance argument needs.

---

### J5. Rate-sensitive pairwise exponential/DCT lemma

#### Purpose

Turn the pointwise difference of Taylor expansions into the normalized-moment asymptotic

\[
\frac{E_{1,q}[P]-E_{2,q}[P]}{q^{k-2}}
\longrightarrow
-\operatorname{Cov}_{\gamma_H}(P,Q).
\]

This is the main analytic stage after J4.

Let `rescaledPosteriorMoment` denote the ratio already implicit in `posteriorIntegral`, after the substitution `x = qy`:

```lean
noncomputable def rescaledPosteriorMoment
    (A : LocalLaplaceDomain L H)
    (P : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  posteriorIntegral A P q / posteriorIntegral A 1 q
```

The exact definition should reuse `posteriorIntegral`.

#### Minimal statement

```lean
theorem tendsto_pairwise_normalized_moment_difference
    {k : ℕ} (hk : 2 < k)
    {L₁ L₂ : EuclidD d → ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ}
    (A₁ : HigherLaplaceDomain k L₁ H)
    (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower :
      ∀ j < k,
        iteratedFDeriv ℝ j L₁ 0 =
        iteratedFDeriv ℝ j L₂ 0)
    {P : EuclidD d → ℝ}
    (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Tendsto
      (fun q =>
        (rescaledPosteriorMoment A₁ P q -
           rescaledPosteriorMoment A₂ P q) / q^(k - 2))
      AtZeroPlus
      (𝓝
        (-gaussianCovariance H P
          (fun x =>
            taylorHomogeneousTerm k L₁ x -
            taylorHomogeneousTerm k L₂ x)))
```

This is the correct pairwise theorem to feed to covariance injectivity.

#### Important structural issue

`LocalLaplaceDomain` may not be strong enough for a **rate-divided** DCT. Ordinary convergence only needs a fixed Gaussian dominator. After division by `q^(k-2)`, one must control the difference quotient uniformly.

A likely new structure is:

```lean
structure HigherLaplaceDomain
    (k : ℕ) (L : EuclidD d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ)
    extends LocalLaplaceDomain L H where
  contDiff_k : ContDiff ℝ k L
  local_iteratedFDeriv_bound : ...
  tail_gap : ...
```

The exact extra assumptions should be dictated by the 1D smooth-germ structure. Typically one needs:

1. bounded \(k\)-th derivatives on a fixed neighborhood of zero;
2. the existing local quadratic lower bound;
3. a strict tail gap or equivalent bound giving errors exponentially small in `q⁻²`.

#### Load-bearing Mathlib API

- `Real.exp_sub`
- `Real.exp_neg`
- mean-value bounds for `exp`, or the identity
  \[
  e^{-a}-e^{-b}=-(a-b)\int_0^1 e^{-((1-t)b+ta)}dt;
  \]
- `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
- `MeasureTheory.Integrable`
- existing:
  - `tendsto_integral_rescaled`
  - `integrable_one_add_sq_mul_exp`
  - `quadKernel_integrable`
  - `integral_comp_whitening`

#### Likely mismatch

The ordinary DCT used in `RescaledDCT.lean` probably cannot simply be applied after dividing by `q^(k-2)`. The proof will likely need a local/tail split:

```lean
Metric.ball 0 (δ / q)
```

or, before rescaling, a fixed neighborhood of the origin. The tail must be shown to be `o(q^N)` for every fixed `N`, using exponential decay.

This is probably the largest stage.

---

### J6. Recovery of one degree

#### Purpose

Combine J2, J3, and J5.

#### Minimal theorem using rescaled data

```lean
theorem iteratedFDeriv_recovery_of_moment_rates
    {k : ℕ} (hk : 2 < k)
    {L₁ L₂ : EuclidD d → ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ}
    (A₁ : HigherLaplaceDomain k L₁ H)
    (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower :
      ∀ j < k,
        iteratedFDeriv ℝ j L₁ 0 =
        iteratedFDeriv ℝ j L₂ 0)
    (hdata :
      ∀ P : EuclidD d → ℝ,
        Continuous P →
        HasPolynomialGrowth P →
        IsHomogeneousOfDegree k P →
        (fun q =>
          rescaledPosteriorMoment A₁ P q -
          rescaledPosteriorMoment A₂ P q)
          =o[AtZeroPlus] (fun q => q^(k - 2))) :
    iteratedFDeriv ℝ k L₁ 0 =
      iteratedFDeriv ℝ k L₂ 0
```

Proof:

1. Let
   ```lean
   Q x := taylorHomogeneousTerm k L₁ x -
          taylorHomogeneousTerm k L₂ x
   ```
2. J5 gives the quotient limit `-Cov(P,Q)`.
3. `hdata` gives quotient limit `0`.
4. Uniqueness of limits gives `Cov(P,Q)=0`.
5. Choose `P=Q`.
6. J2 gives `Q=0`.
7. J3 gives equality of the symmetric \(k\)-linear derivatives.

A smaller data interface is possible:

```lean
(hdata :
  let Q := ...
  (fun q =>
    rescaledPosteriorMoment A₁ Q q -
    rescaledPosteriorMoment A₂ Q q)
    =o[AtZeroPlus] (fun q => q^(k - 2)))
```

but this is unsuitable as an observational theorem because the test `Q` depends on the unknown losses. The public recovery theorem should quantify over a sufficiently rich test family.

#### Finite test families

Eventually replace “all homogeneous `P`” by a basis of degree-\(k\) homogeneous polynomials. That is the point where `MvPolynomial` and multi-indices become useful, but not before.

---

### J7. Induction over \(k\) and smooth-jet recovery

#### Purpose

Iterate J6 after `hessian_recovery`.

#### Finite-order statement

```lean
theorem finite_jet_recovery
    {N : ℕ} (hN : 2 ≤ N)
    {L₁ L₂ : EuclidD d → ℝ}
    (A₁ : HigherLaplaceDomain N L₁ H)
    (A₂ : HigherLaplaceDomain N L₂ H)
    (hHdata : /* covariance data recovering degree 2 */)
    (hdata :
      ∀ k, 3 ≤ k → k ≤ N →
      ∀ P,
        Continuous P →
        HasPolynomialGrowth P →
        IsHomogeneousOfDegree k P →
        momentDifference A₁ A₂ P
          =o[AtZeroPlus] (fun q => q^(k - 2))) :
    ∀ k ≤ N,
      iteratedFDeriv ℝ k L₁ 0 =
      iteratedFDeriv ℝ k L₂ 0
```

#### Infinite smooth-jet statement

```lean
theorem smooth_jet_recovery
    {L₁ L₂ : EuclidD d → ℝ}
    (hL₁ : ContDiff ℝ ∞ L₁)
    (hL₂ : ContDiff ℝ ∞ L₂)
    (hdata : ∀ k ≥ 2, /* degree-k rate data */) :
    ∀ k,
      iteratedFDeriv ℝ k L₁ 0 =
      iteratedFDeriv ℝ k L₂ 0
```

This recovers equality of all Taylor jets, not equality of smooth germs as functions. Equality of germs from equality of all derivatives would require analyticity or a quasianalytic hypothesis.

#### Load-bearing Mathlib API

- `Nat.rec`, strong induction via `Nat.strong_induction_on`
- `Nat.cast_pow`
- `Filter.IsLittleO`
- `tendsto_nhds_unique`
- J6 and existing `hessian_recovery`

#### Likely mismatch

A structure parameterized by a natural `N` may be much easier than trying to use `ContDiff ℝ ∞` uniformly inside all rate proofs. Prove finite-order recovery first; quantify over `N` only in the final wrapper.

---

## 2. Direct 1D analogues versus genuinely new work

### Direct multivariate analogues of the 1D programme

1. Raywise Taylor/Peano expansion.
2. Rescaled-loss asymptotics.
3. Expansion of exponentials under an integral.
4. Normalization producing a covariance term.
5. Pairwise comparison after lower jets have already been matched.
6. Induction on the first unknown degree.
7. Use of `IsLittleO` to express observational matching at the required rate.
8. Local/tail decomposition for rate-sensitive Laplace asymptotics.

These should reuse the conceptual structure of the 1D smooth-germ development.

### Genuinely multivariate stages

1. Gaussian full-support rigidity on `EuclidD d`.
2. Covariance-Gram injectivity without explicit moment matrices.
3. Polynomial-growth integrability for abstract test functions.
4. Symmetric multilinear polarization: diagonal recovery implies tensor recovery.
5. Later, choosing a finite basis of homogeneous test polynomials.
6. If desired, conversion between:
   - symmetric multilinear forms,
   - diagonal homogeneous functions,
   - `MvPolynomial` homogeneous components,
   - coefficient arrays indexed by `Fin d →₀ ℕ`.

The polarization step is especially easy to overlook: recovering `Q(x)=D^kL(0)[x,\ldots,x]/k!` pointwise does not syntactically give equality of the underlying `ContinuousMultilinearMap` without it.

---

## 3. Minimal good first tide

The best first tide is **J2, with only the small amount of J0/J1 needed internally**, delivered as one self-contained “Gaussian covariance rigidity” file.

Suggested file:

```text
Laplace/Multi/GaussianCovariance.lean
```

Target theorem:

```lean
theorem homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {k : ℕ} (hk : 0 < k)
    {Q : EuclidD d → ℝ}
    (hQ_cont : Continuous Q)
    (hQ_growth : HasPolynomialGrowth Q)
    (hQ_hom : IsHomogeneousOfDegree k Q)
    (hvar : gaussianCovariance H Q Q = 0) :
    Q = 0
```

Why this is the best first tide:

- it proves the central no-Isserlis idea;
- it is independent of the difficult higher-order DCT;
- it validates that abstract polynomial-growth tests suffice;
- it exposes any Mathlib full-support/weighted-integral mismatch early;
- it is reusable at every degree;
- its mathematical scope is small and its acceptance criterion is unambiguous.

I would not choose the cubic integrated expansion as the first tide: it mixes Taylor API issues, rate-divided domination, tail estimates, and normalized ratio algebra all at once.

---

## 4. Where the normalized-moment data should enter

The public pairwise recovery theorem should consume **`IsLittleO` hypotheses**, not merely unscaled `Tendsto` hypotheses.

### Recommended rescaled-data form

For a degree-\(k\) test `P`, define the normalized moment after the substitution `x = qy`. Then require

```lean
(fun q =>
  rescaledPosteriorMoment A₁ P q -
  rescaledPosteriorMoment A₂ P q)
  =o[AtZeroPlus] (fun q => q^(k - 2))
```

The analytic theorem J5 proves:

```lean
Tendsto
  (fun q =>
    (rescaledPosteriorMoment A₁ P q -
      rescaledPosteriorMoment A₂ P q) / q^(k - 2))
  AtZeroPlus
  (𝓝 (-gaussianCovariance H P Q))
```

The data hypothesis implies the same quotient tends to zero. Thus covariance vanishes.

This division of responsibilities is clean:

- analytic layer: a precise quotient `Tendsto`;
- observational/data layer: an `IsLittleO` matching hypothesis;
- recovery layer: uniqueness of limits plus covariance injectivity.

### Equivalent raw-moment rate

If `P` is homogeneous of degree `k`, then under `x = qy`,

\[
P(qy)=q^kP(y).
\]

Therefore a rescaled normalized-moment discrepancy of order `o(q^(k-2))` corresponds to a physical/raw normalized-moment discrepancy of order

\[
o(q^{k}q^{k-2})=o(q^{2k-2}).
\]

Thus a convenience theorem may accept:

```lean
rawMomentDifference A₁ A₂ P
  =o[AtZeroPlus] (fun q => q^(2 * k - 2))
```

For the cubic term `k = 3`:

- rescaled cubic-test moment difference: `o(q)`;
- raw homogeneous cubic moment difference: `o(q^4)`.

The rescaled formulation is preferable internally because its exponent `k - 2` directly matches the perturbation of the rescaled loss.

### Why ordinary Tendsto is insufficient

A hypothesis saying only

```lean
Tendsto (momentDifference ...) AtZeroPlus (𝓝 0)
```

does not distinguish degree \(k\) from higher orders: all higher-order perturbations have the same unscaled zero limit. The rate is the identifying information.

### Relation to `hessian_recovery`

Use the same pairwise philosophy as `hessian_recovery`, but at degree \(k\) the natural internal statement is rate-sensitive:

```lean
IsLittleO momentDifference (fun q => q^(k - 2)) AtZeroPlus
```

For external APIs, provide both forms:

1. `..._of_rescaled_moment_isLittleO`;
2. `..._of_raw_moment_isLittleO`.

Avoid making users provide a `Tendsto` of a manually divided expression; `IsLittleO` is more compositional and handles products with the homogeneity scaling cleanly.

---

## 5. Suggested implementation order

1. `GaussianGrowth.lean`: polynomial-growth closure and integrability.
2. `GaussianCovariance.lean`: continuous rigidity, variance, homogeneous injectivity.
3. `MultilinearDiagonal.lean`: polarization.
4. `HigherRayTaylor.lean`: cubic first, then arbitrary `k`.
5. `PairwiseRescaledDCT.lean`: cubic case first.
6. `CubicRecovery.lean`: recover `iteratedFDeriv ℝ 3`.
7. Generalize DCT and recovery from `3` to arbitrary finite `k`.
8. `JetRecovery.lean`: finite induction, then smooth-jet wrapper.
9. Only afterward introduce `MvPolynomial` to replace universal test families by finite monomial data.

The cubic recovery theorem is the right first end-to-end milestone, but Gaussian covariance rigidity is the right first individual tide.