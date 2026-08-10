## 1. Minimal statement chain for piece (iii)

The note’s induction only needs a **one-grade comparison theorem**, followed by covariance injectivity and a finite induction. It does not initially require a full singular asymptotic-expansion framework.

I would normalize the weights integrally rather than formalize arbitrary real weighted degrees:

- `a : Fin d → ℕ` with `0 < a i`;
- principal weighted degree `D : ℕ`;
- \(P(\delta_h x)=h^D P(x)\), where \((\delta_h x)_i=h^{a_i}x_i\);
- corrections \(R_E\) of weighted degree \(E>D\);
- inverse temperature \(t=h^{-D}\).

Then a correction of degree \(E\) enters at the ordinary integer power \(h^{E-D}\). Rational weights can be cleared to this form.

### Stage A: exact anisotropic rescaling

Build this on:

- `Laplace.Multi.AnisotropicScaling.scalesMeasure_normalized_law`;
- `Laplace.Multi.DiagonalVolume`;
- the monomial specialization already used by
  `Laplace.Multi.SeparableAffinity.gibbsExpectation_evenMonomial_powerLaw`.

A useful shape is:

```lean
theorem normalizedMonomial_rescale_semQH
    (a : Fin d → ℕ) (D : ℕ)
    (P : (Fin d → ℝ) → ℝ)
    (R : Finset ℕ → (Fin d → ℝ) → ℝ)
    (hP : IsWeightedHomogeneous a D P)
    (hR : ∀ E ∈ grades, IsWeightedHomogeneous a E (R E))
    (α : Fin d →₀ ℕ) (h : ℝ) (hh : 0 < h) :
  h ^ weightedDegree a α *
      normalizedIntegral
        (fun x => monomial α x)
        (fun x => Real.exp (-(h ^ (-D : ℤ)) *
          (P x + ∑ E ∈ grades, R E x)))
    =
      normalizedIntegral
        (fun u => monomial α u)
        (fun u => Real.exp
          (-(P u + ∑ E ∈ grades, h ^ (E - D) * R E u)))
```

The exact API will depend on how `scalesMeasure_normalized_law` represents the diagonal map and Jacobian. The important output is the rescaled posterior

\[
\mu_{R,h}(du)\propto
\exp\!\left[-P(u)-\sum_{E>D}h^{E-D}R_E(u)\right]du.
\]

For a local analytic loss there is an additional cutoff/tail comparison. I would not include that in the first theorem. First prove the global polynomial/rescaled-density statement; later connect it to local losses using the mesoscopic machinery from:

- `Laplace.Multi.NumeratorTails`;
- `Laplace.Multi.ForwardTheorems`;
- the new graded-exponential and uniform-majorant files.

### Stage B: one-grade normalized difference limit

This is the core theorem. It is the anisotropic analogue of the mechanism behind:

- `Laplace.Multi.NormalizedRate.tendsto_pairwise_normalized_moment_difference`;
- `Laplace.Multi.DegreeRecovery.iteratedFDeriv_recovery_of_moment_rates`;
- the one-dimensional comparison ladder in
  `Laplace.OneD.RecoveryExpansion`,
  `RecoveryAllOrder`, and `JetDifference`.

The cleanest first version is measure-theoretic, with domination assumptions explicit:

```lean
theorem tendsto_normalizedIntegral_difference_div_pow
    (P Q A : X → ℝ)
    (V₁ V₂ : ℝ → X → ℝ)
    (ρ : ℕ)
    (hV₁ : Tendsto V₁ ... 0)
    (hV₂ : Tendsto V₂ ... 0)
    (hdiff :
      ∀ᵐ x,
        Tendsto (fun h => (V₂ h x - V₁ h x) / h ^ ρ)
          (𝓝[>] 0) (𝓝 (Q x)))
    (hmajorant : UniformIntegrableMajorant ...)
    (hZ : 0 < ∫ x, Real.exp (-P x)) :
  Tendsto
    (fun h =>
      (normalizedIntegral A (fun x => exp (-(P x + V₂ h x))) -
       normalizedIntegral A (fun x => exp (-(P x + V₁ h x)))) /
        h ^ ρ)
    (𝓝[>] 0)
    (𝓝 (-covarianceUnder P A Q))
```

Here

```lean
covarianceUnder P A Q =
  expectationUnder P (A * Q) -
  expectationUnder P A * expectationUnder P Q
```

The sign assumes `V₂ - V₁ ∼ h^ρ Q`.

The direct semi-quasi-homogeneous corollary should say:

```lean
theorem weightedGrade_difference_rate
    (hlower :
      ∀ E < E₀, R₁ E = R₂ E)
    (Qdef : Q = R₂ E₀ - R₁ E₀)
    ... :
  Tendsto
    (fun h =>
      (rescaledMoment a D L₂ A h -
       rescaledMoment a D L₁ A h) /
        h ^ (E₀ - D))
    (𝓝[>] 0)
    (𝓝 (-covarianceUnder P A Q))
```

Products of lower corrections do not survive in this *pairwise* formulation because they cancel once all lower grades agree. This is substantially simpler than separately expanding each posterior and subtracting known nonlinear terms.

The new forward programme’s exact exponential split and uniform majorant are directly relevant here. The nondegenerate Gaussian-specific parts are not; the reference law is now \(e^{-P}du\).

### Stage C: covariance injectivity for a polynomial correction

This should be independent of Gaussian structure. The argument only uses positivity of the density and full support.

A finite-support version is enough:

```lean
theorem polynomial_eq_zero_of_covariance_monomials
    (P : (Fin d → ℝ) → ℝ)
    (Q : MvPolynomial (Fin d) ℝ)
    (hfinite : Integrable (fun x => eval x Q ^ 2 * exp (-P x)))
    (hpos : ∀ x, 0 < Real.exp (-P x))
    (hcov :
      ∀ α ∈ Q.support,
        covarianceUnder P (fun x => monomial α x)
          (fun x => eval x Q) = 0) :
  Q = 0
```

Proof:

1. expand \(Q=\sum_{\alpha\in\supp Q}c_\alpha x^\alpha\);
2. linearity gives \(\operatorname{Cov}_P(Q,Q)=0\);
3. hence \(Q\) is almost everywhere constant;
4. positivity of \(e^{-P}\) and continuity of \(Q\) make it everywhere constant;
5. positive weighted degree, or simply `Q 0 = 0`, forces that constant to be zero.

This generalizes the pattern in:

- `Laplace.Multi.GaussianCovariance.homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero`;
- `Laplace.OneD.MonomialVariance.monomial_variance_pos`.

It is worth proving this generically for any positive full-support reference density.

### Stage D: one-grade recovery, then finite induction

The useful packaged theorem is:

```lean
theorem weightedGrade_eq_of_moment_rates
    (hlower : ∀ E < E₀, R₁ E = R₂ E)
    (hmom :
      ∀ α ∈ (R₂ E₀ - R₁ E₀).support,
        Tendsto
          (fun h =>
            (rescaledMoment a D L₂ α h -
             rescaledMoment a D L₁ α h) /
              h ^ (E₀ - D))
          (𝓝[>] 0) (𝓝 0)) :
  R₁ E₀ = R₂ E₀
```

Then, for finitely many corrections:

```lean
theorem finite_semQH_corrections_eq_of_moment_asymptotics
    (grades : Finset ℕ)
    (hgrades : ∀ E ∈ grades, D < E)
    (hmom :
      ∀ α, rescaledMomentFamilyEquivalent L₁ L₂ α) :
  ∀ E ∈ grades, R₁ E = R₂ E
```

This is the genuine analogue of the finite-jet induction in
`Laplace.Multi.JetInduction`.

I would **not** make “all analytic corrections are recovered” the first target. That additionally needs:

- weighted Taylor truncations for analytic germs;
- local finiteness of weighted degrees;
- uniform remainder estimates under anisotropic scaling;
- passage from equality of every weighted truncation to analytic germ equality.

That is considerably more than the covariance argument in the note.

---

## 2. Piece (i) does not require distribution theory

It has a finite-dimensional—and in fact nearly diagonal—reformulation.

For a fixed exponent \(\lambda\), let

\[
S_\lambda=\{\alpha:\ell(\alpha)=\lambda\}.
\]

This set is finite because all weights are positive. The coefficient at that exponent has the form

\[
c_\lambda(\phi)
 =\sum_{\alpha\in S_\lambda}
   \frac{(-1)^{|\alpha|}M_\alpha}{\alpha!}
   \,\partial^\alpha\phi(0).
\]

Define the finite jet matrix

\[
J_{\beta\alpha}=\frac{1}{\alpha!}\partial^\alpha\phi_\beta(0).
\]

Recovery of the colliding coefficient vector \((M_\alpha)_{\alpha\in S_\lambda}\) is simply injectivity of \(J\). Choose

\[
\phi_\beta(x)=x^\beta\chi(x),
\qquad \chi\equiv1\text{ near }0.
\]

Then, for \(\alpha,\beta\in S_\lambda\),

\[
\frac{1}{\alpha!}\partial^\alpha\phi_\beta(0)
 =\delta_{\alpha\beta}.
\]

Thus the matrix is the identity. No theory of distributions is needed.

A Lean-level finite statement could be:

```lean
theorem collisionCoefficientMap_injective
    (S : Finset (Fin d →₀ ℕ))
    (φ : (Fin d →₀ ℕ) → (Fin d → ℝ) → ℝ)
    (hjet :
      ∀ α ∈ S, ∀ β ∈ S,
        iteratedDeriv α (φ β) 0 =
          if α = β then α.factorial else 0) :
  Function.Injective
    (fun M : (Fin d →₀ ℕ) →₀ ℝ =>
      fun β =>
        ∑ α ∈ S,
          M α / α.factorial * iteratedDeriv α (φ β) 0)
```

But an even smaller route is available. For the pure quasi-homogeneous model, test directly with the monomial observable. Anisotropic scaling gives

\[
\int x^\alpha\chi(x)e^{-tP(x)}dx
 =t^{-\ell(\alpha)}M_\alpha+o(t^{-N})
\]

for every \(N\), or exactly without the local cutoff. Therefore the coefficient of the expansion of the single observable \(x^\alpha\chi\) at \(\ell(\alpha)\) is \(M_\alpha\). Other \(\beta\) with the same exponent never enter that observable’s leading coefficient.

Useful target statements are therefore:

```lean
theorem monomial_integral_scaled_tendsto_moment
    ... :
  Tendsto
    (fun t =>
      t ^ ell q α *
        ∫ x, cutoff x * monomial α x * exp (-t * P x))
    atTop
    (𝓝 (∫ u, monomial α u * exp (-P u)))
```

and, for normalized data,

```lean
theorem normalized_monomial_scaled_tendsto_momentRatio
    ... :
  Tendsto
    (fun t =>
      t ^ weightedDegree q α *
        gibbsExpectation t P (cutoff * monomial α))
    atTop
    (𝓝 (M α / M 0))
```

The second is closest to what Proposition 7.6 needs. It should build mainly on `scalesMeasure_normalized_law`; the cutoff error can use `NumeratorTails` or a small weighted-coercivity tail lemma.

The new polynomial-growth observable support also means one may initially work globally with `monomial α` and avoid constructing compactly supported jet-isolating test functions entirely.

---

## 3. Ranking and recommended target

### By infrastructure delta

1. **Piece (i), narrowed to monomial coefficient extraction:** smallest delta.
   - Most of the scaling is already in `AnisotropicScaling` and `DiagonalVolume`.
   - Even-moment versions already occur in `SeparableAffinity` and `SeparableRecovery`.
   - The main additions are signed monomials, local cutoff tails if desired, and a coefficient-extraction wrapper.
   - No distributions are necessary.

2. **Piece (iii), one-grade comparison theorem:** medium delta.
   - The proof pattern already exists in `Multi.NormalizedRate` and the 1D recovery ladder.
   - It needs a non-Gaussian covariance API and a \(P\)-uniform DCT/majorant.
   - The new forward programme provides much of the needed exponential-difference and domination technology, but its quadratic/nondegenerate specialization cannot simply be reused verbatim.

3. **Piece (iii), complete analytic weighted induction:** large delta.
   - Weighted analytic truncations and anisotropic remainder bookkeeping are not merely packaging.
   - This is not presently a single tide-shaped theorem.

### By value toward constructive one-point recovery

1. **Piece (i)** is logically upstream: it recovers all \(M_\alpha/M_0\) and the weights. However, without the coarea/Gelfand–Leray step it still does not recover the principal part \(P\) in general.
2. **Piece (iii)** is highly valuable only *after \(P\) is known*. It recovers all higher corrections conditionally on the principal quasi-homogeneous part. It therefore does not bypass the geometric-measure-theory bottleneck in piece (ii).

Consequently, neither a full implementation of (i) nor a full implementation of (iii) currently closes Proposition 7.6 by itself.

## Recommended minimal targets

There are two good, bounded targets:

### Best small target

Formalize direct moment extraction:

```lean
normalized_monomial_scaled_tendsto_momentRatio
```

for an abstract positive quasi-homogeneous \(P\), all multi-indices—including odd ones. Then package:

```lean
momentRatios_eq_of_normalized_expansions
```

This settles piece (i) without distributions and strengthens the existing even-coordinate-moment recovery perimeter.

### Best reusable recovery target

Formalize the one-grade theorem:

```lean
weightedGrade_eq_of_moment_rates
```

factored through:

```lean
tendsto_normalizedIntegral_difference_div_pow
polynomial_eq_zero_of_covariance_monomials
```

Restrict the first application to finite polynomial corrections. That is closed-form-checkable, directly mirrors the note, and is reusable if the coarea obstruction is later removed.

I would stop short of the full semi-quasi-homogeneous analytic-germ theorem. Given the lower priority of class (c), the sensible endpoint is:

> principal-model moment ratios are recoverable, and—conditional on a common recovered principal part—each finite weighted correction grade is recoverable from normalized moment rates.

That is a precise and meaningful formalized fragment of Proposition 7.6 without committing to the unresolved coarea layer or a large weighted-analytic infrastructure project.