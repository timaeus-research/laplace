# Research round 100 — germbij response-map programme: programme J landed; what next?

You are GPT-6 Astra, research advisor to a Lean 4 (Mathlib) formalisation of the note *germbij* ("The germ of a bijection": the response map `q ↦ Φ(q) ∈ W` of a bounded feature family `S : J → X → ℝ` over data laws `q ≪ ν`, `W = dirSpan` the direction space of the moment body, `P_θ = ν.tilted(−⟨θ,S⟩)`, mean map `m`, inverse chart `θr`, Fisher form `G`, m-Christoffel `C(u,v) = A⁻¹T(u,v)` with `T` the third-cumulant operator, chart derivative `A = CD θ` and its inverse `(CDE θ).symm`). Everything below is sorry-free Lean in laplace `Laplace/Multi/Response*` (≈65 modules, rounds 84–99).

The user's standing direction: *"make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to map the space of responses across the data manifold (ideally all the way from the featureless distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?"* plus the resolution story (truth shifts vs sampling shifts of the structural coordinate; chambers below the sampling scale are unresolvable).

## What landed since round 99 (your programme J + audit)

* **J1 `ResponseTestingResolution`** — the testing lower bound (converse of the probabilistic resolution theorem).
* **Audit fix `ResponseCertifiedChart`** — the probabilistic resolution theorem now exports the good event (interior ∧ chart valid ∧ sign), plus the certificate-free chart-validity theorem; the I3 hypothesis is named `varianceCurvaturePairing` with the inequality version `concaveOn_lineVariance_of_pairing_nonpos`.
* **J2 `ResponseSimplexIdentification`** — finite `X`, charged atoms, `SpansAffine`: atom-mass map `B : W ≃ₜ Δ°`, smooth both ways via the log-lift `W ≃ₗ (X→ℝ)⧸ℝ𝟙`; mean map = barycentre; **featureless journey = mixture segment**; exact mixture variance identity.
* **J3 `ResponseSimplexSphere`** — **`d_F(θ₀,θ₁) = 2 arccos ∑√(B(θ₀)B(θ₁))`** (spherical bound attained; great-circle lift through the log-lift; Fisher speed via `G(θ̇,θ̇) = ∑ṗ²/p`); `d_F < π`.
* **J6 `ResponseMeanPolytopeJourney`** — finite full-support (not nec. saturated): `Ω = relint conv S(X)`, `W ≃ₜ relint conv S(X)` (the seabed already had the global chart), polytope journey lift with velocity, max-entropy law along it; feature means agree with the mixture but laws differ off saturation.
* **J4 `ResponseLocalizedSamplingBias`** — generic cubic remainder; `D²(m⁻¹)(m θ₀)[e,e] = −C(A⁻¹e,A⁻¹e)`; cubic expansion on a certified ball; law-level **localised bias = curvature term**: `‖E[θ̂_loc − θ₀] + ½E_μ[C(A⁻¹Z,A⁻¹Z)]‖ ≤ (‖A⁻¹‖/δ² + K + ½‖A⁻¹‖‖T‖‖A⁻¹‖²/δ) M₃` for the reset-localised estimator, `μ` any finite centred law of the displacement with third absolute moment `M₃`. NOT done: the i.i.d. instance (`E[C(A⁻¹ξ̄,A⁻¹ξ̄)] = (1/n)∑C_{ab}Cov_D(S_a,S_b)`, and `M₃ = O(n^{-3/2})` which needs a fourth-moment bound for bounded *mutually* independent sums — the seabed's sampling hypotheses are only pairwise `IndepFun`).
* J5 (summary/packaging module) deliberately not done yet (user prioritises new mathematics).

## Key statements (verbatim Lean)

```lean
-- Laplace/Multi/ResponseTestingResolution.lean
/-- **The testing lower bound in terms of the intrinsic distance**: for `d_F(θ₀,θ₁) ≤ π`, every
equal-prior test on `n` samples has error at least `(1 − √(1 − cos^{2n}(d_F/2)))/2`. -/
theorem testing_error_model_ge_of_fisherDist [Nonempty X] (n : ℕ) (θ₀ θ₁ : 𝕍)
    (hd : fisherDist S ν θ₀ θ₁ ≤ Real.pi) {φ : (Fin n → X) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(1 - (Real.cos (fisherDist S ν θ₀ θ₁ / 2) ^ n) ^ 2)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ Pfam (θ₀ : J → ℝ))) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ Pfam (θ₁ : J → ℝ))) / 2
```

```lean
-- Laplace/Multi/ResponseTestingResolution.lean
/-- **The resolution scale**: for `d_F ≤ π`, every equal-prior test on `n` samples has error at
least `1/2 − √n d_F/4`. -/
theorem testing_error_model_ge_half_sub [Nonempty X] (n : ℕ) (θ₀ θ₁ : 𝕍)
    (hd : fisherDist S ν θ₀ θ₁ ≤ Real.pi) {φ : (Fin n → X) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    1 / 2 - Real.sqrt n * fisherDist S ν θ₀ θ₁ / 4 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ Pfam (θ₀ : J → ℝ))) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ Pfam (θ₁ : J → ℝ))) / 2
```

```lean
-- Laplace/Multi/ResponseCertifiedChart.lean
/-- **The probabilistic resolution theorem with the good event**: with probability at least
`1 − τ_{θ₀}(D)/(n r²)` the empirical mean is interior, the chart inverts the mean map at it
(the empirical response is the maximum-entropy law with the empirical moments), and the response
has crossed the wall `ℓ` in the direction of the truth shift. -/
theorem measureReal_goodEvent_certified_ge (θ₀ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ₀ v v) {δ K : ℝ} (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2)
    (ℓ : 𝕍 →L[ℝ] ℝ) (e : 𝕍) (t r : ℝ) (hr : 0 < r)
    (hmean : (fun j ↦ ∫ x, S j x ∂D) = mean (θ₀ : J → ℝ) + t • (e : J → ℝ))
    (hδ : |t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r ≤ δ)
    (hcert : 0 < t * ℓ (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) e) - ‖ℓ‖ / Real.sqrt c * r -
      ‖ℓ‖ * K * (|t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r) ^ 2)
    {n : ℕ} (hn : 0 < n) :
    1 - -(∑ a, ∑ b, samplingOp hS ν θ₀ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n / r ^ 2 ≤
      P.real {ω | sampleResponse S Xs n ω ∈ Ωm ∧
        mean (θr (sampleResponse S Xs n ω)) = sampleResponse S Xs n ω ∧
        ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))}
```

```lean
-- Laplace/Multi/ResponseSimplexIdentification.lean
/-- **`B ∘ B⁻¹ = id` on the open simplex.** -/
theorem atomMass_simplexInv (hspan : SpansAffine S ν) {p : X → ℝ} (hp : p ∈ posSimplex X) :
    atomMass S ν (simplexInv hS ν hν hspan p : J → ℝ) = p
```

```lean
-- Laplace/Multi/ResponseSimplexIdentification.lean
/-- **The featureless journey is the mixture segment in the simplex**: for `t ∈ [0,1]`,
`B(θ_t) = (1 − t) ν{·} + t B(θ₁)` along the model journey from `θ = 0` to `θ₁`. -/
theorem atomMass_modelJourney_zero (hspan : SpansAffine S ν) (θ₁ : 𝕍) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    atomMass S ν (modelJourney hS ν 0 θ₁ t : J → ℝ) =
      fun x ↦ (1 - t) * ν.real {x} + t * atomMass S ν (θ₁ : J → ℝ) x
```

```lean
-- Laplace/Multi/ResponseSimplexIdentification.lean
/-- **The exact mixture identity for the posterior variance along the featureless journey**:
`Var_{θ_t} F = (1−t) Var_ν F + t Var_{θ₁} F + t(1−t)(E_{θ₁}F − E_ν F)²`. -/
theorem lawCov_modelJourney_zero (hspan : SpansAffine S ν) (θ₁ : 𝕍) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (F : X → ℝ) :
    lawCov (Pfam (modelJourney hS ν 0 θ₁ t : J → ℝ)) F F =
      (1 - t) * lawCov ν F F + t * lawCov (Pfam (θ₁ : J → ℝ)) F F +
        t * (1 - t) * ((∫ x, F x ∂Pfam (θ₁ : J → ℝ)) - ∫ x, F x ∂ν) ^ 2
```

```lean
-- Laplace/Multi/ResponseSimplexSphere.lean
/-- **The Fisher speed of the lift**: `G(θ̇_s, θ̇_s) = ∑_x ṗ_x²/p_x`. -/
theorem fisherVar_sphereLift (hp : p ∈ posSimplex X) (hq : q ∈ posSimplex X) (hne : p ≠ q)
    (s : ℝ) : fisherVar S ν (sphereLift hS ν hν hspan p q s) (sphereLiftDeriv hS ν hν hspan p q s) =
      ∑ x, spherePathDeriv p q s x ^ 2 / spherePath p q s x
```

```lean
-- Laplace/Multi/ResponseSimplexSphere.lean
/-- **THE SPHERE THEOREM**: for a saturated finite family,
`d_F(θ₀, θ₁) = 2 arccos ∑_x √(B(θ₀)_x B(θ₁)_x)`. -/
theorem fisherDist_eq_two_arccos (θ₀ θ₁ : 𝕍) :
    fisherDist S ν θ₀ θ₁ =
      2 * Real.arccos (∑ x, √(atomMass S ν (θ₀ : J → ℝ) x) * √(atomMass S ν (θ₁ : J → ℝ) x))
```

```lean
-- Laplace/Multi/ResponseSimplexSphere.lean
/-- **The response space of a saturated finite family has Fisher diameter below `π`**: it is
bounded, hence (being an open simplex) not complete. -/
theorem fisherDist_lt_pi (θ₀ θ₁ : 𝕍) : fisherDist S ν θ₀ θ₁ < Real.pi
```

```lean
-- Laplace/Multi/ResponseMeanPolytopeJourney.lean
/-- **The law along the polytope journey is the maximum-entropy law with the prescribed means**:
the information projection of the mean `m_t`. -/
theorem familyMeasure_polytopeJourney_eq_responseProjection
    (hp : p ∈ intrinsicInterior ℝ hull) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Pfam (polytopeJourney hS ν p t : J → ℝ) = responseProjection hS ν (m₀ + t • (p - m₀))
```

```lean
-- Laplace/Multi/ResponseLocalizedSamplingBias.lean
/-- **The quantitative cubic remainder** of a `C³` map on a ball around `0`. -/
theorem exists_cubic_remainder {F : E → G} {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
    (hF : ContDiffOn ℝ 3 F U) :
    ∃ δ > 0, Metric.closedBall (0 : E) δ ⊆ U ∧ ∃ K, 0 ≤ K ∧ ∀ z : E, ‖z‖ ≤ δ →
      ‖F z - F 0 - fderiv ℝ F 0 z - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 z z‖ ≤ K * ‖z‖ ^ 3
```

```lean
-- Laplace/Multi/ResponseLocalizedSamplingBias.lean
/-- **The second derivative of the inverse chart is minus the m-Christoffel symbol**:
`D²(m⁻¹)(m(θ₀))[e, e] = −C_{θ₀}(A⁻¹e, A⁻¹e)`. -/
theorem fderiv_fderiv_responseTheta_meanAdd_zero (θ₀ e : 𝕍) :
    fderiv ℝ (fderiv ℝ (Finv θ₀)) 0 e e =
      -C θ₀ ((CDE θ₀).symm e) ((CDE θ₀).symm e)
```

```lean
-- Laplace/Multi/ResponseLocalizedSamplingBias.lean
/-- **The localised bias decomposition** on the law `μ` of the sampling displacement:
`∫_{‖z‖≤δ} (θr(m₀+z) − θ₀) dμ = A⁻¹ ∫_{‖z‖≤δ} z dμ − ½ ∫_{‖z‖≤δ} C(A⁻¹z,A⁻¹z) dμ + R`,
`‖R‖ ≤ K ∫_{‖z‖≤δ} ‖z‖³ dμ`. -/
theorem localizedBias_decomposition (μ : Measure 𝕍) [IsFiniteMeasure μ] (θ₀ : 𝕍) {K : ℝ}
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z +
        (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z‖ ≤ K * ‖z‖ ^ 3) :
    ‖(∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀) ∂μ) -
        (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) (∫ z in cball, z ∂μ) -
          (1 / 2 : ℝ) • ∫ z in cball, curvatureForm hS ν θ₀ z ∂μ)‖ ≤
      K * ∫ z in cball, ‖z‖ ^ 3 ∂μ
```

```lean
-- Laplace/Multi/ResponseLocalizedSamplingBias.lean
/-- **The truncated linear term of a centred law is controlled by the third moment**:
`‖∫_{‖z‖≤δ} z dμ‖ ≤ M₃/δ²`. -/
theorem norm_setIntegral_id_le_of_centred (μ : Measure 𝕍) [IsFiniteMeasure μ] (hδ : 0 < δ)
    (hcent : ∫ z, z ∂μ = 0)
    (hint : Integrable (fun z : 𝕍 ↦ z) μ) (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    ‖∫ z in cball, z ∂μ‖ ≤ (∫ z, ‖z‖ ^ 3 ∂μ) / δ ^ 2
```

```lean
-- Laplace/Multi/ResponseLocalizedSamplingBias.lean
/-- **THE LOCALISED SAMPLING BIAS IS THE CURVATURE TERM**: for a centred law `μ` of the sampling
displacement with third absolute moment `M₃`,

`‖ E[θ̂_loc − θ₀] + ½ E_μ[C_{θ₀}(A⁻¹Z, A⁻¹Z)] ‖ ≤ (‖A⁻¹‖/δ² + K + ½ ‖A⁻¹‖‖T‖‖A⁻¹‖²/δ) M₃`,

where `θ̂_loc = θ₀ + 1_{‖ξ‖≤δ}(θr(m₀+ξ) − θ₀)` is the reset-localised response. -/
theorem localizedBias_curvature (μ : Measure 𝕍) [IsFiniteMeasure μ] (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z +
        (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z‖ ≤ K * ‖z‖ ^ 3)
    (hcent : ∫ z, z ∂μ = 0) (hint : Integrable (fun z : 𝕍 ↦ z) μ)
    (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    ‖(∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀) ∂μ) +
        (1 / 2 : ℝ) • ∫ z, curvatureForm hS ν θ₀ z ∂μ‖ ≤
      (‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ / δ ^ 2 + K +
        (1 / 2 : ℝ) * (‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * ‖thirdOp hS ν θ₀‖ *
          ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ ^ 2) / δ) * ∫ z, ‖z‖ ^ 3 ∂μ
```

```lean
-- Laplace/Multi/ResponseObservableHessian.lean
/-- **Nonpositive variance–curvature pairing gives concave posterior variances along mean
segments**: if `E_t[(F − E_t F)² r_{V_t V_t}] ≤ 0` along the line, the variance is concave on
every interval inside the domain. -/
theorem concaveOn_lineVariance_of_pairing_nonpos {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {a b : ℝ}
    (hab : Icc a b ⊆ responseLineDomain S ν θ₀ e)
    (hpair : ∀ t ∈ Icc a b, varianceCurvaturePairing hS ν F θ₀ e t ≤ 0) :
    ConcaveOn ℝ (Icc a b) (lineVariance hS ν F θ₀ e)
```

## Questions

**Q1 (audit).** Check the statements above for mathematical correctness and for hidden weakness: (a) J3 uses the seabed's `fisherDist = sInf` over global `C¹` paths in `W` with the Fisher speed `√Var_{P_θ}⟨θ̇,S⟩`; is `d_F = 2 arccos ∑√(pq)` the correct claim for saturated finite families with reference `ν` (not uniform)? (b) J4's `localizedBias_curvature` — is the reset-localisation convention and the third-moment control the right statement, and are the constants sane? (c) J2's claim "featureless journey = mixture segment" — any subtlety with the choice of `ν` as the featureless law (max *relative* entropy) or with the `t = 1` endpoint? (d) anything in the good-event theorem that a careful statistician would object to?

**Q2 (ranking).** Rank 5–7 next Lean modules by value for the user's direction (mapping responses across the data manifold from featureless to data; the resolution story), with a one-paragraph proof route each. Candidates I see: (i) the i.i.d. instance of J4 (bilinear covariance contraction + fourth-moment bound under `iIndepFun`, then Cauchy–Schwarz `M₃ ≤ √M₂√M₄` to get `n^{-3/2}`); (ii) the completion of the saturated response space by the closed simplex with the same sphere formula; (iii) a `ResponseGeometrySummary` theorem-first packaging; (iv) a non-saturated finite analogue of the sphere theorem (lower bound sharpness? `d_F` vs the induced spherical distance on the quotient); (v) curvature bounds for non-saturated finite families (`K` between? Gauss identity with the residual); (vi) the "response atlas as a quotient of DataLaw by feature means" made explicit in the finite case (the fibre over a mean is a polytope of laws; its dimension `|X| − 1 − dim W`); (vii) the journey information cost `KL = defect + ∫(1−t)G` specialised to the simplex (closed form along the mixture segment: `KL((1−t)ν+tp ‖ ν)` derivative identities); (viii) anything I am missing that is more beautiful. Which of these are one-tide-sized?

**Q3 (headline).** After programme J, what is the single most compelling headline theorem still missing for the note's story "from the featureless law to the data along the response map", and what would its Lean statement look like?

Be concrete, point out false statements bluntly, and prefer routes that reuse the landed objects. Do not propose Lean code; propose statements and proof routes.
