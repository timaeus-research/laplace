# germbij formalisation — research consult, round 16

You are Astra, advising the Lean formalisation of the germbij note ("What expectation values know about the loss landscape", Murfet 2026) in the laplace seabed (Lean 4.33, Mathlib) and its resolution-facing mirror on the local hironaka branch `wall-atlas`. Round 15 asked for (1) a note-to-Lean statement audit plus an end-to-end analytic-input theorem, (2) a certificate-coverage audit, (3) the critical-boundary regression `T = xy, F = ax, θ = x^p y^q`, (4) the constructive-recovery export or the smooth counterexample, (5) asymptotic-scale cleanup. Items 1–3 are landed; the results are below, verbatim from the Lean source. Please audit them for statement-level errors and rank what to do next.

## Landed since round 15

### (1a) The audit
Every displayed claim of the note's identifiability section (`lem:pencil`, `lem:sector`, `thm:singular`, `rem:singular-scope`(c), `prop:one-point`, constructive recovery (a) and the retained fragment of (b)) carries a `\leanref`. The one untagged proof, the "No" to the proportionality question, was already formalised in `NormalizedSingular.lean` (global `C^∞`, both losses `≥ 0`) and is now also proved under the hypotheses of the unnormalised pencil theorem:

```lean
theorem proportional_families_force_eq_near {L₁ L₂ : (ι → ℝ) → ℝ} {W₀ : Set (ι → ℝ)}
    (hL1c : Continuous L₁) (hL2c : Continuous L₂) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2 : ∀ p ∈ W₀, AnalyticAt ℝ L₂ p)
    (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2 : ∀ p ∈ W₀, L₂ p = 0) (C : ℝ → ℝ)
    (hfam : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - C t * ∫ w, φ w * Real.exp (-(t * L₁ w))) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w
```
(`SuperPoly f := ∀ N, f =o[atTop] t^{-N}`.) Nothing is assumed on `C`, `L₁ ≥ 0` is not needed. Is this the right general form, and is there any reason the note's statement should keep `L₁ ≥ 0`?

### (1b) The end-to-end theorem for a general analytic truth function (hironaka, local)
```lean
theorem truth_fibre_expectation_pushforward {U₀ : Set (Fin (m + 1) → ℝ)} (hU₀ : IsOpen U₀)
    {F : (Fin (m + 1) → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U₀) (hFc : Continuous F)
    (hF0 : ∀ z, 0 ≤ F z) (T : (Fin (m + 1) → ℝ) → ℝ) (hT : AnalyticOnNhd ℝ T U₀)
    (hT0 : T 0 = 0) (hTm : Measurable T)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℝ), F z * T z = 0)
    (W : Opens (Fin (m + 1) → ℝ)) (hW : IsConnected (W : Set (Fin (m + 1) → ℝ)))
    (h0W : (0 : Fin (m + 1) → ℝ) ∈ W) (hWU : (W : Set (Fin (m + 1) → ℝ)) ⊆ U₀)
    {L : Set (Fin (m + 1) → ℝ)} (hL : IsCompact L) (hLW : L ⊆ W) :
    ∃ ε > 0, ∃ D : TruthChartsData m T (L ∩ {z | |T z| ≤ ε}),
      (∀ θ : (Fin (m + 1) → ℝ) → ℝ≥0∞, Measurable θ → Measurable (D.totalKernel θ) ∧
        ∀ η : ℝ → ℝ≥0∞, Measurable η →
          ∫⁻ z in L ∩ {z | |T z| ≤ ε}, θ z * η (T z) = ∫⁻ s, η s * D.totalKernel θ s) ∧
      ∃ P : D.Phase F, ∀ (σ γ : ℝ), σ ≠ 0 → ∀ C : P.TermMeasureCertificate σ γ,
      ∀ (ψ χ : (Fin (m + 1) → ℝ) → ℝ), Continuous ψ → (∀ z, 0 ≤ ψ z) →
      ∀ Mψ : ℝ, (∀ z, ψ z ≤ Mψ) → (∀ z, ψ z ≠ 0 → z ∈ L ∩ {z | |T z| ≤ ε}) →
      Continuous χ → (∀ z, 0 ≤ χ z) → ∀ Mχ : ℝ, (∀ z, χ z ≤ Mχ) →
      (∀ z, χ z ≠ 0 → z ∈ L ∩ {z | |T z| ≤ ε}) →
      (∫ z, χ z ∂C.leadingMeasure) ≠ 0 →
      Tendsto (fun t ↦ D.fibreRatio F ψ χ σ γ t) atTop
        (𝓝 ((∫ z, ψ z ∂C.leadingMeasure) / ∫ z, χ z ∂C.leadingMeasure))
```
with `D.fibreRatio F ψ χ σ γ t := (D.totalKernel (ofReal (e^{-tF} ψ)) (σ t^{-γ})).toReal / (D.totalKernel (ofReal (e^{-tF} χ)) (σ t^{-γ})).toReal`. Also the constant / dominant-set / limiting-measure / point forms (`truth_fibre_expectation`, `_dominant`, `_measure`, `_point`). The certificate `C` is still an input.

### (2) Certificate coverage
`ProfileIntegrableOf.of_uniqueLPMin_vertex` (all `κ > 0`, `α = (δ/κ_j) e_j`, `δ > 0`, strict truth, `UniqueLPMin Q κ γ δ (r+1) α` ⇒ profile certificate) and `ProfileIntegrableOf.of_uniqueLPMin_twoScaled` (two scaled coordinates, `Δ ≠ 0`, dual decomposition `r_S + 1 = ηκ_S − θQ_S` given as data, `UniqueLPMin` ⇒ certificate), and the term data `TermData.vertexOfUniqueLPMin`, `twoScaledOfUniqueLPMin`. Degenerate shapes (a face of minimisers) are the log regimes with their own `TermData` constructors (tied, partial, activeTruth, activeTruthSpectator, activeTruthDegenerate). Missing: a decision procedure "given the exponent data, which shape is the optimum" (existence and classification of an optimal vertex of the chart polytope).

### (3) The critical-boundary regression
```lean
theorem mix_tendsto_totalKernel_boundary {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) (p q : ℕ)
    {ψ : (Fin 2 → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z)
    (hψL : ∀ z, ψ z ≠ 0 → z ∈ mixLc) :
    Tendsto (fun t ↦ t ^ p * (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (a * z 1))) * (z 0 ^ q * z 1 ^ p * ψ z)))
        (σ / t)).toReal)
      atTop (𝓝 (σ ^ q * ∫ u in Ioi (2 * σ),
        u ^ ((p : ℝ) - q - 1) * exp (-(a * u)) * ψ ![σ / u, 0]))
```
(`mixLc = [0,1/2]²`, `mixData` the identity-chart record for `T = z₀z₁` with kernel `∫_{2s}^{1/2} g(s/x, x) dx/x`), and `exported_mix_tendsto_totalKernel_boundary` for every `TruthChartsData 1 (z₀z₁) (mixThin ε)`. Note the limit sees `ψ` along the whole segment `{z₁ = 0}` (weighted by `ψ(σ/u, 0)`), not at a point; with `ψ ≡ 1` on the square and `p = q + 1` the constant is `σ^q e^{-2aσ}/a`. Your formula had `∫_σ^∞`; ours has `2σ` because the box is `[0,1/2]`. Is the segment-weighted form what the note's "critical boundary" discussion needs, and does the model-theorem side (vertex regime, tied cut, tied phase) reproduce this constant, or is the axis-supported phase outside the certified regimes (the phase `a z₁` vanishes on the wall component `z₁ = 0`, so its `TermData` classification is the degenerate/boundary one)?

## Questions
1. Statement audit of (1a), (1b), (3): any hypothesis that is wrong, redundant, or missing; any mismatch with the note's displayed conclusions.
2. Rank the next items with concrete Lean-level statements:
   (a) the constructive-recovery export (finite-jet reconstruction from the exported chart data) — what exactly should be proved, and from which landed pieces;
   (b) the smooth counterexample (a flat perturbation invisible to all expansion coefficients) at singular minima, if the note needs more than `prop:flat`;
   (c) the shape decision procedure for the chart LP (optimal vertex existence + classification into vertex / two-scaled / face), to make `truth_fibre_expectation` hypothesis-free;
   (d) the unit-dependent boundary regression (`F = a(z) z₁` with `a` continuous positive) or its identification with the boundary `TermData` (`activeTruthDegenerate`);
   (e) asymptotic-scale cleanup (a `Laplace.Scale` API: `t^{-λ} (log t)^m`, comparability, formal division of expansions with positive leading coefficient);
   (f) anything else the note's "What remains" section needs.
3. For the top item, the obstruction you foresee and the cheapest bounded first step.
