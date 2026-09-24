# Consult: germbij analytic layer, third research round (after research_partial_v1)

You are GPT-6 Astra advising on a Lean 4 + Mathlib formalisation (repo laplace, namespace Laplace.Multi, mirrored on the hironaka wall-atlas branch) of "What expectation values know about the loss landscape" (germbij): the leading-order asymptotics of fibre expectations `⟨ψ⟩_χ(t) = ∫ e^{-tF} ψ / ∫ e^{-tF} χ` along a wall, after resolution into wall charts with a constrained LP per chart. Your previous ranking (research_partial_v1) had three targets; all three are now formalised, zero sorries, axioms propext/Classical.choice/Quot.sound only. Please (A) audit the STATEMENTS below for soundness / misleading hypotheses (not the proofs), and (B) rank the next 3–4 targets, with the precise mathematical statement you would formalise for each and the main risk.

## What landed since the last consult (all in `Laplace/Multi/`)

1. Partially tied faces. Index `Fin (k+1) ⊕ ν` (tied block T of size k+1, strictly worse block N).
   - `tendsto_modelKernel_partial` (constant unit): `t^{γp+δλ}/(log t)^k · K(t) → A w₀ (B a₀)^{-λ} δ^k Γ(λ)/k! ∏_T κ^{-1} ∫_{(0,ρ)^N} ∏ z^{r_j − λκ_j}`.
   - `tendsto_modelKernel_partial_var` (moving unit and weight, statement below).
   - `tendsto_modelKernelOf_partial` (chart level, statement below) and `tendsto_termKernel_partial` (the certificate at the pair (γp+δλ, k) consumed by the lexicographic assembly `tendsto_fibre_expectation_lex`).
   - Tools: `modelKernel_reindex` (Lebesgue invariance under `piCongrLeft`), `continuousAt_weightFn` at any point whose bridge point is in the open ball, all-scale tied-block bound `tiedBlockIntegral ≤ M s^{-λ}(1+log⁺ s)^k`.

2. Tied truth, two scaled coordinates (your §(b)).
   - `integral_twoScaledInner`: ∫_{y>0, h<Q·log y} ∏ y^{a−1} e^{−c∏y^κ} = Γ(η) c^{−η} e^{−θh}/(θ|Δ|) under a = ηκ − θQ, η,θ>0, Δ≠0 (with integrability).
   - `integral_tiedDom_twoScaled` / `integrable_tiedDom_twoScaled` (statement below) on `Fin 2 ⊕ ν`, and the chart-level `ProfileIntegrableOf.of_twoScaled` (statement below).
   - `not_profileIntegrableOf_of_three_scaled` (statement below): with ≥3 scaled coordinates and a nonempty limiting domain there is no certificate (rank–nullity direction with d·κ = d·Q = 0; the flow preserves the surviving cutoff). Together with `of_vertex` (strict truth, one scaled coordinate) the isolated-optimum count is closed.

3. Distinguishability (your (3)).
   - `NormalisedMeasure.lean`: `normaliseMeasure μ = μ(1)⁻¹ • μ`; `normalise_eq_iff_forall_ratio` (nonzero finite Borel measures, HasOuterApproxClosed space: same normalised integrals of all bounded continuous functions ⟺ same normalisation); `restrict_ext_of_forall_integral_eq` (bounded continuous functions supported in an open U determine the restriction to U, via cutoffs min(1, n·dist(x,Uᶜ))); `normalise_restrict_eq_of_forall_ratio_nonneg` (ratios against a fixed positive reference χ for all NONNEGATIVE bounded continuous ψ supported in U determine the normalised restriction to U).
   - `WallDistinguishability.lean`: `tendsto_fibreRatio_sub_of_normalise_eq` and `normalise_restrict_limitMeasure_eq_of_forall_tendsto` (statement below). The latter needs `IsOpen L'` (L' is the ambient region of the wall atlas record `WallChartsData m ℓ L'`; the record does not assume it open; the observable class of the fibre expectation theorem is continuous, nonnegative, bounded, supported in L').

## Statements (Lean, verbatim)

```lean
theorem tendsto_modelKernel_partial_var {ρ A B D γ p q δ : ℝ} {κ r : Fin (k + 1) ⊕ ν → ℝ}
    {W a : (Fin (k + 1) ⊕ ν → ℝ) → ℝ → ℝ}
    (hρ : 0 < ρ) (hD : 0 ≤ D) (hκ : ∀ i, 0 < κ i) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ i, (r (Sum.inl i) + 1) / κ (Sum.inl i) = lam)
    (hgap : ∀ j, lam * κ (Sum.inr j) < r (Sum.inr j) + 1)
    (hB : 0 < B) (hδ : 0 < δ) (hγq : 0 < γ / q) {aL wU : ℝ} (haL : 0 < aL)
    (hW : Measurable (Function.uncurry W)) (ha : Measurable (Function.uncurry a))
    (hW0 : ∀ x v, 0 ≤ W x v) (hWup : ∀ x v, W x v ≤ wU)
    (halow : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → 0 ≤ v → v < ρ → aL ≤ a x v)
    (ha₀ : ∀ z : ν → ℝ, (∀ j, z j ∈ Ioo (0 : ℝ) ρ) → 0 < a (Sum.elim 0 z) 0)
    (hWlim : ∀ z : ν → ℝ, (∀ j, z j ∈ Ioo (0 : ℝ) ρ) →
      ContinuousAt (Function.uncurry W) (Sum.elim 0 z, 0))
    (halim : ∀ z : ν → ℝ, (∀ j, z j ∈ Ioo (0 : ℝ) ρ) →
      ContinuousAt (Function.uncurry a) (Sum.elim 0 z, 0)) :
    Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t) atTop
      (𝓝 (A * (δ ^ k * (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i))) *
        ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) ρ),
          W (Sum.elim 0 z) 0 * (B * a (Sum.elim 0 z) 0) ^ (-lam) *
            ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j)))) := by

theorem WallChartsData.Phase.tendsto_modelKernelOf_partial (e : Fin (k + 1) ⊕ ν ≃ Fin m)
    (hσ : σ ≠ 0) (hγ : 0 < γ) (hQ : D.Qexp i = 0) (hκ : ∀ j, 0 < P.kappa i j) {lam : ℝ}
    (hlam : 0 < lam)
    (htied : ∀ j, (P.rExp i (e (Sum.inl j)) + 1) / P.kappa i (e (Sum.inl j)) = lam)
    (hgap : ∀ j, lam * P.kappa i (e (Sum.inr j)) < P.rExp i (e (Sum.inr j)) + 1)
    (hδ : 0 < P.phaseExp i γ) (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + P.phaseExp i γ * lam) / log t ^ k *
        P.modelKernelOf i φ ε b t γ σ) atTop
      (𝓝 (P.constA i σ * (P.phaseExp i γ ^ k *
          (Gamma lam / k.factorial * ∏ j, 1 / P.kappa i (e (Sum.inl j)))) *
        ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)),
          φ (D.rep i (D.bridgePt i ε b (partialFace e z) 0)) *
            (P.wt i (D.bridgePt i ε b (partialFace e z) 0) *
              |P.b i (D.bridgePt i ε b (partialFace e z) 0)|) *
            (P.constB i σ * |P.a i (D.bridgePt i ε b (partialFace e z) 0)|) ^ (-lam) *
            ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j))))) := by

theorem integral_tiedDom_twoScaled {ρ D γ q c₀ η θ : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    (hc₀ : 0 < c₀) {Q κ r : Fin 2 ⊕ ν → ℝ} {αS : Fin 2 → ℝ} (hαS : ∀ i, 0 < αS i)
    (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ i, r (Sum.inl i) + 1 = η * κ (Sum.inl i) - θ * Q (Sum.inl i))
    (hη : 0 < η) (hθ : 0 < θ) (hβ : ∀ j, -1 < resExp η θ Q κ r j) :
    ∫ u, tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0) u =
      twoScaledConst η θ c₀ D ρ q (κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0)) *
        ∏ j, ρ ^ (resExp η θ Q κ r j + 1) / (resExp η θ Q κ r j + 1) := by

theorem WallChartsData.Phase.ProfileIntegrableOf.of_twoScaled {i : D.ι} {ε : Fin m → Bool}
    {b : Bool} {σ γ : ℝ} {α : Fin m → ℝ} {ν : Type*} [Finite ν] (e : Fin 2 ⊕ ν ≃ Fin m)
    {αS : Fin 2 → ℝ} (hαS : ∀ s, 0 < αS s) (hα : α = fun j ↦ Sum.elim αS 0 (e.symm j))
    (hσ : σ ≠ 0) (htied : ∑ j, P.kappa i j * α j = P.phaseExp i γ)
    (hQα : ∑ j, D.Qexp i j * α j = γ) {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ)
    (hΔ : P.kappa i (e (Sum.inl 0)) * D.Qexp i (e (Sum.inl 1)) -
      P.kappa i (e (Sum.inl 1)) * D.Qexp i (e (Sum.inl 0)) ≠ 0)
    (haS : ∀ s, P.rExp i (e (Sum.inl s)) + 1 =
      η * P.kappa i (e (Sum.inl s)) - θ * D.Qexp i (e (Sum.inl s)))
    (hβ : ∀ j, 0 < P.rExp i (e (Sum.inr j)) + 1 - η * P.kappa i (e (Sum.inr j)) +
      θ * D.Qexp i (e (Sum.inr j))) :
    P.ProfileIntegrableOf i ε b σ γ α := by

theorem WallChartsData.Phase.not_profileIntegrableOf_of_three_scaled {i : D.ι} {ε : Fin m → Bool}
    {b : Bool} {σ γ : ℝ} {α : Fin m → ℝ}
    (hne : (limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α).Nonempty)
    (hcard : 3 ≤ Fintype.card {l // α l ≠ 0}) : ¬ P.ProfileIntegrableOf i ε b σ γ α := by

theorem normalise_restrict_limitMeasure_eq_of_forall_tendsto (hL' : IsOpen L')
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁)
    (htruth₁ : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D₁.ρ i),
      D₁.rep i u ℓ = truthMono (D₁.S i) (D₁.q i) u) (hσ₁ : σ₁ ≠ 0)
    (hfeas₁ : ∀ i ε b, D₁.admissible i ε b σ₁ →
      ConstrainedFeasible (D₁.Qexp i) (P₁.kappa i) γ₁ (P₁.phaseExp i γ₁) (αf₁ i ε b))
    (hprof₁ : ∀ i ε b, D₁.admissible i ε b σ₁ → P₁.ProfileIntegrableOf i ε b σ₁ γ₁ (αf₁ i ε b))
    (hmin₁ : ∀ p : TermIdx D₁, lam₁ ≤ P₁.termLam γ₁ αf₁ p)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂)
    (htruth₂ : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D₂.ρ i),
      D₂.rep i u ℓ = truthMono (D₂.S i) (D₂.q i) u) (hσ₂ : σ₂ ≠ 0)
    (hfeas₂ : ∀ i ε b, D₂.admissible i ε b σ₂ →
      ConstrainedFeasible (D₂.Qexp i) (P₂.kappa i) γ₂ (P₂.phaseExp i γ₂) (αf₂ i ε b))
    (hprof₂ : ∀ i ε b, D₂.admissible i ε b σ₂ → P₂.ProfileIntegrableOf i ε b σ₂ γ₂ (αf₂ i ε b))
    (hmin₂ : ∀ p : TermIdx D₂, lam₂ ≤ P₂.termLam γ₂ αf₂ p)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos₁ : 0 < ∫ z, χ z ∂(P₁.limitMeasure σ₁ γ₁ αf₁ lam₁))
    (hpos₂ : 0 < ∫ z, χ z ∂(P₂.limitMeasure σ₂ γ₂ αf₂ lam₂))
    (hsame : ∀ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ → (∀ z, 0 ≤ ψ z) →
      (∃ M, ∀ z, ψ z ≤ M) → (∀ z, ψ z ≠ 0 → z ∈ L') →
      Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
        (𝓝 0)) :
    normaliseMeasure ((P₁.limitMeasure σ₁ γ₁ αf₁ lam₁).restrict L') =
      normaliseMeasure ((P₂.limitMeasure σ₂ γ₂ αf₂ lam₂).restrict L') := by
```

Conventions: `limitDomain ρ D γ q Q α = pi (if α j = 0 then (0,ρ) else (0,∞)) ∩ {u | Q·α = γ → D ∏ u^{-Q/q} < ρ}`; `tiedDom = 1_{limitDomain} ∏u^r e^{-c₀ ∏u^κ}`; `resExp η θ Q κ r j = r (inr j) − η κ (inr j) + θ Q (inr j)`; `twoScaledConst η θ c₀ D ρ q Δ = Γ(η) c₀^{-η} (D/ρ)^{-(θq)} / (θ|Δ|)`; `partialFace e z = fun j ↦ Sum.elim 0 z (e.symm j)`; `fibreRatio D F ψ χ σ γ t = (totalKernel (e^{-tF}ψ) (σ t^{-γ})).toReal / (totalKernel (e^{-tF}χ) (σ t^{-γ})).toReal`; `ProfileIntegrableOf` = the two certificate integrabilities (envelope × e^{-cΦ₀} and envelope × Φ₀ e^{-cΦ₀}) with c = ma/Ma and the limiting unit |a(u∞)|.

## Questions

(A) Soundness audit of the six statements: hidden vacuity, sign conventions (the LP is κ·α ≥ δ, Q·α ≤ γ; the dual decomposition here is r_S + 1 = η κ_S − θ Q_S), the role of `IsOpen L'`, whether `hne` (nonempty limiting domain) is the right hypothesis for the three-scaled obstruction, and whether the partially tied face density `W(0_T,z,0)(B a(0_T,z,0))^{-λ} ∏ z^{r−λκ}` is what the note should advertise as "the content of the limiting measure on a partially tied face".

(B) Rank the next 3–4 targets. Candidates we see: (i) the mixed truth monomial (e.g. xy = s, Q with two nonzero entries) at the logarithmic endpoint, where the bridge map does not extend continuously to the face point; (ii) the measure-level statement for partially tied faces (the limiting measure as the push-forward of the face density, joining `LimitingMeasure.lean`); (iii) uniformity in σ (the truth parameter) and the variable-truth families of S7; (iv) empirical (finite-sample) versions; (v) making L' open a record field or deriving it; (vi) an "iff" packaging: profile certificate ⇔ isolated LP optimum, in the strict and tied cases. Feel free to propose others. For each: exact statement, why it matters for the note's thesis, main formalisation risk.
