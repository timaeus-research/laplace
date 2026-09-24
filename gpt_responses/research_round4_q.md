# Consult: germbij analytic layer, fourth research round (after research_round3)

Same setting as the previous consults (Lean 4 + Mathlib, repo laplace, namespace Laplace.Multi, mirrored on the hironaka wall-atlas branch; germbij = "What expectation values know about the loss landscape"). Since round 3 (research_round3_v1.md) the following landed, zero sorries, standard axioms only:

1. Target 1 (measure-valued partial faces): `PartialFaceMeasure.lean` — `partialMeasure` = push-forward under the ambient face point `ρ_i(bridgePt(partialFace e z, 0))` of the density `A δ^k Γ(λ)/k! ∏_T κ^{-1} · wt|b| (B|a|)^{-λ} ∏_N z^{r−λκ}` on `(0,ρ)^N` (finite by strict gaps and the unit/weight bounds); `tendsto_termKernel_partial_measure` (`t^{γp+δλ}/(log t)^k K_p(φ) → ∫ φ dμ_p`); `tendsto_fibre_expectation_lex_measure` (statement below): term measures μ_p certified at (λ_p,k_p) give ⟨ψ⟩_χ → ∫ψ dμ_*/∫χ dμ_* for μ_* = ∑_{(λ_p,k_p)=(λ_*,k_*)} μ_p. `WallDistinguishabilityLex.lean`: both distinguishability statements for μ_* (equal normalised μ_* ⇒ equal limits; equal limits against a positive reference for all nonnegative bounded continuous ψ supported in the open L' ⇒ equal normalised restrictions to L').

2. Target 2 (mixed truth `xy = s`, core lemma): `MixedTruthLog.lean` — `tendsto_mixedLog` (statement below): `(1/log t) ∫_{σ/(ρt)}^{ρ} f(x, σ/(tx)) dx/x → f(0,0)` for f continuous on the closed box, via `x = ρe^{-Lu}`, `L = log(ρ²t/σ)`, dominated convergence on (0,1); `tendsto_mixedLog_ratio`: for `F = xy·a(x,y)` the fibre expectation on `{xy = σ/t}` → ψ(0,0)/χ(0,0) when w(0,0)χ(0,0) ≠ 0. NOT done: the translation into the record's `fibreKernel`/`totalKernel` conventions (branchKernel with `solvedCoord`, sign branches, atlas weights).

3. Target 3 (certificate ⇔ unique LP minimiser), both halves. Analytic: `CertificateNecessity.lean` — `not_integrable_tiedDom_of_recession` (directions with `d_B ≤ 0`, `d·κ ≤ 0`, `d·Q ≥ 0` if tied truth, `d·(r+1) ≥ 0`), `integrable_vertexDom_iff`, `integrable_tiedDom_twoScaled_iff` (statements below). LP: `CertificateLP.lean` — `UniqueLPMin`, `uniqueLPMin_vertex_iff`, `uniqueLPMin_twoScaled_iff` (statements below), via the identities `a·β − a·α = η(κ·β − δ) [+ θ(γ − Q·β)] + ∑ (reduced cost) β_j` and explicit feasible perturbations.

4. Target 4 (local uniformity in σ): NOT started.

Also from the round-3 audit: the wording "isolated-optimum count closed" was softened in the note as you advised; `IsOpen L'` stays a theorem-level hypothesis.

## Statements (Lean, verbatim)

```lean
theorem tendsto_fibre_expectation_lex_measure (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F) (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ)
    (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ} (hMψ : ∀ z, ψ z ≤ Mψ) (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z)
    {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) {lam : TermIdx D → ℝ} {kk : TermIdx D → ℕ}
    {μ : TermIdx D → Measure (Fin (m + 1) → ℝ)} [∀ p, IsFiniteMeasure (μ p)] {lam₀ : ℝ} {k₀ : ℕ}
    (hmin : ∀ p, lam₀ ≤ lam p ∧ (lam p = lam₀ → kk p ≤ k₀))
    (hKψ : ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel ψ σ γ p t) atTop
      (𝓝 (∫ z, ψ z ∂(μ p))))
    (hKχ : ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel χ σ γ p t) atTop
      (𝓝 (∫ z, χ z ∂(μ p))))
    (hpos : (∫ z, χ z ∂(∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), μ p)) ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal)
      atTop
      (𝓝 ((∫ z, ψ z ∂(∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), μ p)) /
        ∫ z, χ z ∂(∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), μ p))) := by

theorem tendsto_mixedLog (hρ : 0 < ρ) (hσ : 0 < σ) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ ↦ f p.1 p.2) (Icc 0 ρ ×ˢ Icc 0 ρ)) :
    Tendsto (fun t ↦ (∫ x in Ioo (σ / (ρ * t)) ρ, f x (σ / (t * x)) / x) / log t) atTop
      (𝓝 (f 0 0)) := by

theorem integrable_vertexDom_iff {ρ D γ q δ c₀ : ℝ} {Q κ r α : Fin (k + 1) → ℝ} (hρ : 0 < ρ)
    (hD : 0 ≤ D) (hq : 0 < q) (hc₀ : 0 < c₀) (hκ : ∀ i, 0 < κ i) (s : Fin (k + 1))
    (hα : ∀ i, α i = if i = s then δ / κ s else 0) (hδκ : 0 < δ / κ s)
    (hstrict : ∑ i, Q i * α i < γ) :
    Integrable (vertexDom ρ D γ q c₀ Q κ r α) ↔
      0 < (r s + 1) / κ s ∧ ∀ j, j ≠ s → κ j * ((r s + 1) / κ s) < r j + 1 := by

theorem integrable_tiedDom_twoScaled_iff {ρ D γ q c₀ η θ : ℝ} {Q κ r : Fin 2 ⊕ ν → ℝ}
    {αS : Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hc₀ : 0 < c₀)
    (hne : (limitDomain ρ D γ q Q (Sum.elim αS 0)).Nonempty) (hαS : ∀ s, 0 < αS s)
    (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ s, r (Sum.inl s) + 1 = η * κ (Sum.inl s) - θ * Q (Sum.inl s)) :
    Integrable (tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0)) ↔
      0 < η ∧ 0 < θ ∧ ∀ j, -1 < resExp η θ Q κ r j := by

theorem uniqueLPMin_vertex_iff (hκ : ∀ i, 0 < κ i) (hQ : ∀ i, 0 ≤ Q i) (s : ι)
    (hα : ∀ i, α i = if i = s then δ / κ s else 0) (hδ : 0 < δ) (hstrict : ∑ i, Q i * α i < γ) :
    UniqueLPMin Q κ γ δ a α ↔ 0 < a s / κ s ∧ ∀ j, j ≠ s → κ j * (a s / κ s) < a j := by

theorem uniqueLPMin_twoScaled_iff (hαS : ∀ s, 0 < αS s)
    (hκα : ∑ i, κ i * Sum.elim αS 0 i = δ) (hQα : ∑ i, Q i * Sum.elim αS 0 i = γ)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ s, a (Sum.inl s) = η * κ (Sum.inl s) - θ * Q (Sum.inl s)) :
    UniqueLPMin Q κ γ δ a (Sum.elim αS 0) ↔
      0 < η ∧ 0 < θ ∧ ∀ j, 0 < a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j) := by
```

Conventions: `UniqueLPMin Q κ γ δ a α := ConstrainedFeasible Q κ γ δ α ∧ ∀ β, ConstrainedFeasible Q κ γ δ β → β ≠ α → ∑ a α < ∑ a β` with `ConstrainedFeasible Q κ γ δ α := (∀ j, 0 ≤ α j) ∧ ∑ Q α ≤ γ ∧ δ ≤ ∑ κ α`; `tiedDom = vertexDom = 1_{limitDomain} ∏u^r e^{-c₀∏u^κ}`; `resExp η θ Q κ r j = r_j − ηκ_j + θQ_j`; `TermIdx D = D.ι × (Fin m → Bool) × Bool`; `termKernel φ σ γ p t` = the model kernel of the branch `p` (0 if inadmissible).

## Questions

(A) Audit the six statements for soundness and for misleading hypotheses. In particular: (i) in `uniqueLPMin_vertex_iff` we assume `Q ≥ 0` and `κ > 0` — is `Q ≥ 0` needed (we used it for feasibility of the perturbation along e_s)? (ii) in the tied LP theorem there is no `Q ≥ 0`, no `κ > 0` — is that right? (iii) `tendsto_fibre_expectation_lex_measure` quantifies the certificates `hKψ hKχ` only for the two observables at hand — is this the right interface, or should the term measures be required to work for all admissible observables? (iv) does `tendsto_mixedLog` really capture the "mixed truth" wall term, i.e. what is the correct identification of `∫ f(x, σ/(tx)) dx/x` with the record's fibre kernel for the chart with truth monomial `xy` (we believe `branchKernel` with `q = (1,1)`, `k = 0` gives `Φ(s/w, w)/w` on the positive branch)?

(B) Rank the next 3–4 targets for the note's thesis ("expectation values know exactly the normalised coefficient measure; the LP tells which faces carry it"), now that the round-3 list is done except σ-uniformity. Candidates: (i) local uniformity in σ / the variable-parameter corollary σ(t) → σ₀ (your round-3 target 4); (ii) the record-level mixed-truth term (bookkeeping into `fibreKernel`, a 2D instance record with truth monomial `xy` like the existing toy/blow-up instances); (iii) the degenerate LP cases (tied one-coordinate vertex, Δ = 0, zero reduced costs) — what is the right statement, or is this where the face asymptotics take over; (iv) a "face classification" theorem: for a product-like chart with Q = 0, the LP's optimal face is a coordinate face, and the dominant term is a point mass (fully tied), a vertex, or a partial face density — a single theorem matching the LP geometry to the three coefficient-measure shapes; (v) anything on the hironaka side (the wall-atlas branch has the end-to-end `wall_fibre_expectation` consuming this layer; is there a natural next ambient statement?); (vi) numerical validation of a partially tied face density or the two-scaled constant (which example would be most convincing?). For each: exact statement, value for the thesis, main formalisation risk.
