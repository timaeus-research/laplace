/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PartialFaceMeasure
import Laplace.Multi.WallDistinguishability

/-!
# Distinguishability for the lexicographic coefficient measure

The two distinguishability statements of `WallDistinguishability` lifted from the isolated-profile
limiting measure to the lexicographic coefficient measure `μ_* = ∑_{(λ_p,k_p)=(λ_*,k_*)} μ_p` of
`PartialFaceMeasure` (logarithmic and power-law terms alike):
`tendsto_fibreRatio_sub_of_normalise_eq_lex` (equal normalised coefficient measures give equal
leading expectations) and `normalise_restrict_lexMeasure_eq_of_forall_tendsto` (equal leading
expectations against a fixed positive reference observable determine the normalised restriction
of the coefficient measure to the open region `L'`).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

namespace WallChartsData.Phase

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}
  {D₁ D₂ : WallChartsData m ℓ L'} {F₁ F₂ : (Fin (m + 1) → ℝ) → ℝ}
  (P₁ : D₁.Phase F₁) (P₂ : D₂.Phase F₂) {σ₁ γ₁ σ₂ γ₂ : ℝ}

/-- The lexicographic coefficient measure of a family of term measures. -/
noncomputable def lexMeasure {D : WallChartsData m ℓ L'} (lam : TermIdx D → ℝ)
    (kk : TermIdx D → ℕ) (μ : TermIdx D → Measure (Fin (m + 1) → ℝ)) (lam₀ : ℝ) (k₀ : ℕ) :
    Measure (Fin (m + 1) → ℝ) :=
  ∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), μ p

instance {D : WallChartsData m ℓ L'} (lam : TermIdx D → ℝ) (kk : TermIdx D → ℕ)
    (μ : TermIdx D → Measure (Fin (m + 1) → ℝ)) [∀ p, IsFiniteMeasure (μ p)] (lam₀ : ℝ)
    (k₀ : ℕ) : IsFiniteMeasure (lexMeasure lam kk μ lam₀ k₀) :=
  inferInstanceAs (IsFiniteMeasure (∑ p ∈ _, μ p))

/-- **Equal normalised coefficient measures give equal leading expectations.** -/
theorem tendsto_fibreRatio_sub_of_normalise_eq_lex (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z)
    (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0) (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z)
    (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ)
    {lam₁ : TermIdx D₁ → ℝ} {kk₁ : TermIdx D₁ → ℕ} {μ₁ : TermIdx D₁ → Measure (Fin (m + 1) → ℝ)}
    [∀ p, IsFiniteMeasure (μ₁ p)] {lam₁₀ : ℝ} {k₁₀ : ℕ}
    (hmin₁ : ∀ p, lam₁₀ ≤ lam₁ p ∧ (lam₁ p = lam₁₀ → kk₁ p ≤ k₁₀))
    (hKψ₁ : ∀ p, Tendsto (fun t ↦ t ^ lam₁ p / log t ^ kk₁ p * P₁.termKernel ψ σ₁ γ₁ p t) atTop
      (𝓝 (∫ z, ψ z ∂(μ₁ p))))
    (hKχ₁ : ∀ p, Tendsto (fun t ↦ t ^ lam₁ p / log t ^ kk₁ p * P₁.termKernel χ σ₁ γ₁ p t) atTop
      (𝓝 (∫ z, χ z ∂(μ₁ p))))
    {lam₂ : TermIdx D₂ → ℝ} {kk₂ : TermIdx D₂ → ℕ} {μ₂ : TermIdx D₂ → Measure (Fin (m + 1) → ℝ)}
    [∀ p, IsFiniteMeasure (μ₂ p)] {lam₂₀ : ℝ} {k₂₀ : ℕ}
    (hmin₂ : ∀ p, lam₂₀ ≤ lam₂ p ∧ (lam₂ p = lam₂₀ → kk₂ p ≤ k₂₀))
    (hKψ₂ : ∀ p, Tendsto (fun t ↦ t ^ lam₂ p / log t ^ kk₂ p * P₂.termKernel ψ σ₂ γ₂ p t) atTop
      (𝓝 (∫ z, ψ z ∂(μ₂ p))))
    (hKχ₂ : ∀ p, Tendsto (fun t ↦ t ^ lam₂ p / log t ^ kk₂ p * P₂.termKernel χ σ₂ γ₂ p t) atTop
      (𝓝 (∫ z, χ z ∂(μ₂ p))))
    (hpos₁ : (∫ z, χ z ∂(lexMeasure lam₁ kk₁ μ₁ lam₁₀ k₁₀)) ≠ 0)
    (hpos₂ : (∫ z, χ z ∂(lexMeasure lam₂ kk₂ μ₂ lam₂₀ k₂₀)) ≠ 0)
    (hnorm : normaliseMeasure (lexMeasure lam₁ kk₁ μ₁ lam₁₀ k₁₀) =
      normaliseMeasure (lexMeasure lam₂ kk₂ μ₂ lam₂₀ k₂₀)) :
    Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
      (𝓝 0) := by
  have h₁ := P₁.tendsto_fibre_expectation_lex_measure hS₁ hF₁ hFm₁ hσ₁ hψc hψ hMψ hχc hχ hMχ hmin₁
    hKψ₁ hKχ₁ hpos₁
  have h₂ := P₂.tendsto_fibre_expectation_lex_measure hS₂ hF₂ hFm₂ hσ₂ hψc hψ hMψ hχc hχ hMχ hmin₂
    hKψ₂ hKχ₂ hpos₂
  have e := ratio_eq_of_normalise_eq hnorm ψ χ hpos₁ hpos₂
  unfold lexMeasure at e
  have := h₁.sub h₂
  rw [e, sub_self] at this
  exact this

/-- **Equal leading expectations determine the normalised coefficient measure on `L'`.** -/
theorem normalise_restrict_lexMeasure_eq_of_forall_tendsto (hL' : IsOpen L')
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ)
    {lam₁ : TermIdx D₁ → ℝ} {kk₁ : TermIdx D₁ → ℕ} {μ₁ : TermIdx D₁ → Measure (Fin (m + 1) → ℝ)}
    [∀ p, IsFiniteMeasure (μ₁ p)] {lam₁₀ : ℝ} {k₁₀ : ℕ}
    (hmin₁ : ∀ p, lam₁₀ ≤ lam₁ p ∧ (lam₁ p = lam₁₀ → kk₁ p ≤ k₁₀))
    (hK₁ : ∀ φ : (Fin (m + 1) → ℝ) → ℝ, Continuous φ → (∀ z, 0 ≤ φ z) → (∃ M, ∀ z, φ z ≤ M) →
      ∀ p, Tendsto (fun t ↦ t ^ lam₁ p / log t ^ kk₁ p * P₁.termKernel φ σ₁ γ₁ p t) atTop
        (𝓝 (∫ z, φ z ∂(μ₁ p))))
    {lam₂ : TermIdx D₂ → ℝ} {kk₂ : TermIdx D₂ → ℕ} {μ₂ : TermIdx D₂ → Measure (Fin (m + 1) → ℝ)}
    [∀ p, IsFiniteMeasure (μ₂ p)] {lam₂₀ : ℝ} {k₂₀ : ℕ}
    (hmin₂ : ∀ p, lam₂₀ ≤ lam₂ p ∧ (lam₂ p = lam₂₀ → kk₂ p ≤ k₂₀))
    (hK₂ : ∀ φ : (Fin (m + 1) → ℝ) → ℝ, Continuous φ → (∀ z, 0 ≤ φ z) → (∃ M, ∀ z, φ z ≤ M) →
      ∀ p, Tendsto (fun t ↦ t ^ lam₂ p / log t ^ kk₂ p * P₂.termKernel φ σ₂ γ₂ p t) atTop
        (𝓝 (∫ z, φ z ∂(μ₂ p))))
    (hpos₁ : 0 < ∫ z, χ z ∂(lexMeasure lam₁ kk₁ μ₁ lam₁₀ k₁₀))
    (hpos₂ : 0 < ∫ z, χ z ∂(lexMeasure lam₂ kk₂ μ₂ lam₂₀ k₂₀))
    (hsame : ∀ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ → (∀ z, 0 ≤ ψ z) →
      (∃ M, ∀ z, ψ z ≤ M) → (∀ z, ψ z ≠ 0 → z ∈ L') →
      Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
        (𝓝 0)) :
    normaliseMeasure ((lexMeasure lam₁ kk₁ μ₁ lam₁₀ k₁₀).restrict L') =
      normaliseMeasure ((lexMeasure lam₂ kk₂ μ₂ lam₂₀ k₂₀).restrict L') := by
  unfold lexMeasure at hpos₁ hpos₂ ⊢
  refine normalise_restrict_eq_of_forall_ratio_nonneg hL' hpos₁ hpos₂
    fun ψ hψc hψ ⟨M, hM⟩ hψL ↦ ?_
  have h₁ := P₁.tendsto_fibre_expectation_lex_measure hS₁ hF₁ hFm₁ hσ₁ hψc hψ hM hχc hχ hMχ hmin₁
    (hK₁ ψ hψc hψ ⟨M, hM⟩) (hK₁ χ hχc hχ ⟨Mχ, hMχ⟩) hpos₁.ne'
  have h₂ := P₂.tendsto_fibre_expectation_lex_measure hS₂ hF₂ hFm₂ hσ₂ hψc hψ hM hχc hχ hMχ hmin₂
    (hK₂ ψ hψc hψ ⟨M, hM⟩) (hK₂ χ hχc hχ ⟨Mχ, hMχ⟩) hpos₂.ne'
  exact sub_eq_zero.mp (tendsto_nhds_unique (h₁.sub h₂) (hsame ψ hψc hψ ⟨M, hM⟩ hψL))

end WallChartsData.Phase

end Laplace.Multi
