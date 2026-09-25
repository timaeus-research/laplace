/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.NormalisedMeasure
import Laplace.Multi.LimitingMeasure

/-!
# Distinguishability: what the leading expectations know

Two wall-chart phases (two loss landscapes over the same region `L'`) have the same leading
normalised expectations `lim ⟨ψ⟩_χ` for all certified observables exactly when their limiting
measures have the same normalisation on `L'`:

* `tendsto_fibreRatio_sub_of_normalise_eq`: equal normalised limiting measures give equal
  limits for every pair of certified observables (`ratio_eq_of_normalise_eq` and the
  measure-form fibre expectation theorem);
* `normalise_restrict_limitMeasure_eq_of_forall_tendsto`: if `L'` is open and the two fibre
  expectations against a fixed positive reference observable `χ` have the same limit for every
  nonnegative bounded continuous `ψ` supported in `L'`, the normalised restrictions to `L'` of
  the two limiting measures agree (`normalise_restrict_eq_of_forall_ratio_nonneg`).

So the leading expectations know the normalised limiting measure on `L'` and nothing else: not
the mass, not the dominant power or logarithmic scale, not what the face maps erase (Astra's
target (3), `research_partial_v1.md`).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

namespace TruthChartsData

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)}

/-- The fibre expectation of `ψ` against `χ` at `t`: the ratio of the two total kernels at
`σ t^{-γ}`. -/
noncomputable def fibreRatio {T : (Fin (m + 1) → ℝ) → ℝ}
    (D : TruthChartsData m T L') (F : (Fin (m + 1) → ℝ) → ℝ)
    (ψ χ : (Fin (m + 1) → ℝ) → ℝ) (σ γ t : ℝ) : ℝ :=
  (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
    (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal

namespace Phase

variable {T : (Fin (m + 1) → ℝ) → ℝ}
  {D₁ D₂ : TruthChartsData m T L'} {F₁ F₂ : (Fin (m + 1) → ℝ) → ℝ}
  (P₁ : D₁.Phase F₁) (P₂ : D₂.Phase F₂)
  {σ₁ γ₁ : ℝ} {αf₁ : D₁.ι → (Fin m → Bool) → Bool → Fin m → ℝ} {lam₁ : ℝ}
  {σ₂ γ₂ : ℝ} {αf₂ : D₂.ι → (Fin m → Bool) → Bool → Fin m → ℝ} {lam₂ : ℝ}

/-- **Equal normalised limiting measures give equal leading expectations**, for every pair of
certified observables. -/
theorem tendsto_fibreRatio_sub_of_normalise_eq
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁)
    (htruth₁ : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D₁.ρ i),
      T (D₁.rep i u) = truthMono (D₁.S i) (D₁.q i) u) (hσ₁ : σ₁ ≠ 0)
    (hfeas₁ : ∀ i ε b, D₁.admissible i ε b σ₁ →
      ConstrainedFeasible (D₁.Qexp i) (P₁.kappa i) γ₁ (P₁.phaseExp i γ₁) (αf₁ i ε b))
    (hprof₁ : ∀ i ε b, D₁.admissible i ε b σ₁ → P₁.ProfileIntegrableOf i ε b σ₁ γ₁ (αf₁ i ε b))
    (hmin₁ : ∀ p : TermIdx D₁, lam₁ ≤ P₁.termLam γ₁ αf₁ p)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂)
    (htruth₂ : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D₂.ρ i),
      T (D₂.rep i u) = truthMono (D₂.S i) (D₂.q i) u) (hσ₂ : σ₂ ≠ 0)
    (hfeas₂ : ∀ i ε b, D₂.admissible i ε b σ₂ →
      ConstrainedFeasible (D₂.Qexp i) (P₂.kappa i) γ₂ (P₂.phaseExp i γ₂) (αf₂ i ε b))
    (hprof₂ : ∀ i ε b, D₂.admissible i ε b σ₂ → P₂.ProfileIntegrableOf i ε b σ₂ γ₂ (αf₂ i ε b))
    (hmin₂ : ∀ p : TermIdx D₂, lam₂ ≤ P₂.termLam γ₂ αf₂ p)
    {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ L') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos₁ : (∫ z, χ z ∂(P₁.limitMeasure σ₁ γ₁ αf₁ lam₁)) ≠ 0)
    (hpos₂ : (∫ z, χ z ∂(P₂.limitMeasure σ₂ γ₂ αf₂ lam₂)) ≠ 0)
    (hnorm : normaliseMeasure (P₁.limitMeasure σ₁ γ₁ αf₁ lam₁) =
      normaliseMeasure (P₂.limitMeasure σ₂ γ₂ αf₂ lam₂)) :
    Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
      (𝓝 0) := by
  have hfin₁ := P₁.isFiniteMeasure_limitMeasure σ₁ γ₁ αf₁ lam₁ hσ₁ hprof₁
  have hfin₂ := P₂.isFiniteMeasure_limitMeasure σ₂ γ₂ αf₂ lam₂ hσ₂ hprof₂
  have h₁ := P₁.tendsto_fibre_expectation_measure hS₁ hF₁ hFm₁ htruth₁ hσ₁ hψc hψ hMψ hψL hχc hχ
    hMχ hχL hfeas₁ hprof₁ hmin₁ hpos₁
  have h₂ := P₂.tendsto_fibre_expectation_measure hS₂ hF₂ hFm₂ htruth₂ hσ₂ hψc hψ hMψ hψL hχc hχ
    hMχ hχL hfeas₂ hprof₂ hmin₂ hpos₂
  have e := ratio_eq_of_normalise_eq hnorm ψ χ hpos₁ hpos₂
  have := h₁.sub h₂
  rw [e, sub_self] at this
  exact this

/-- **Equal leading expectations determine the normalised limiting measure on `L'`.** If `L'` is
open and, against a fixed positive reference observable `χ`, the two fibre expectations have
the same limit for every nonnegative bounded continuous `ψ` supported in `L'`, then the
normalised restrictions of the two limiting measures to `L'` agree. -/
theorem normalise_restrict_limitMeasure_eq_of_forall_tendsto (hL' : IsOpen L')
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁)
    (htruth₁ : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D₁.ρ i),
      T (D₁.rep i u) = truthMono (D₁.S i) (D₁.q i) u) (hσ₁ : σ₁ ≠ 0)
    (hfeas₁ : ∀ i ε b, D₁.admissible i ε b σ₁ →
      ConstrainedFeasible (D₁.Qexp i) (P₁.kappa i) γ₁ (P₁.phaseExp i γ₁) (αf₁ i ε b))
    (hprof₁ : ∀ i ε b, D₁.admissible i ε b σ₁ → P₁.ProfileIntegrableOf i ε b σ₁ γ₁ (αf₁ i ε b))
    (hmin₁ : ∀ p : TermIdx D₁, lam₁ ≤ P₁.termLam γ₁ αf₁ p)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂)
    (htruth₂ : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D₂.ρ i),
      T (D₂.rep i u) = truthMono (D₂.S i) (D₂.q i) u) (hσ₂ : σ₂ ≠ 0)
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
  have hfin₁ := P₁.isFiniteMeasure_limitMeasure σ₁ γ₁ αf₁ lam₁ hσ₁ hprof₁
  have hfin₂ := P₂.isFiniteMeasure_limitMeasure σ₂ γ₂ αf₂ lam₂ hσ₂ hprof₂
  refine normalise_restrict_eq_of_forall_ratio_nonneg hL' hpos₁ hpos₂
    fun ψ hψc hψ ⟨M, hM⟩ hψL ↦ ?_
  have h₁ := P₁.tendsto_fibre_expectation_measure hS₁ hF₁ hFm₁ htruth₁ hσ₁ hψc hψ hM hψL hχc hχ
    hMχ hχL hfeas₁ hprof₁ hmin₁ hpos₁.ne'
  have h₂ := P₂.tendsto_fibre_expectation_measure hS₂ hF₂ hFm₂ htruth₂ hσ₂ hψc hψ hM hψL hχc hχ
    hMχ hχL hfeas₂ hprof₂ hmin₂ hpos₂.ne'
  exact sub_eq_zero.mp (tendsto_nhds_unique (h₁.sub h₂) (hsame ψ hψc hψ ⟨M, hM⟩ hψL))

end Phase

end TruthChartsData

end Laplace.Multi
