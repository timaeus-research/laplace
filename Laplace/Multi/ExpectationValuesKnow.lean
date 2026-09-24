/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TermMeasureCertificate

/-!
# What the leading expectations know

The headline of the analytic layer in certificate language. For two certified phases and a
reference observable `χ` supported in the open region `L'` with positive leading integrals, the
leading fibre expectations agree for every observable supported in `L'` **if and only if** the
normalised leading measures restricted to `L'` agree
(`TermMeasureCertificate.normalise_restrict_eq_iff_forall_tendsto`). The expectations therefore
know exactly the normalised leading coefficient measure on the region tested by the observables,
and nothing about mass carried outside it (Astra, round 6: the projective leading measure on
precisely the region tested).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-- An observable vanishing off `U` integrates the same against `μ` and against `μ|_U`. -/
theorem integral_eq_integral_restrict_of_vanish {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {U : Set X} {ψ : X → ℝ} (hψU : ∀ x, ψ x ≠ 0 → x ∈ U) :
    ∫ x, ψ x ∂μ = ∫ x in U, ψ x ∂μ :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    by_contra h
    exact hx (hψU x h)).symm

namespace WallChartsData.Phase.TermMeasureCertificate

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}
  {D₁ D₂ : WallChartsData m ℓ L'} {F₁ F₂ : (Fin (m + 1) → ℝ) → ℝ}
  {P₁ : D₁.Phase F₁} {P₂ : D₂.Phase F₂} {σ₁ γ₁ σ₂ γ₂ : ℝ}
  (C₁ : P₁.TermMeasureCertificate σ₁ γ₁) (C₂ : P₂.TermMeasureCertificate σ₂ γ₂)

/-- Equal normalised leading measures on `L'` give equal leading expectations of every observable
supported in `L'`. -/
theorem tendsto_fibreRatio_sub_of_normalise_restrict_eq (hL' : IsOpen L')
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos₁ : 0 < ∫ z, χ z ∂C₁.leadingMeasure) (hpos₂ : 0 < ∫ z, χ z ∂C₂.leadingMeasure)
    (hnorm : normaliseMeasure (C₁.leadingMeasure.restrict L') =
      normaliseMeasure (C₂.leadingMeasure.restrict L'))
    {ψ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
      (𝓝 0) := by
  have h₁ := C₁.tendsto_fibre_expectation hS₁ hF₁ hFm₁ hσ₁ hψc hψ hMψ hψL hχc hχ hMχ hχL hpos₁.ne'
  have h₂ := C₂.tendsto_fibre_expectation hS₂ hF₂ hFm₂ hσ₂ hψc hψ hMψ hψL hχc hχ hMχ hχL hpos₂.ne'
  have hU := hL'.measurableSet
  have e : (∫ z, ψ z ∂C₁.leadingMeasure) / ∫ z, χ z ∂C₁.leadingMeasure =
      (∫ z, ψ z ∂C₂.leadingMeasure) / ∫ z, χ z ∂C₂.leadingMeasure := by
    rw [integral_eq_integral_restrict_of_vanish (μ := C₁.leadingMeasure) hψL,
      integral_eq_integral_restrict_of_vanish (μ := C₁.leadingMeasure) hχL,
      integral_eq_integral_restrict_of_vanish (μ := C₂.leadingMeasure) hψL,
      integral_eq_integral_restrict_of_vanish (μ := C₂.leadingMeasure) hχL]
    refine ratio_eq_of_normalise_eq hnorm ψ χ ?_ ?_
    · rw [← integral_eq_integral_restrict_of_vanish hχL]
      exact hpos₁.ne'
    · rw [← integral_eq_integral_restrict_of_vanish hχL]
      exact hpos₂.ne'
  have := h₁.sub h₂
  rw [e, sub_self] at this
  exact this

/-- **What the leading expectations know.** For two certified phases and a reference observable
supported in the open region `L'`, the leading fibre expectations agree for every observable
supported in `L'` if and only if the normalised leading measures on `L'` agree. -/
theorem normalise_restrict_eq_iff_forall_tendsto (hL' : IsOpen L')
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos₁ : 0 < ∫ z, χ z ∂C₁.leadingMeasure) (hpos₂ : 0 < ∫ z, χ z ∂C₂.leadingMeasure) :
    normaliseMeasure (C₁.leadingMeasure.restrict L') =
        normaliseMeasure (C₂.leadingMeasure.restrict L') ↔
      ∀ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ → (∀ z, 0 ≤ ψ z) → (∃ M, ∀ z, ψ z ≤ M) →
        (∀ z, ψ z ≠ 0 → z ∈ L') →
        Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
          (𝓝 0) := by
  constructor
  · intro hnorm ψ hψc hψ ⟨M, hM⟩ hψL
    exact C₁.tendsto_fibreRatio_sub_of_normalise_restrict_eq C₂ hL' hS₁ hF₁ hFm₁ hσ₁ hS₂ hF₂ hFm₂
      hσ₂ hχc hχ hMχ hχL hpos₁ hpos₂ hnorm hψc hψ hM hψL
  · intro hsame
    exact WallChartsData.Phase.TermMeasureCertificate.normalise_eq_of_forall_tendsto hL' C₁ C₂ hS₁
      hF₁ hFm₁ hσ₁ hS₂ hF₂ hFm₂ hσ₂ hχc hχ hMχ hχL hpos₁ hpos₂ hsame

end WallChartsData.Phase.TermMeasureCertificate

end Laplace.Multi
