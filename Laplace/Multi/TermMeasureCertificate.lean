/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallDistinguishabilityLex

/-!
# The coefficient certificate of a phase

The universal interface for the leading coefficients of the wall terms: a
`TermMeasureCertificate` of a phase `P` at `(σ, γ)` assigns to every term `p` a power `lam p`, a
logarithmic order `kk p` and a finite coefficient measure `μ p` such that, for **every** continuous
nonnegative bounded observable `φ`, `t^{lam p}/(log t)^{kk p} · K_{p,φ}(t) → ∫ φ dμ_p`, together
with the leading order `(lam₀, k₀)` (minimal power, then maximal log order). Its leading measure
`μ_* = ∑_{(lam_p,kk_p)=(lam₀,k₀)} μ_p` (`leadingMeasure`) assembles the chart contributions
(`TermMeasureCertificate.tendsto_fibre_expectation`: the fibre expectation of every observable
converges to `∫ψ dμ_*/∫χ dμ_*` when `∫χ dμ_* ≠ 0`), and two certified phases with the same
leading expectations have the same normalised leading measure on an open `L'`
(`TermMeasureCertificate.normalise_eq_of_forall_tendsto`). The certificate is a common interface
for established asymptotics — a vertex, a fully tied face or a partially tied face certifies its
term — not a claim that every chart has such an asymptotic (Astra, round 5, target 2).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData.Phase

variable {D : WallChartsData m ℓ L'} {F : (Fin (m + 1) → ℝ) → ℝ}

/-- A coefficient certificate of the phase `P` at the parameters `(σ, γ)`. -/
structure TermMeasureCertificate (P : D.Phase F) (σ γ : ℝ) where
  /-- The power of each term. -/
  lam : TermIdx D → ℝ
  /-- The logarithmic order of each term. -/
  kk : TermIdx D → ℕ
  /-- The coefficient measure of each term. -/
  μ : TermIdx D → Measure (Fin (m + 1) → ℝ)
  finite : ∀ p, IsFiniteMeasure (μ p)
  /-- The leading order: minimal power, then maximal logarithmic order. -/
  lam₀ : ℝ
  k₀ : ℕ
  hmin : ∀ p, lam₀ ≤ lam p ∧ (lam p = lam₀ → kk p ≤ k₀)
  /-- The certified asymptotic of every term against every continuous nonnegative bounded
  observable. -/
  tendsto : ∀ φ : (Fin (m + 1) → ℝ) → ℝ, Continuous φ → (∀ z, 0 ≤ φ z) → (∃ M, ∀ z, φ z ≤ M) →
    ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel φ σ γ p t) atTop
      (𝓝 (∫ z, φ z ∂(μ p)))

attribute [instance] TermMeasureCertificate.finite

namespace TermMeasureCertificate

variable {P : D.Phase F} {σ γ : ℝ} (C : P.TermMeasureCertificate σ γ)

/-- The leading coefficient measure: the sum of the coefficient measures of the terms of leading
order. -/
noncomputable def leadingMeasure : Measure (Fin (m + 1) → ℝ) :=
  lexMeasure C.lam C.kk C.μ C.lam₀ C.k₀

instance : IsFiniteMeasure C.leadingMeasure := by
  unfold leadingMeasure lexMeasure
  infer_instance

/-- **The fibre expectation of a certified phase.** -/
theorem tendsto_fibre_expectation (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z) (hFm : Measurable F)
    (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ)
    (hpos : (∫ z, χ z ∂C.leadingMeasure) ≠ 0) :
    Tendsto (fun t ↦ D.fibreRatio F ψ χ σ γ t) atTop
      (𝓝 ((∫ z, ψ z ∂C.leadingMeasure) / ∫ z, χ z ∂C.leadingMeasure)) := by
  unfold leadingMeasure lexMeasure at hpos ⊢
  exact P.tendsto_fibre_expectation_lex_measure hS hF hFm hσ hψc hψ hMψ hχc hχ hMχ C.hmin
    (C.tendsto ψ hψc hψ ⟨Mψ, hMψ⟩) (C.tendsto χ hχc hχ ⟨Mχ, hMχ⟩) hpos

end TermMeasureCertificate

end WallChartsData.Phase

open WallChartsData.Phase in
/-- **Certified phases with the same leading expectations have the same normalised leading
measure** on an open region. -/
theorem WallChartsData.Phase.TermMeasureCertificate.normalise_eq_of_forall_tendsto
    (hL' : IsOpen L') {D₁ D₂ : WallChartsData m ℓ L'} {F₁ F₂ : (Fin (m + 1) → ℝ) → ℝ}
    {P₁ : D₁.Phase F₁} {P₂ : D₂.Phase F₂} {σ₁ γ₁ σ₂ γ₂ : ℝ}
    (C₁ : P₁.TermMeasureCertificate σ₁ γ₁) (C₂ : P₂.TermMeasureCertificate σ₂ γ₂)
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ) (hpos₁ : 0 < ∫ z, χ z ∂C₁.leadingMeasure)
    (hpos₂ : 0 < ∫ z, χ z ∂C₂.leadingMeasure)
    (hsame : ∀ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ → (∀ z, 0 ≤ ψ z) →
      (∃ M, ∀ z, ψ z ≤ M) → (∀ z, ψ z ≠ 0 → z ∈ L') →
      Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
        (𝓝 0)) :
    normaliseMeasure (C₁.leadingMeasure.restrict L') =
      normaliseMeasure (C₂.leadingMeasure.restrict L') := by
  unfold TermMeasureCertificate.leadingMeasure at hpos₁ hpos₂ ⊢
  exact normalise_restrict_lexMeasure_eq_of_forall_tendsto (P₁ := P₁) (P₂ := P₂) hL' hS₁ hF₁ hFm₁
    hσ₁ hS₂ hF₂ hFm₂ hσ₂ hχc hχ hMχ C₁.hmin C₁.tendsto C₂.hmin C₂.tendsto hpos₁ hpos₂ hsame

end Laplace.Multi
