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
nonnegative bounded observable `φ` supported in `L'`, `t^{lam p}/(log t)^{kk p} · K_{p,φ}(t) →
∫ φ dμ_p`, together with the leading order `(lam₀, k₀)` (minimal power, then maximal log order;
computed from the term data by `TermMeasureCertificate.ofTerms`). Its leading measure
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

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)}

namespace TruthChartsData.Phase

variable {T : (Fin (m + 1) → ℝ) → ℝ} {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ}

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
  observable supported in `L'`. -/
  tendsto : ∀ φ : (Fin (m + 1) → ℝ) → ℝ, Continuous φ → (∀ z, 0 ≤ φ z) → (∃ M, ∀ z, φ z ≤ M) →
    (∀ z, φ z ≠ 0 → z ∈ L') →
    ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel φ σ γ p t) atTop
      (𝓝 (∫ z, φ z ∂(μ p)))

attribute [instance] TermMeasureCertificate.finite

namespace TermMeasureCertificate

variable {P : D.Phase F} {σ γ : ℝ}

open scoped Classical in
/-- A certificate from the term data: the leading order is computed (minimal power, then maximal
logarithmic order among the terms of minimal power). -/
noncomputable def ofTerms [Nonempty D.ι] (lam : TermIdx D → ℝ) (kk : TermIdx D → ℕ)
    (μ : TermIdx D → Measure (Fin (m + 1) → ℝ)) (finite : ∀ p, IsFiniteMeasure (μ p))
    (tendsto : ∀ φ : (Fin (m + 1) → ℝ) → ℝ, Continuous φ → (∀ z, 0 ≤ φ z) →
      (∃ M, ∀ z, φ z ≤ M) → (∀ z, φ z ≠ 0 → z ∈ L') →
      ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel φ σ γ p t) atTop
        (𝓝 (∫ z, φ z ∂(μ p)))) :
    P.TermMeasureCertificate σ γ where
  lam := lam
  kk := kk
  μ := μ
  finite := finite
  lam₀ := Finset.univ.inf' Finset.univ_nonempty lam
  k₀ := (Finset.univ.filter fun p ↦ lam p = Finset.univ.inf' Finset.univ_nonempty lam).sup kk
  hmin := fun p ↦ ⟨Finset.inf'_le lam (Finset.mem_univ p), fun h ↦
    Finset.le_sup (f := kk) (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩)⟩
  tendsto := tendsto

variable (C : P.TermMeasureCertificate σ γ)

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
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ L') (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z)
    {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos : (∫ z, χ z ∂C.leadingMeasure) ≠ 0) :
    Tendsto (fun t ↦ D.fibreRatio F ψ χ σ γ t) atTop
      (𝓝 ((∫ z, ψ z ∂C.leadingMeasure) / ∫ z, χ z ∂C.leadingMeasure)) := by
  unfold leadingMeasure lexMeasure at hpos ⊢
  exact P.tendsto_fibre_expectation_lex_measure hS hF hFm hσ hψc hψ hMψ hχc hχ hMχ C.hmin
    (C.tendsto ψ hψc hψ ⟨Mψ, hMψ⟩ hψL) (C.tendsto χ hχc hχ ⟨Mχ, hMχ⟩ hχL) hpos

end TermMeasureCertificate

end TruthChartsData.Phase

open TruthChartsData.Phase in
/-- **Certified phases with the same leading expectations have the same normalised leading
measure** on an open region. -/
theorem TruthChartsData.Phase.TermMeasureCertificate.normalise_eq_of_forall_tendsto
    (hL' : IsOpen L') {T : (Fin (m + 1) → ℝ) → ℝ}
    {D₁ D₂ : TruthChartsData m T L'} {F₁ F₂ : (Fin (m + 1) → ℝ) → ℝ}
    {P₁ : D₁.Phase F₁} {P₂ : D₂.Phase F₂} {σ₁ γ₁ σ₂ γ₂ : ℝ}
    (C₁ : P₁.TermMeasureCertificate σ₁ γ₁) (C₂ : P₂.TermMeasureCertificate σ₂ γ₂)
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos₁ : 0 < ∫ z, χ z ∂C₁.leadingMeasure) (hpos₂ : 0 < ∫ z, χ z ∂C₂.leadingMeasure)
    (hsame : ∀ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ → (∀ z, 0 ≤ ψ z) →
      (∃ M, ∀ z, ψ z ≤ M) → (∀ z, ψ z ≠ 0 → z ∈ L') →
      Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
        (𝓝 0)) :
    normaliseMeasure (C₁.leadingMeasure.restrict L') =
      normaliseMeasure (C₂.leadingMeasure.restrict L') := by
  unfold TermMeasureCertificate.leadingMeasure lexMeasure at hpos₁ hpos₂ ⊢
  refine normalise_restrict_eq_of_forall_ratio_nonneg hL' hpos₁ hpos₂
    fun ψ hψc hψ ⟨M, hM⟩ hψL ↦ ?_
  have h₁ := P₁.tendsto_fibre_expectation_lex_measure hS₁ hF₁ hFm₁ hσ₁ hψc hψ hM hχc hχ hMχ
    C₁.hmin (C₁.tendsto ψ hψc hψ ⟨M, hM⟩ hψL) (C₁.tendsto χ hχc hχ ⟨Mχ, hMχ⟩ hχL) hpos₁.ne'
  have h₂ := P₂.tendsto_fibre_expectation_lex_measure hS₂ hF₂ hFm₂ hσ₂ hψc hψ hM hχc hχ hMχ
    C₂.hmin (C₂.tendsto ψ hψc hψ ⟨M, hM⟩ hψL) (C₂.tendsto χ hχc hχ ⟨Mχ, hMχ⟩ hχL) hpos₂.ne'
  exact sub_eq_zero.mp (tendsto_nhds_unique (h₁.sub h₂) (hsame ψ hψc hψ ⟨M, hM⟩ hψL))

end Laplace.Multi
