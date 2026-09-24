/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallFibreExpectation
import Laplace.Multi.PowerLogAssembly

/-!
# The expectation along the truth fibre, certifying only the dominant terms

Astra's review (`review_endtoend_v1`, §1.1, §5): the theorem `tendsto_fibre_expectation` demands a
certificate for every admissible term at its own scale, so an irrelevant chart can block it. Here
only a set `S` of terms is certified (feasible scale and integrable profile), every other term is
assumed negligible at the dominant normalisation `t^{λ₀}` for both observables, and the assembly
with negligible terms (`tendsto_sum_ratio_powLog`, `k₀ = 0`) gives the ratio limit
(`tendsto_fibre_expectation_dominant`). Negligibility can be supplied by any means — a certificate
at a larger exponent (`tendsto_negligible_of_certified`), a logarithmic sandwich, or a vanishing
weight.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData.Phase

variable {D : WallChartsData m ℓ L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {σ γ : ℝ}

open scoped Classical in
/-- **The expectation along the truth fibre with a certified dominant set.** -/
theorem tendsto_fibre_expectation_dominant (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ L') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ} (S : Finset (TermIdx D)) {lam₀ : ℝ}
    (hadm : ∀ p ∈ S, D.admissible p.1 p.2.1 p.2.2 σ)
    (hlam : ∀ p ∈ S, P.termLam γ α p = lam₀)
    (hfeas : ∀ p ∈ S, ConstrainedFeasible (D.Qexp p.1) (P.kappa p.1) γ (P.phaseExp p.1 γ)
      (α p.1 p.2.1 p.2.2))
    (hprof : ∀ p ∈ S, P.ProfileIntegrableOf p.1 p.2.1 p.2.2 σ γ (α p.1 p.2.1 p.2.2))
    (hnegψ : ∀ p ∉ S, Tendsto (fun t ↦ t ^ lam₀ * P.termKernel ψ σ γ p t) atTop (𝓝 0))
    (hnegχ : ∀ p ∉ S, Tendsto (fun t ↦ t ^ lam₀ * P.termKernel χ σ γ p t) atTop (𝓝 0))
    (hpos : (∑ p ∈ S, P.termConst' χ σ γ α p) ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal)
      atTop (𝓝 ((∑ p ∈ S, P.termConst' ψ σ γ α p) / ∑ p ∈ S, P.termConst' χ σ γ α p)) := by
  have hterm : ∀ (φ : (Fin (m + 1) → ℝ) → ℝ), Continuous φ → (∀ z, 0 ≤ φ z) → ∀ Mφ : ℝ,
      (∀ z, φ z ≤ Mφ) → (∀ z, φ z ≠ 0 → z ∈ L') → ∀ p ∈ S,
      Tendsto (fun t ↦ t ^ lam₀ / log t ^ 0 * P.termKernel φ σ γ p t) atTop
        (𝓝 (P.termConst' φ σ γ α p)) := by
    intro φ hφc hφ Mφ hMφ hφL p hp
    have h := P.tendsto_term (hS p.1) hσ (hadm p hp) (htruth p.1) hφc hφ hMφ hφL (hfeas p hp)
      (hprof p hp)
    rw [← hlam p hp]
    unfold termKernel termConst'
    simp only [if_pos (hadm p hp), pow_zero, div_one]
    exact h
  have hneg : ∀ (φ : (Fin (m + 1) → ℝ) → ℝ),
      (∀ p ∉ S, Tendsto (fun t ↦ t ^ lam₀ * P.termKernel φ σ γ p t) atTop (𝓝 0)) → ∀ p ∉ S,
      Tendsto (fun t ↦ t ^ lam₀ / log t ^ 0 * P.termKernel φ σ γ p t) atTop (𝓝 0) := by
    intro φ hφ p hp
    simpa only [pow_zero, div_one] using hφ p hp
  have hmain := tendsto_sum_ratio_powLog (lam₀ := lam₀) (k₀ := 0) S
    (hterm χ hχc hχ Mχ hMχ hχL) (hterm ψ hψc hψ Mψ hMψ hψL) (hneg χ hnegχ) (hneg ψ hnegψ) hpos
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [P.totalKernel_toReal_eq_sum_terms hS hF hFm hψc.measurable hψ hMψ ht hσ,
    P.totalKernel_toReal_eq_sum_terms hS hF hFm hχc.measurable hχ hMχ ht hσ]

end WallChartsData.Phase

end Laplace.Multi
