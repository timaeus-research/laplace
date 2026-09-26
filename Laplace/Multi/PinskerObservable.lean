/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DataFisherBudget

/-!
# Pinsker for bounded observables: uniform convergence of posterior expectations

The event form of Pinsker's inequality extends verbatim to bounded observables through the
Donsker–Varadhan inequality and Hoeffding's lemma: for `|F − c| ≤ L`,

  `(E_μ F − E_η F)² ≤ 2 L² KL(μ ‖ η)`   (`pinsker_observable`).

Along the straight bridge to a response of finite rate, the expectation of every bounded observable
under the canonical representative therefore converges at the endpoint, with the information gap as
a uniform modulus (`sq_integral_responseProjection_segment_le`,
`tendsto_integral_responseProjection_segment`): the visible journey ends continuously for the whole
class of posterior expectation values.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Pinsker

variable {X : Type*} [MeasurableSpace X] [Nonempty X]

/-- **Pinsker's inequality for bounded observables**: `(E_μ F − E_η F)² ≤ 2 L² KL(μ ‖ η)` when
`|F − c| ≤ L`. -/
theorem pinsker_observable (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    {F : X → ℝ} (hF : Bdd F) {c L : ℝ} (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    ENNReal.ofReal (((∫ x, F x ∂μ) - ∫ x, F x ∂η) ^ 2 / (2 * L ^ 2)) ≤ klDiv μ η := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (∫ x, F x ∂μ) - ∫ x, F x ∂η := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = d / L ^ 2 := ⟨_, rfl⟩
  have hg : Bdd fun x ↦ t * F x := Bdd.const_mul t hF
  have hDV := ofReal_integral_sub_log_le_klDiv η μ hg
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hDV
  have hμ : ∫ x, t * F x ∂μ = t * ∫ x, F x ∂μ := integral_const_mul _ _
  have hη : ∫ x, t * F x ∂η = t * ∫ x, F x ∂η := integral_const_mul _ _
  have hlog : Real.log (∫ x, Real.exp (t * F x) ∂η) ≤ (∫ x, t * F x ∂η) + (|t| * L) ^ 2 / 2 := by
    refine log_integral_exp_le_of_ae_abs_sub_le η hg (c := t * c) (Eventually.of_forall fun x ↦ ?_)
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hFc x) (abs_nonneg t)
  rw [mul_pow, sq_abs] at hlog
  rw [hμ, ← hd]
  have hL2 : 0 < L ^ 2 := by positivity
  have hkey : t * (∫ x, F x ∂η) + t * d - Real.log (∫ x, Real.exp (t * F x) ∂η) ≥
      t * d - t ^ 2 * L ^ 2 / 2 := by linarith
  have e1 : t * (∫ x, F x ∂η) + t * d = t * ((∫ x, F x ∂η) + d) := by ring
  have e2 : t * d - t ^ 2 * L ^ 2 / 2 = d ^ 2 / (2 * L ^ 2) := by
    rw [ht]
    field_simp
    ring
  rw [e1] at hkey
  have e3 : (∫ x, F x ∂η) + d = ∫ x, F x ∂μ := by rw [hd]; ring
  rw [e3, e2] at hkey
  linarith

end Pinsker

section Bridge

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- **Every bounded posterior expectation of the representatives is controlled by the information
gap**: `(E_{Π(M)} F − E_{Π(M_s)} F)² ≤ 2 L² (𝓘(M) − 𝓘(M_s))` for `0 < s < 1` and `|F − c| ≤ L`. -/
theorem sq_integral_responseProjection_segment_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {F : X → ℝ} (hF : Bdd F) {c L : ℝ} (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    ((∫ x, F x ∂responseProjection hS ν M) -
        ∫ x, F x ∂responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) ^ 2 /
        (2 * L ^ 2) ≤
      (genRate ν S M - genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)).toReal := by
  have hP := (responseProjection_spec hS ν hfin).1
  have hfinS : genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M) ≠ ⊤ := by
    intro h
    have := genRate_segment_le hS ν hs0.le hs1.le (M := M)
    rw [h, top_le_iff, ENNReal.mul_eq_top] at this
    rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hfin h2
    · exact ENNReal.ofReal_ne_top h1
  have hPs := (responseProjection_spec hS ν hfinS).1
  have h := (pinsker_observable (responseProjection hS ν M)
    (responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) hF hL hFc).trans
    (klDiv_responseProjection_segment_le hS ν hfin hs0 hs1)
  exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.sub_ne_top hfin)).1 h

/-- **Uniform convergence of bounded posterior expectations at the endpoint of the bridge.** -/
theorem tendsto_integral_responseProjection_segment {F : X → ℝ} (hF : Bdd F) {c L : ℝ}
    (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    Tendsto (fun s : ℝ ↦
        ∫ x, F x ∂responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M))
      (𝓝[<] 1) (𝓝 (∫ x, F x ∂responseProjection hS ν M)) := by
  have hsub : Tendsto (fun s : ℝ ↦ genRate ν S M -
      genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) (𝓝[<] 1) (𝓝 0) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds (tendsto_genRate_segment hS ν hfin)
      (Or.inl hfin)
    rwa [tsub_self] at this
  have hup : Tendsto (fun s : ℝ ↦ (genRate ν S M -
      genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)).toReal * (2 * L ^ 2))
      (𝓝[<] 1) (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsub).mul_const (2 * L ^ 2)
    simpa using this
  have hL2 : 0 < 2 * L ^ 2 := by positivity
  have hsq : Tendsto (fun s : ℝ ↦ ((∫ x, F x ∂responseProjection hS ν M) -
      ∫ x, F x ∂responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) ^ 2)
      (𝓝[<] 1) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ ↦ sq_nonneg _) ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
    have := sq_integral_responseProjection_segment_le hS ν hfin hs.1 hs.2 hF hL hFc
    rwa [div_le_iff₀ hL2] at this
  have habs : Tendsto (fun s : ℝ ↦ |(∫ x, F x ∂responseProjection hS ν M) -
      ∫ x, F x ∂responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)|)
      (𝓝[<] 1) (𝓝 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs] using this
  have hd := (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have := (tendsto_const_nhds (x := ∫ x, F x ∂responseProjection hS ν M)).sub hd
  simpa using this

end Bridge

end Laplace.Multi
