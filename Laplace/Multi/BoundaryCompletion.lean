/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BoundaryTaylor
import Laplace.Multi.PinskerObservable
import Laplace.Multi.EndpointTail

/-!
# The atlas is completed at every finite-rate response

For a response `M` of finite rate, on the relative boundary of the moment body or not, the straight
atlas `M_s = m₀ + s(M − m₀)` stays interior for `s < 1` and its laws `Q_s = Π(M_s)` complete at
`s = 1` to the information projection `Q_* = Π(M)` (the entropy minimiser with response `M`):

* `KL(Q_* ‖ Q_s) = ∫_s^1 (1 − u) κ_u du` (`toReal_klDiv_responseProjection_atlas_eq_integral`,
  recalled), and `KL(Q_* ‖ Q_s) → 0` as `s ↑ 1` (`tendsto_klDiv_responseProjection_atlas`);
* every bounded observable's endpoint defect is controlled by the tail of the weighted Fisher energy
  (`sq_integral_sub_responseProjection_atlas_le`:
  `(E_{Q_*}F − E_{Q_s}F)² ≤ 2L² ∫_s^1 (1 − u) κ_u du`), so the atlas responses converge to the
  endpoint responses (`tendsto_integral_atlas_endpoint`);
* the triangular accounting expression converges to the endpoint response
  (`tendsto_atlas_taylor_responseProjection`).

`boundary_completion` packages these with the defining properties of the information projection. The
natural coordinates `θ(M_s)` escape to infinity at boundary responses (`BoundaryEscape`); the laws
nevertheless converge, and the accounting of observables and of information extends to the endpoint.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The reconstruction at the atlas point `s`. -/
local notation "Qat" s => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
  (atlasTheta hS ν M s)

/-- The atlas law is the reconstruction of the atlas point. -/
theorem atlas_eq_responseProjection {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (Qat s) = responseProjection hS ν (atlasPath S ν M s) := by
  unfold atlasTheta
  exact (responseProjection_eq_familyMeasure_responseTheta hS ν
    (atlas_mem_intrinsicInterior hS ν hfin hs0 hs1)).symm

/-- **Endpoint convergence of the atlas responses**: for every bounded observable and every
finite-rate response, `E_{Q_t}φ → E_{Q_*}φ` as `t ↑ 1`. -/
theorem tendsto_integral_atlas_endpoint {φ : X → ℝ} (hφ : Bdd φ) :
    Tendsto (fun t ↦ ∫ x, φ x ∂(Qat t)) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ x, φ x ∂responseProjection hS ν M)) := by
  obtain ⟨hφm, L, hL⟩ := hφ
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL (Classical.arbitrary X))
  have h := tendsto_integral_responseProjection_segment hS ν hfin ⟨hφm, L, hL⟩ (c := 0)
    (L := L + 1) (by linarith) fun x ↦ by
      rw [sub_zero]
      linarith [hL x]
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
  rw [atlas_eq_responseProjection hS ν hfin ht.1.le ht.2, atlasPath_eq]

/-- **The triangular accounting identity at the endpoint**, with the endpoint law identified as the
information projection `Q_* = Π(M)`:
`E_{Q_*}φ − E_νφ = lim_{t↑1} [t E_ν[φℓ_0] + ∫₀ᵗ (t − u) E_{Q_u}[φ N(ℓ_u²)] du]`. -/
theorem tendsto_atlas_taylor_responseProjection {φ : X → ℝ} (hφ : Bdd φ) :
    Tendsto (fun t ↦ t * (∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν) +
        ∫ u in (0 : ℝ)..t, (t - u) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M u)
          (bdd_atlasScore_sq hS ν hfin (s := u)) x ∂(Qat u))
      (𝓝[<] (1 : ℝ)) (𝓝 ((∫ x, φ x ∂responseProjection hS ν M) - ∫ x, φ x ∂ν)) :=
  tendsto_atlas_taylor_endpoint hS ν hfin hφ (tendsto_integral_atlas_endpoint hS ν hfin hφ)

/-- **Information convergence at the endpoint**: `KL(Q_* ‖ Q_s) → 0` as `s ↑ 1`. -/
theorem tendsto_klDiv_responseProjection_atlas :
    Tendsto (fun s ↦ klDiv (responseProjection hS ν M) (Qat s)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hsub : Tendsto (fun s : ℝ ↦ genRate ν S M -
      genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) (𝓝[<] 1) (𝓝 0) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds (tendsto_genRate_segment hS ν hfin)
      (Or.inl hfin)
    rwa [tsub_self] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsub
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with s hs
  rw [atlas_eq_responseProjection hS ν hfin hs.1.le hs.2, atlasPath_eq]
  exact klDiv_responseProjection_segment_le hS ν hfin hs.1 hs.2

/-- **Pinsker at the endpoint**: the endpoint defect of every bounded observable is controlled by
the tail of the weighted Fisher energy, `(E_{Q_*}F − E_{Q_s}F)² ≤ 2 L² ∫_s^1 (1 − u) κ_u du` for
`|F − c| ≤ L`. -/
theorem sq_integral_sub_responseProjection_atlas_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {F : X → ℝ} (hF : Bdd F) {c L : ℝ} (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    ((∫ x, F x ∂responseProjection hS ν M) - ∫ x, F x ∂(Qat s)) ^ 2 ≤
      2 * L ^ 2 * ∫ u in s..1, (1 - u) * atlasCurv hS ν hfin u := by
  have hP := (responseProjection_spec hS ν hfin).1
  have hPs := isProbabilityMeasure_family hS ν (atlasTheta hS ν M s : J → ℝ)
  have h := pinsker_observable (responseProjection hS ν M) (Qat s) hF hL hFc
  rw [atlas_eq_responseProjection hS ν hfin hs0 hs1] at h ⊢
  have hne := klDiv_responseProjection_interior_ne_top hS ν hfin
    (atlas_mem_intrinsicInterior hS ν hfin hs0 hs1)
  have h' := (ENNReal.ofReal_le_iff_le_toReal hne).1 h
  rw [toReal_klDiv_responseProjection_atlas_eq_integral hS ν hfin hs0 hs1,
    div_le_iff₀ (by positivity)] at h'
  linarith

/-- **The boundary completion theorem.** For every finite-rate response `M` (boundary or interior):
the information projection `Q_* = Π(M)` is a probability law with response `M` and
`KL(Q_* ‖ ν) = 𝓘(M)`, Pythagoras `KL(ρ ‖ ν) = KL(ρ ‖ Q_*) + 𝓘(M)` holds for every law `ρ` with
response `M`; along the atlas `KL(Q_* ‖ Q_s) = ∫_s^1 (1 − u) κ_u du → 0`; every bounded observable's
atlas response converges to its `Q_*`-response, and the triangular accounting identity holds in the
limit. -/
theorem boundary_completion :
    IsProbabilityMeasure (responseProjection hS ν M) ∧
      (fun i ↦ ∫ x, S i x ∂responseProjection hS ν M) = M ∧
      klDiv (responseProjection hS ν M) ν = genRate ν S M ∧
      (∀ ρ : Measure X, IsProbabilityMeasure ρ → (fun i ↦ ∫ x, S i x ∂ρ) = M →
        klDiv ρ ν = klDiv ρ (responseProjection hS ν M) + genRate ν S M) ∧
      (∀ s : ℝ, 0 ≤ s → s < 1 →
        (klDiv (responseProjection hS ν M) (Qat s)).toReal =
          ∫ u in s..1, (1 - u) * atlasCurv hS ν hfin u) ∧
      Tendsto (fun s ↦ klDiv (responseProjection hS ν M) (Qat s)) (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
      (∀ φ : X → ℝ, Bdd φ → Tendsto (fun t ↦ ∫ x, φ x ∂(Qat t)) (𝓝[<] (1 : ℝ))
        (𝓝 (∫ x, φ x ∂responseProjection hS ν M))) ∧
      (∀ φ : X → ℝ, Bdd φ →
        Tendsto (fun t ↦ t * (∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν) +
          ∫ u in (0 : ℝ)..t, (t - u) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M u)
            (bdd_atlasScore_sq hS ν hfin (s := u)) x ∂(Qat u))
          (𝓝[<] (1 : ℝ)) (𝓝 ((∫ x, φ x ∂responseProjection hS ν M) - ∫ x, φ x ∂ν))) := by
  obtain ⟨hP, hM, hkl, hpyth⟩ := responseProjection_spec hS ν hfin
  refine ⟨hP, hM, hkl, hpyth, fun s hs0 hs1 ↦ ?_, tendsto_klDiv_responseProjection_atlas hS ν hfin,
    fun φ hφ ↦ tendsto_integral_atlas_endpoint hS ν hfin hφ,
    fun φ hφ ↦ tendsto_atlas_taylor_responseProjection hS ν hfin hφ⟩
  rw [atlas_eq_responseProjection hS ν hfin hs0 hs1]
  exact toReal_klDiv_responseProjection_atlas_eq_integral hS ν hfin hs0 hs1

end Laplace.Multi
