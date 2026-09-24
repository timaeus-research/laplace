/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MixedTruthRecord

/-!
# Atlas independence of the fibre kernel

Two chart systems over the same region and truth define the same total fibre kernel almost
everywhere: both kernels are densities of the same push-forward measure `(θ dz)|_{L'} ∘ T⁻¹`
(`TruthChartsData.totalKernel_ae_eq`, `WallChartsData.totalKernel_ae_eq`, by the push-forward
identity and uniqueness of densities). Pointwise statements along prescribed rays need continuity
of the kernels (`FibreContinuity`) and are not part of this lemma.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ}

/-- **Atlas independence.** Two chart systems for the same truth function over the same region
have almost everywhere equal total fibre kernels. -/
theorem TruthChartsData.totalKernel_ae_eq {T : (Fin (m + 1) → ℝ) → ℝ}
    {L' : Set (Fin (m + 1) → ℝ)} (D₁ D₂ : TruthChartsData m T L') (hT : Measurable T)
    {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθ : Measurable θ) :
    D₁.totalKernel θ =ᵐ[volume] D₂.totalKernel θ := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (D₁.measurable_totalKernel hθ)
    (D₂.measurable_totalKernel hθ) fun E hE _ ↦ ?_
  have key : ∀ D : TruthChartsData m T L', ∫⁻ s in E, D.totalKernel θ s =
      ∫⁻ z in L', θ z * E.indicator (fun _ ↦ 1) (T z) := by
    intro D
    rw [D.lintegral_mul_comp_truth hT hθ (measurable_const.indicator hE), ← lintegral_indicator hE]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ E
    · simp only [indicator_of_mem hs, one_mul]
    · simp only [indicator_of_notMem hs, zero_mul]
  rw [key, key]

/-- Atlas independence for Euclidean wall data (the coordinate truth `z ℓ`). -/
theorem WallChartsData.totalKernel_ae_eq {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}
    (D₁ D₂ : WallChartsData m ℓ L') {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθ : Measurable θ) :
    D₁.totalKernel θ =ᵐ[volume] D₂.totalKernel θ :=
  TruthChartsData.totalKernel_ae_eq D₁.toTruth D₂.toTruth (measurable_pi_apply ℓ) hθ

end Laplace.Multi
