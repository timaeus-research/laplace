/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.InformationAlongAtlas

/-!
# The second-order Peano expansion of the natural coordinate

A vector-valued version of the generic Peano lemma (`isLittleO_peano_of_hasFDerivAt'`) and its
application to the natural coordinate in response coordinates:

`θ(M+z) = θ(M) + R z − ½ R T_{θ(M)}(Rz)(Rz) + o(‖z‖²)` (`isLittleO_responseTheta_peano`),

with `R = (Dm(θ)|_𝕍)⁻¹` and `T` the third-cumulant operator. The quadratic term is
`−½ R Cov_Q(S, ℓ_{M,z}²)`, minus half the bending direction of the atlas
(`responseTheta_peano_quadratic`).
-/

open MeasureTheory Filter Topology Set Asymptotics

namespace Laplace.Multi

section PeanoVector

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- **Second-order Peano expansion from a differentiable derivative field**, vector-valued. -/
theorem isLittleO_peano_of_hasFDerivAt' {F : E → G} {A : E → (E →L[ℝ] G)}
    {B : E →L[ℝ] (E →L[ℝ] G)} (hF : ∀ᶠ z in 𝓝 (0 : E), HasFDerivAt F (A z) z)
    (hA : HasFDerivAt A B 0) :
    (fun z ↦ F z - F 0 - A 0 z - (1 / 2 : ℝ) • B z z) =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hA'⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hA).def hε)
  obtain ⟨δ₂, hδ₂, hF'⟩ := Metric.eventually_nhds_iff.1 hF
  rw [Metric.eventually_nhds_iff]
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z hz ↦ ?_⟩
  rw [dist_zero_right] at hz
  have hz₁ : ‖z‖ < δ₁ := hz.trans_le (min_le_left _ _)
  have hz₂ : ‖z‖ < δ₂ := hz.trans_le (min_le_right _ _)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → G,
      g = fun t ↦ F (t • z) - t • A 0 z - (t ^ 2 / 2) • B z z := ⟨_, rfl⟩
  have hgd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (A (t • z) z - A 0 z - t • B z z) t := by
    intro t ht
    have htz : ‖t • z‖ < δ₂ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ < δ₂ := by simpa using hz₂
    have h1 : HasDerivAt (fun t : ℝ ↦ F (t • z)) (A (t • z) z) t := by
      have hl : HasDerivAt (fun t : ℝ ↦ t • z) z t := by
        simpa using (hasDerivAt_id t).smul_const z
      have := (hF' (by rwa [dist_zero_right])).comp_hasDerivAt t hl
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun t : ℝ ↦ t • A 0 z) (A 0 z) t := by
      simpa using (hasDerivAt_id t).smul_const (A 0 z)
    have h3 : HasDerivAt (fun t : ℝ ↦ (t ^ 2 / 2) • B z z) (t • B z z) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).smul_const (B z z)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      rw [show (2 : ℝ) * t / 2 = t by ring]
    rw [hg]
    exact (h1.sub h2).sub h3
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖A (t • z) z - A 0 z - t • B z z‖ ≤ ε * ‖z‖ ^ 2 := by
    intro t ht
    have htz : ‖t • z‖ < δ₁ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
        _ < δ₁ := by simpa using hz₁
    have hAt := hA' (by rwa [dist_zero_right])
    rw [zero_add] at hAt
    have e : A (t • z) z - A 0 z - t • B z z = (A (t • z) - A 0 - B (t • z)) z := by
      simp only [sub_apply, map_smul, smul_apply]
    rw [e]
    calc ‖(A (t • z) - A 0 - B (t • z)) z‖
        ≤ ‖A (t • z) - A 0 - B (t • z)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖t • z‖ * ‖z‖ := mul_le_mul_of_nonneg_right hAt (norm_nonneg _)
      _ ≤ ε * ‖z‖ * ‖z‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          have : t * ‖z‖ ≤ ‖z‖ := by
            calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
              _ = ‖z‖ := one_mul _
          gcongr
      _ = ε * ‖z‖ ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (f' := fun t ↦ A (t • z) z - A 0 z - t • B z z) (a := 0) (b := 1)
    (fun t ht ↦ (hgd t ht).hasDerivWithinAt) hbound 1 (right_mem_Icc.mpr zero_le_one)
  rw [hg] at hmv
  simp only [one_smul, one_pow, zero_smul, sub_zero, mul_one] at hmv
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z‖)]
  calc ‖F z - F 0 - A 0 z - (1 / 2 : ℝ) • B z z‖
      = ‖F z - A 0 z - (1 / 2 : ℝ) • B z z - F 0‖ := by
        congr 1
        abel
    _ ≤ ε * ‖z‖ ^ 2 := by simpa using hmv

end PeanoVector

section ThetaPeano

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

include hS

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The natural coordinate has a second-order Peano expansion in response coordinates**:
`θ(M+z) = θ(M) + R z − ½ R T_{θ(M)}(Rz)(Rz) + o(‖z‖²)`. -/
theorem isLittleO_responseTheta_peano :
    (fun z : 𝕍 ↦ θr (M + z) - θr M - ContinuousLinearEquiv.symm (CDE (θr M)) z -
      (1 / 2 : ℝ) • (-(ContinuousLinearEquiv.symm (CDE (θr M))
        (thirdOp hS ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) z)
          (ContinuousLinearEquiv.symm (CDE (θr M)) z)))))
      =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
  have hF : ∀ᶠ z : 𝕍 in 𝓝 0, HasFDerivAt (fun z : 𝕍 ↦ θr (M + z))
      (ContinuousLinearEquiv.symm (CDE (θr (M + z))) : 𝕍 →L[ℝ] 𝕍) z := by
    filter_upwards [eventually_add_mem_intrinsicInterior hS ν hrel] with z hz
    exact hasFDerivAt_responseTheta_add_at hS ν hz
  have h := isLittleO_peano_of_hasFDerivAt' hF (hasFDerivAt_inverse_response hS ν hrel)
  refine h.congr_left fun z ↦ ?_
  have h0 : M + ((0 : 𝕍) : J → ℝ) = M := by simp
  simp only [h0]
  rfl

/-- The quadratic term of the natural coordinate is minus half the response score direction of
the squared score: `−½ R T(Rz)(Rz) = −½ R Cov_Q(S, ℓ_{M,z}²)`. -/
theorem responseTheta_peano_quadratic (z : 𝕍) :
    thirdOp hS ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) z)
        (ContinuousLinearEquiv.symm (CDE (θr M)) z) =
      ⟨respCov hS ν M (fun x ↦ responseScore hS ν M z x * responseScore hS ν M z x),
        respCov_mem_dirSpan hS ν ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z))⟩ :=
  Subtype.ext (by rw [thirdOp_coe_apply, thirdVec_eq_respCov hS ν hrel])

end ThetaPeano

end Laplace.Multi
