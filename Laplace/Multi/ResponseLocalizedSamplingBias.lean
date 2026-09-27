/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseCertifiedChart

/-!
# The localised sampling bias of the response: curvature as bias

How much of an apparent truth shift is curvature-induced sampling bias? The response of the
empirical mean `θr(m₀ + ξ)` has the cubic expansion

`θr(m₀ + ξ) = θ₀ + A⁻¹ξ − ½ C_{θ₀}(A⁻¹ξ, A⁻¹ξ) + O(‖ξ‖³)`

(`exists_responseTheta_cubic_remainder`): the generic **cubic remainder** of a `C³` map
(`exists_cubic_remainder`, the quadratic remainder of the derivative integrated along the
segment) together with the identification of the **second derivative of the inverse chart as
minus the m-Christoffel symbol** (`fderiv_fderiv_responseTheta_meanAdd_zero`, from the bending
of response lines in `ResponseSamplingGeometry`).

For the **reset-localised estimator** `θ̂_loc = θ₀ + 1_{‖ξ‖ ≤ δ}(θr(m₀ + ξ) − θ₀)` — the
estimator that stays at `θ₀` when the sampling displacement leaves the certified ball — the bias
is computed on the law `μ` of `ξ` (`localizedBias_decomposition`):

`∫_{‖z‖≤δ} (θr(m₀+z) − θ₀) dμ = A⁻¹ ∫_{‖z‖≤δ} z dμ − ½ ∫_{‖z‖≤δ} C(A⁻¹z,A⁻¹z) dμ + R`,
`‖R‖ ≤ K ∫_{‖z‖≤δ} ‖z‖³ dμ`.

The localisation is explicit: the truncated linear term does **not** vanish for a centred law, but
is controlled by the third absolute moment (`norm_setIntegral_id_le_of_centred`:
`‖∫_{‖z‖≤δ} z dμ‖ ≤ M₃/δ²`), and so is the tail of the curvature term. The headline
(`localizedBias_curvature`) is

`‖ E[θ̂_loc − θ₀] + ½ E_μ[C(A⁻¹Z, A⁻¹Z)] ‖ ≤ (‖A⁻¹‖/δ² + K + ½‖A⁻¹‖²‖T‖‖A⁻¹‖/δ) M₃`:

the localised bias is the **curvature term** `−½ E[C(A⁻¹Z, A⁻¹Z)]` up to the third absolute
moment. For the sample mean of `n` i.i.d. observations the curvature term is `O(1/n)` (a bilinear
form of the covariance, cf. `integral_samplingEnergy`) while `M₃ = O(n^{−3/2})`; so the leading
bias of the localised response is exactly the m-connection contracted with the sampling covariance.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The quantitative cubic remainder** of a `C³` map on a ball around `0`. -/
theorem exists_cubic_remainder {F : E → G} {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
    (hF : ContDiffOn ℝ 3 F U) :
    ∃ δ > 0, Metric.closedBall (0 : E) δ ⊆ U ∧ ∃ K, 0 ≤ K ∧ ∀ z : E, ‖z‖ ≤ δ →
      ‖F z - F 0 - fderiv ℝ F 0 z - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 z z‖ ≤ K * ‖z‖ ^ 3 := by
  have hF1 : ContDiffOn ℝ 2 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨δ, hδ, hsub, K, hK, h⟩ := exists_quadratic_remainder_subset hU h0 hF1
  refine ⟨δ, hδ, hsub, K, hK, fun z hz ↦ ?_⟩
  set L := fderiv ℝ F 0 with hL
  set Q := fderiv ℝ (fderiv ℝ F) 0 with hQ
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖t • z‖ ≤ δ := fun t ht ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg z, ht.2]
  have hzU : ∀ t ∈ Icc (0 : ℝ) 1, t • z ∈ U := fun t ht ↦ hsub (by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hnorm t ht)
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ F (t • z)) (fderiv ℝ F (t • z) z) t := by
    intro t ht
    have hd : DifferentiableAt ℝ F (t • z) :=
      (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hzU t ht))
    have := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const z)
    simpa [Function.comp_def] using this
  have hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ F (t • z) - t • L z - (t ^ 2 / 2) • Q z z)
        (fderiv ℝ F (t • z) z - L z - t • Q z z) t := by
    intro t ht
    have h2 : HasDerivAt (fun t : ℝ ↦ t • L z) (L z) t := by
      simpa using (hasDerivAt_id t).smul_const (L z)
    have h3 : HasDerivAt (fun t : ℝ ↦ (t ^ 2 / 2) • Q z z) (t • Q z z) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).smul_const (Q z z)
      refine this.congr_deriv ?_
      have e : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t := by push_cast; ring
      rw [e]
    exact ((hdiff t ht).sub h2).sub h3
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ F (t • z) z - L z - t • Q z z‖ ≤ K * ‖z‖ ^ 3 := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have h1 := h (t • z) (hnorm t ht')
    have hts : ‖t • z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [norm_nonneg z, ht.2.le]
    have e : fderiv ℝ F (t • z) z - L z - t • Q z z = (fderiv ℝ F (t • z) - L - Q (t • z)) z := by
      simp only [sub_apply, map_smul, smul_apply]
    rw [e]
    calc ‖(fderiv ℝ F (t • z) - L - Q (t • z)) z‖
        ≤ ‖fderiv ℝ F (t • z) - L - Q (t • z)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖t • z‖ ^ 2 * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ K * ‖z‖ ^ 2 * ‖z‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hts 2) hK) (norm_nonneg _)
      _ = K * ‖z‖ ^ 3 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ ↦ F (t • z) - t • L z - (t ^ 2 / 2) • Q z z) (a := 0) (b := 1)
    (C := K * ‖z‖ ^ 3) (fun t ht ↦ (hg t ht).hasDerivWithinAt) hbound 1
    (right_mem_Icc.mpr zero_le_one)
  simp only [one_smul, zero_smul, one_pow, sub_zero, mul_one] at hmv
  norm_num at hmv
  have e : F z - F 0 - L z - (1 / 2 : ℝ) • Q z z = F z - L z - (1 / 2 : ℝ) • Q z z - F 0 := by abel
  rw [e]
  exact hmv

end Generic

section Response

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The m-Christoffel symbol. -/
local notation "C" => mChristoffel hS ν

/-- The inverse chart at `θ₀` in a mean displacement. -/
local notation "Finv" θ₀ => fun z : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ))

/-- The response line is the inverse chart along the ray `t • e`. -/
theorem responseLine_eq_meanAdd (θ₀ e : 𝕍) :
    responseLine hS ν θ₀ e = fun t ↦ (Finv θ₀) (t • e) := by
  funext t
  simp only [responseLine, Submodule.coe_smul]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The ray `t • e` is in the ball domain iff `t` is in the line domain. -/
theorem smul_mem_responseBallDomain_iff (θ₀ e : 𝕍) (t : ℝ) :
    t • e ∈ responseBallDomain S ν θ₀ ↔ t ∈ responseLineDomain S ν θ₀ e := Iff.rfl

/-- **The second derivative of the inverse chart is minus the m-Christoffel symbol**:
`D²(m⁻¹)(m(θ₀))[e, e] = −C_{θ₀}(A⁻¹e, A⁻¹e)`. -/
theorem fderiv_fderiv_responseTheta_meanAdd_zero (θ₀ e : 𝕍) :
    fderiv ℝ (fderiv ℝ (Finv θ₀)) 0 e e =
      -C θ₀ ((CDE θ₀).symm e) ((CDE θ₀).symm e) := by
  have hU := isOpen_responseBallDomain hS ν θ₀
  have hF1 : ContDiffOn ℝ 2 (fderiv ℝ (Finv θ₀)) (responseBallDomain S ν θ₀) :=
    ((contDiffOn_responseTheta_meanAdd hS ν θ₀).of_le (by exact_mod_cast natCast_le_infty 3))
      |>.fderiv_of_isOpen hU (by norm_num)
  -- first derivative along the line is the line velocity
  have h1 : ∀ t ∈ responseLineDomain S ν θ₀ e,
      HasDerivAt (fun t : ℝ ↦ (Finv θ₀) (t • e)) (fderiv ℝ (Finv θ₀) (t • e) e) t := by
    intro t ht
    have hd : DifferentiableAt ℝ (Finv θ₀) (t • e) :=
      ((contDiffOn_responseTheta_meanAdd hS ν θ₀).differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds ((smul_mem_responseBallDomain_iff ν θ₀ e t).2 ht))
    have := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const e)
    simpa [Function.comp_def] using this
  have hvel : ∀ t ∈ responseLineDomain S ν θ₀ e,
      fderiv ℝ (Finv θ₀) (t • e) e = responseLineVel hS ν θ₀ e t := fun t ht ↦ by
    have h := hasDerivAt_responseLine hS ν θ₀ e ht
    rw [responseLine_eq_meanAdd hS ν] at h
    exact (h1 t ht).unique h
  -- second derivative along the line
  have h2 : HasDerivAt (fun t : ℝ ↦ fderiv ℝ (Finv θ₀) (t • e) e)
      (fderiv ℝ (fderiv ℝ (Finv θ₀)) 0 e e) 0 := by
    have hd : DifferentiableAt ℝ (fderiv ℝ (Finv θ₀)) ((0 : ℝ) • e) := by
      rw [zero_smul]
      exact (hF1.differentiableOn (by norm_num)).differentiableAt
        (hU.mem_nhds (zero_mem_responseBallDomain hS ν θ₀))
    have h := (hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const e))
    have h' := h.clm_apply (hasDerivAt_const (0 : ℝ) e)
    simp only [Function.comp_def, id_eq, one_smul, zero_smul, map_zero, add_zero] at h'
    exact h'
  have h3 : HasDerivAt (fun t : ℝ ↦ fderiv ℝ (Finv θ₀) (t • e) e)
      (-C (responseLine hS ν θ₀ e 0) (responseLineVel hS ν θ₀ e 0) (responseLineVel hS ν θ₀ e 0))
      0 := by
    refine (hasDerivAt_responseLineVel hS ν θ₀ e (zero_mem_responseLineDomain hS ν θ₀ e))
      |>.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_responseLineDomain hS ν θ₀ e).mem_nhds
      (zero_mem_responseLineDomain hS ν θ₀ e)] with t ht
    exact hvel t ht
  have h0 : responseLine hS ν θ₀ e 0 = θ₀ := by
    simp only [responseLine, zero_smul, add_zero, responseTheta_meanMap hS ν]
  have hV : responseLineVel hS ν θ₀ e 0 = (CDE θ₀).symm e := by
    simp only [responseLineVel, h0]
  rw [h2.unique h3, h0, hV]

/-- **The cubic expansion of the response in a mean displacement, quantitatively on a ball**:
`‖θr(m₀ + z) − θ₀ − A⁻¹z + ½ C(A⁻¹z, A⁻¹z)‖ ≤ K ‖z‖³` for `‖z‖ ≤ δ`, the ball being inside the
chart domain. -/
theorem exists_responseTheta_cubic_remainder (θ₀ : 𝕍) :
    ∃ δ > 0, (∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω) ∧
      ∃ K, 0 ≤ K ∧ ∀ z : 𝕍, ‖z‖ ≤ δ →
        ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z +
          (1 / 2 : ℝ) • C θ₀ ((CDE θ₀).symm z) ((CDE θ₀).symm z)‖ ≤ K * ‖z‖ ^ 3 := by
  obtain ⟨δ, hδ, hsub, K, hK, h⟩ := exists_cubic_remainder (isOpen_responseBallDomain hS ν θ₀)
    (zero_mem_responseBallDomain hS ν θ₀)
    ((contDiffOn_responseTheta_meanAdd hS ν θ₀).of_le (by exact_mod_cast natCast_le_infty 3))
  refine ⟨δ, hδ, fun z hz ↦ ?_, K, hK, fun z hz ↦ ?_⟩
  · have hz' : z ∈ Metric.closedBall (0 : 𝕍) δ := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz
    exact hsub hz'
  · have := h z hz
    rw [fderiv_responseTheta_meanAdd_zero hS ν,
      fderiv_fderiv_responseTheta_meanAdd_zero hS ν] at this
    simp only [Submodule.coe_zero, add_zero, responseTheta_meanMap hS ν, smul_neg] at this
    rw [sub_neg_eq_add] at this
    exact this

end Response

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The m-Christoffel symbol. -/
local notation "C" => mChristoffel hS ν

variable {δ : ℝ}

/-- The certified ball `{‖z‖ ≤ δ}`. -/
local notation "cball" => Metric.closedBall (0 : 𝕍) δ

/-- The curvature quadratic form `z ↦ C_{θ₀}(A⁻¹z, A⁻¹z)`. -/
noncomputable def curvatureForm (θ₀ : 𝕍) (z : 𝕍) : 𝕍 := C θ₀ ((CDE θ₀).symm z) ((CDE θ₀).symm z)

theorem continuous_curvatureForm (θ₀ : 𝕍) : Continuous (curvatureForm hS ν θ₀) := by
  unfold curvatureForm mChristoffel
  exact (CDE θ₀).symm.continuous.comp
    (Continuous.clm_apply ((thirdOp hS ν θ₀).continuous.comp (CDE θ₀).symm.continuous)
      (CDE θ₀).symm.continuous)

/-- The curvature form is bounded by `‖A⁻¹‖ ‖T‖ ‖A⁻¹‖² ‖z‖²`. -/
theorem norm_curvatureForm_le (θ₀ : 𝕍) (z : 𝕍) :
    ‖curvatureForm hS ν θ₀ z‖ ≤
      ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * ‖thirdOp hS ν θ₀‖ * ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ ^ 2 *
        ‖z‖ ^ 2 := by
  set B : 𝕍 →L[ℝ] 𝕍 := ((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) with hB
  have hBz : ‖B z‖ ≤ ‖B‖ * ‖z‖ := B.le_opNorm z
  have hT : ‖thirdOp hS ν θ₀ (B z) (B z)‖ ≤ ‖thirdOp hS ν θ₀‖ * ‖B z‖ * ‖B z‖ := by
    calc ‖thirdOp hS ν θ₀ (B z) (B z)‖ ≤ ‖thirdOp hS ν θ₀ (B z)‖ * ‖B z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖thirdOp hS ν θ₀‖ * ‖B z‖ * ‖B z‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
  have hBz2 : ‖B z‖ * ‖B z‖ ≤ (‖B‖ * ‖z‖) * (‖B‖ * ‖z‖) :=
    mul_le_mul hBz hBz (norm_nonneg _) (by positivity)
  calc ‖curvatureForm hS ν θ₀ z‖ = ‖B (thirdOp hS ν θ₀ (B z) (B z))‖ := rfl
    _ ≤ ‖B‖ * ‖thirdOp hS ν θ₀ (B z) (B z)‖ := B.le_opNorm _
    _ ≤ ‖B‖ * (‖thirdOp hS ν θ₀‖ * ‖B z‖ * ‖B z‖) := mul_le_mul_of_nonneg_left hT (norm_nonneg _)
    _ ≤ ‖B‖ * (‖thirdOp hS ν θ₀‖ * ((‖B‖ * ‖z‖) * (‖B‖ * ‖z‖))) := by
        rw [mul_assoc ‖thirdOp hS ν θ₀‖]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBz2 (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖B‖ * ‖thirdOp hS ν θ₀‖ * ‖B‖ ^ 2 * ‖z‖ ^ 2 := by ring

/-- **The localised bias decomposition** on the law `μ` of the sampling displacement:
`∫_{‖z‖≤δ} (θr(m₀+z) − θ₀) dμ = A⁻¹ ∫_{‖z‖≤δ} z dμ − ½ ∫_{‖z‖≤δ} C(A⁻¹z,A⁻¹z) dμ + R`,
`‖R‖ ≤ K ∫_{‖z‖≤δ} ‖z‖³ dμ`. -/
theorem localizedBias_decomposition (μ : Measure 𝕍) [IsFiniteMeasure μ] (θ₀ : 𝕍) {K : ℝ}
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z +
        (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z‖ ≤ K * ‖z‖ ^ 3) :
    ‖(∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀) ∂μ) -
        (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) (∫ z in cball, z ∂μ) -
          (1 / 2 : ℝ) • ∫ z in cball, curvatureForm hS ν θ₀ z ∂μ)‖ ≤
      K * ∫ z in cball, ‖z‖ ^ 3 ∂μ := by
  set B : 𝕍 →L[ℝ] 𝕍 := ((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) with hB
  have hs : MeasurableSet (cball) := Metric.isClosed_closedBall.measurableSet
  have hcpt : IsCompact (cball) := isCompact_closedBall (0 : 𝕍) δ
  have hballdom : cball ⊆ responseBallDomain S ν θ₀ := fun z hz ↦ by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hdom z hz
  -- the inverse chart is continuous on the ball
  have hcont : ContinuousOn (fun z : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ))) (cball) :=
    (contDiffOn_responseTheta_meanAdd hS ν θ₀).continuousOn.mono hballdom
  -- integrability on the ball
  have hI1 : IntegrableOn (fun z : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀) (cball) μ :=
    (hcont.sub continuousOn_const).integrableOn_compact hcpt
  have hI2 : IntegrableOn (fun z : 𝕍 ↦ z) (cball) μ :=
    continuous_id.continuousOn.integrableOn_compact hcpt
  have hI3 : IntegrableOn (curvatureForm hS ν θ₀) (cball) μ :=
    (continuous_curvatureForm hS ν θ₀).continuousOn.integrableOn_compact hcpt
  have hI4 : IntegrableOn (fun z : 𝕍 ↦ ‖z‖ ^ 3) (cball) μ :=
    (continuous_norm.pow 3).continuousOn.integrableOn_compact hcpt
  -- the remainder
  set R : 𝕍 → 𝕍 := fun z ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - B z +
    (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z with hR
  have hI3' : IntegrableOn (fun z : 𝕍 ↦ (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z) cball μ :=
    hI3.smul (1 / 2 : ℝ)
  have hIB : IntegrableOn (fun z : 𝕍 ↦ B z) cball μ :=
    B.continuous.continuousOn.integrableOn_compact hcpt
  have hIR : IntegrableOn R cball μ := (hI1.sub hIB).add hI3'
  have hsplit : ∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀) ∂μ =
      B (∫ z in cball, z ∂μ) - (1 / 2 : ℝ) • (∫ z in cball, curvatureForm hS ν θ₀ z ∂μ) +
        ∫ z in cball, R z ∂μ := by
    have e : ∀ z ∈ cball, θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ =
        (B z - (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z) + R z := fun z _ ↦ by
      simp only [hR]; abel
    rw [setIntegral_congr_fun hs e]
    have hIBC : IntegrableOn (fun z : 𝕍 ↦ B z - (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z) cball μ :=
      hIB.sub hI3'
    rw [integral_add hIBC hIR, integral_sub hIB hI3', integral_smul, B.integral_comp_comm hI2]
  rw [hsplit]
  have e2 : B (∫ z in cball, z ∂μ) - (1 / 2 : ℝ) • (∫ z in cball, curvatureForm hS ν θ₀ z ∂μ) +
      (∫ z in cball, R z ∂μ) -
      (B (∫ z in cball, z ∂μ) - (1 / 2 : ℝ) • ∫ z in cball, curvatureForm hS ν θ₀ z ∂μ) =
      ∫ z in cball, R z ∂μ := by abel
  rw [e2]
  have hbound : ∀ᵐ z ∂μ.restrict (cball), ‖R z‖ ≤ K * ‖z‖ ^ 3 := by
    rw [ae_restrict_iff' hs]
    refine ae_of_all _ fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hrem z hz
  calc ‖∫ z in cball, R z ∂μ‖ ≤ ∫ z in cball, K * ‖z‖ ^ 3 ∂μ :=
        norm_integral_le_of_norm_le (hI4.const_mul K) hbound
    _ = K * ∫ z in cball, ‖z‖ ^ 3 ∂μ := integral_const_mul _ _

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **The truncated linear term of a centred law is controlled by the third moment**:
`‖∫_{‖z‖≤δ} z dμ‖ ≤ M₃/δ²`. -/
theorem norm_setIntegral_id_le_of_centred (μ : Measure 𝕍) [IsFiniteMeasure μ] (hδ : 0 < δ)
    (hcent : ∫ z, z ∂μ = 0)
    (hint : Integrable (fun z : 𝕍 ↦ z) μ) (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    ‖∫ z in cball, z ∂μ‖ ≤ (∫ z, ‖z‖ ^ 3 ∂μ) / δ ^ 2 := by
  have hs : MeasurableSet (cball) := Metric.isClosed_closedBall.measurableSet
  have hsplit := integral_add_compl hs hint
  rw [hcent] at hsplit
  have e : ∫ z in cball, z ∂μ = -∫ z in (cball)ᶜ, z ∂μ := by
    rw [eq_neg_iff_add_eq_zero]; exact hsplit
  rw [e, norm_neg]
  have hbound : ∀ᵐ z ∂μ.restrict (cball)ᶜ, ‖z‖ ≤ ‖z‖ ^ 3 / δ ^ 2 := by
    rw [ae_restrict_iff' hs.compl]
    refine ae_of_all _ fun z hz ↦ ?_
    rw [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (norm_nonneg z) (mul_nonneg (sub_nonneg.2 hz.le)
      (add_nonneg (norm_nonneg z) hδ.le))]
  calc ‖∫ z in (cball)ᶜ, z ∂μ‖ ≤ ∫ z in (cball)ᶜ, ‖z‖ ^ 3 / δ ^ 2 ∂μ :=
        norm_integral_le_of_norm_le (h3.div_const _).integrableOn hbound
    _ ≤ ∫ z, ‖z‖ ^ 3 / δ ^ 2 ∂μ :=
        setIntegral_le_integral (h3.div_const _) (ae_of_all _ fun z ↦ by positivity)
    _ = (∫ z, ‖z‖ ^ 3 ∂μ) / δ ^ 2 := integral_div _ _

/-- **The tail of the curvature term is controlled by the third moment**:
`‖∫_{‖z‖≤δ} C(A⁻¹z,A⁻¹z) dμ − E_μ C(A⁻¹Z,A⁻¹Z)‖ ≤ ‖A⁻¹‖‖T‖‖A⁻¹‖² M₃/δ`. -/
theorem norm_setIntegral_curvatureForm_sub_le (μ : Measure 𝕍) [IsFiniteMeasure μ] (θ₀ : 𝕍)
    (hδ : 0 < δ)
    (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    ‖(∫ z in cball, curvatureForm hS ν θ₀ z ∂μ) - ∫ z, curvatureForm hS ν θ₀ z ∂μ‖ ≤
      ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * ‖thirdOp hS ν θ₀‖ * ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ ^ 2 *
        (∫ z, ‖z‖ ^ 3 ∂μ) / δ := by
  set κ := ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * ‖thirdOp hS ν θ₀‖ *
    ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hs : MeasurableSet (cball) := Metric.isClosed_closedBall.measurableSet
  -- integrability of the curvature form on the whole space: `‖Cz‖ ≤ κ (1 + ‖z‖³)`
  have hIC : Integrable (curvatureForm hS ν θ₀) μ := by
    refine Integrable.mono' ((integrable_const (κ : ℝ)).add (h3.const_mul κ))
      (continuous_curvatureForm hS ν θ₀).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    have h := norm_curvatureForm_le hS ν θ₀ z
    have h2 : ‖z‖ ^ 2 ≤ 1 + ‖z‖ ^ 3 := by
      rcases le_or_gt ‖z‖ 1 with hz | hz
      · nlinarith [norm_nonneg z, pow_le_one₀ (norm_nonneg z) hz (n := 2),
          pow_nonneg (norm_nonneg z) 3]
      · nlinarith [norm_nonneg z, pow_le_pow_right₀ hz.le (by norm_num : (2 : ℕ) ≤ 3)]
    calc ‖curvatureForm hS ν θ₀ z‖ ≤ κ * ‖z‖ ^ 2 := h
      _ ≤ κ * (1 + ‖z‖ ^ 3) := mul_le_mul_of_nonneg_left h2 hκ0
      _ = κ + κ * ‖z‖ ^ 3 := by ring
  have hsplit := integral_add_compl hs hIC
  have e : (∫ z in cball, curvatureForm hS ν θ₀ z ∂μ) - ∫ z, curvatureForm hS ν θ₀ z ∂μ =
      -∫ z in (cball)ᶜ, curvatureForm hS ν θ₀ z ∂μ := by
    rw [← hsplit]; abel
  rw [e, norm_neg]
  have hbound : ∀ᵐ z ∂μ.restrict (cball)ᶜ, ‖curvatureForm hS ν θ₀ z‖ ≤ κ * ‖z‖ ^ 3 / δ := by
    rw [ae_restrict_iff' hs.compl]
    refine ae_of_all _ fun z hz ↦ ?_
    rw [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    refine (norm_curvatureForm_le hS ν θ₀ z).trans ?_
    rw [le_div_iff₀ hδ]
    have : ‖z‖ ^ 2 * δ ≤ ‖z‖ ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg ‖z‖) (sub_nonneg.2 hz.le)]
    calc κ * ‖z‖ ^ 2 * δ = κ * (‖z‖ ^ 2 * δ) := by ring
      _ ≤ κ * ‖z‖ ^ 3 := mul_le_mul_of_nonneg_left this hκ0
  calc ‖∫ z in (cball)ᶜ, curvatureForm hS ν θ₀ z ∂μ‖
      ≤ ∫ z in (cball)ᶜ, κ * ‖z‖ ^ 3 / δ ∂μ :=
        norm_integral_le_of_norm_le ((h3.const_mul κ).div_const δ).integrableOn hbound
    _ ≤ ∫ z, κ * ‖z‖ ^ 3 / δ ∂μ :=
        setIntegral_le_integral ((h3.const_mul κ).div_const δ)
          (ae_of_all _ fun z ↦ by positivity)
    _ = κ * (∫ z, ‖z‖ ^ 3 ∂μ) / δ := by rw [integral_div, integral_const_mul]

/-- **THE LOCALISED SAMPLING BIAS IS THE CURVATURE TERM**: for a centred law `μ` of the sampling
displacement with third absolute moment `M₃`,

`‖ E[θ̂_loc − θ₀] + ½ E_μ[C_{θ₀}(A⁻¹Z, A⁻¹Z)] ‖ ≤ (‖A⁻¹‖/δ² + K + ½ ‖A⁻¹‖‖T‖‖A⁻¹‖²/δ) M₃`,

where `θ̂_loc = θ₀ + 1_{‖ξ‖≤δ}(θr(m₀+ξ) − θ₀)` is the reset-localised response. -/
theorem localizedBias_curvature (μ : Measure 𝕍) [IsFiniteMeasure μ] (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z +
        (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z‖ ≤ K * ‖z‖ ^ 3)
    (hcent : ∫ z, z ∂μ = 0) (hint : Integrable (fun z : 𝕍 ↦ z) μ)
    (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    ‖(∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀) ∂μ) +
        (1 / 2 : ℝ) • ∫ z, curvatureForm hS ν θ₀ z ∂μ‖ ≤
      (‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ / δ ^ 2 + K +
        (1 / 2 : ℝ) * (‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * ‖thirdOp hS ν θ₀‖ *
          ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ ^ 2) / δ) * ∫ z, ‖z‖ ^ 3 ∂μ := by
  have h1 := localizedBias_decomposition hS ν μ θ₀ hdom hrem
  have h2 := norm_setIntegral_id_le_of_centred ν μ hδ hcent hint h3
  have h3' := norm_setIntegral_curvatureForm_sub_le hS ν μ θ₀ hδ h3
  have hball3 : ∫ z in cball, ‖z‖ ^ 3 ∂μ ≤ ∫ z, ‖z‖ ^ 3 ∂μ :=
    setIntegral_le_integral h3 (ae_of_all _ fun z ↦ by positivity)
  set B : 𝕍 →L[ℝ] 𝕍 := ((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) with hB
  set κ := ‖B‖ * ‖thirdOp hS ν θ₀‖ * ‖B‖ ^ 2 with hκ
  set M₃ := ∫ z, ‖z‖ ^ 3 ∂μ with hM₃
  set I := ∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀) ∂μ with hI
  set L := ∫ z in cball, z ∂μ with hL
  set Cδ := ∫ z in cball, curvatureForm hS ν θ₀ z ∂μ with hCδ
  set Cfull := ∫ z, curvatureForm hS ν θ₀ z ∂μ with hCfull
  have hA : ‖I - (B L - (1 / 2 : ℝ) • Cδ)‖ ≤ K * M₃ :=
    h1.trans (mul_le_mul_of_nonneg_left hball3 hK)
  have hBL : ‖B L‖ ≤ ‖B‖ * (M₃ / δ ^ 2) :=
    (B.le_opNorm L).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have hC : ‖(1 / 2 : ℝ) • (Cδ - Cfull)‖ ≤ (1 / 2 : ℝ) * (κ * M₃ / δ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left h3' (by norm_num)
  have e : I + (1 / 2 : ℝ) • Cfull = (I - (B L - (1 / 2 : ℝ) • Cδ)) + B L -
      (1 / 2 : ℝ) • (Cδ - Cfull) := by
    simp only [smul_sub]; abel
  rw [e]
  calc ‖(I - (B L - (1 / 2 : ℝ) • Cδ)) + B L - (1 / 2 : ℝ) • (Cδ - Cfull)‖
      ≤ ‖(I - (B L - (1 / 2 : ℝ) • Cδ)) + B L‖ + ‖(1 / 2 : ℝ) • (Cδ - Cfull)‖ := norm_sub_le _ _
    _ ≤ ‖I - (B L - (1 / 2 : ℝ) • Cδ)‖ + ‖B L‖ + ‖(1 / 2 : ℝ) • (Cδ - Cfull)‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ K * M₃ + ‖B‖ * (M₃ / δ ^ 2) + (1 / 2 : ℝ) * (κ * M₃ / δ) :=
        add_le_add (add_le_add hA hBL) hC
    _ = (‖B‖ / δ ^ 2 + K + (1 / 2 : ℝ) * κ / δ) * M₃ := by ring

end Law

end Laplace.Multi
