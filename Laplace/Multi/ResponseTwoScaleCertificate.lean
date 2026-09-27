/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSamplingGeometry

/-!
# The quadratic remainder of the response and the two-scale sign certificate

`ResponseSamplingGeometry` gave the second jet of the inverse mean map with an `o(‖e‖²)`
remainder. Here the remainder is made **quantitative on a ball**: for a `C²` map on an open set
containing `0`, `‖F(z) − F(0) − DF(0) z‖ ≤ K ‖z‖²` for `‖z‖ ≤ δ` (`exists_quadratic_remainder`,
two mean-value inequalities), and for the response `F(z) = m⁻¹(m(θ₀) + z)`
(`exists_responseTheta_quadratic_remainder`).

**The two-scale sign certificate** (`twoScale_sign_certificate`): for a truth displacement `t e`
and a sampling displacement `ξ` with `‖ξ‖ ≤ r`, and any covector `ℓ` (a wall),

`ℓ(θ̂) − ℓ(θ₀) ≥ t ℓ(B e) − ‖ℓ‖ ‖B‖ r − ‖ℓ‖ K (|t| ‖e‖ + r)²`,
`B = A_{θ₀}⁻¹`, `θ̂ = m⁻¹(m(θ₀) + t e + ξ)`.

Positivity of the right-hand side certifies the sign of the response shift across the wall `ℓ`
on the event `‖ξ‖ ≤ r` (`twoScale_sign_of_certificate`): the truth shift `t ℓ(Be)` must beat the
first-order sampling scale `‖ℓ‖‖B‖ r` and the curvature correction `‖ℓ‖ K (|t|‖e‖ + r)²`. This is
the deterministic core of the user's resolution story, with the chart's curvature included; the
probability of the event `‖ξ‖ ≤ r` is supplied separately by the sampling-risk bounds.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The quantitative quadratic remainder** of a `C²` map on a ball around `0`. -/
theorem exists_quadratic_remainder {F : E → G} {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
    (hF : ContDiffOn ℝ 2 F U) :
    ∃ δ > 0, ∃ K, 0 ≤ K ∧ ∀ z : E, ‖z‖ ≤ δ →
      ‖F z - F 0 - fderiv ℝ F 0 z‖ ≤ K * ‖z‖ ^ 2 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  have hsub : Metric.closedBall (0 : E) (δ / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  have hF1 : ContDiffOn ℝ 1 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ F)) U := hF1.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) (δ / 2)).exists_bound_of_continuousOn
    (hcont.mono hsub)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Metric.mem_closedBall_self (by positivity)))
  -- the derivative is `M`-Lipschitz on the closed ball
  have hlip : ∀ z ∈ Metric.closedBall (0 : E) (δ / 2), ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ M * ‖z‖ := by
    intro z hz
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ F) (C := M)
      (s := Metric.closedBall (0 : E) (δ / 2))
      (fun x hx ↦ (hF1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hsub hx)))
      hM (convex_closedBall 0 (δ / 2)) (Metric.mem_closedBall_self (by positivity)) hz
    simpa using h
  refine ⟨δ / 2, by positivity, M, hM0, fun z hz ↦ ?_⟩
  have hzball : z ∈ Metric.closedBall (0 : E) (δ / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hz
  -- the map `g = F − DF(0)` has derivative `DF(z) − DF(0)` on `U`
  have hg : ∀ x ∈ Metric.closedBall (0 : E) ‖z‖,
      HasFDerivAt (fun y ↦ F y - fderiv ℝ F 0 y) (fderiv ℝ F x - fderiv ℝ F 0) x := by
    intro x hx
    have hxU : x ∈ U := hsub (Metric.closedBall_subset_closedBall hz hx)
    exact ((hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hxU)).hasFDerivAt.sub
      (fderiv ℝ F 0).hasFDerivAt
  have hbound : ∀ x ∈ Metric.closedBall (0 : E) ‖z‖,
      ‖fderiv ℝ (fun y ↦ F y - fderiv ℝ F 0 y) x‖ ≤ M * ‖z‖ := by
    intro x hx
    rw [(hg x hx).fderiv]
    have hx' : x ∈ Metric.closedBall (0 : E) (δ / 2) := Metric.closedBall_subset_closedBall hz hx
    calc ‖fderiv ℝ F x - fderiv ℝ F 0‖ ≤ M * ‖x‖ := hlip x hx'
      _ ≤ M * ‖z‖ := by
          have : ‖x‖ ≤ ‖z‖ := by simpa using hx
          exact mul_le_mul_of_nonneg_left this hM0
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun y ↦ F y - fderiv ℝ F 0 y)
    (C := M * ‖z‖) (s := Metric.closedBall (0 : E) ‖z‖)
    (fun x hx ↦ (hg x hx).differentiableAt) hbound (convex_closedBall 0 ‖z‖)
    (Metric.mem_closedBall_self (norm_nonneg z)) (by rw [Metric.mem_closedBall, dist_zero_right])
  simp only [map_zero, sub_zero] at h
  calc ‖F z - F 0 - fderiv ℝ F 0 z‖ = ‖F z - fderiv ℝ F 0 z - F 0‖ := by congr 1; abel
    _ ≤ M * ‖z‖ * ‖z‖ := h
    _ = M * ‖z‖ ^ 2 := by ring

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

/-- The intrinsic chart. -/
local notation "chV" => chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

variable (S) in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The mean displacements at which the response is interior. -/
def responseBallDomain (θ₀ : 𝕍) : Set 𝕍 := {z | mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω}

omit [Nonempty J] in
theorem zero_mem_responseBallDomain (θ₀ : 𝕍) : (0 : 𝕍) ∈ responseBallDomain S ν θ₀ := by
  change mean (θ₀ : J → ℝ) + ((0 : 𝕍) : J → ℝ) ∈ Ω
  rw [Submodule.coe_zero, add_zero, ← tiltedMean_modelTilt hS ν]
  exact mean_tilted_mem_intrinsicInterior hS ν (bdd_modelTilt hS _)

theorem isOpen_responseBallDomain (θ₀ : 𝕍) : IsOpen (responseBallDomain S ν θ₀) := by
  have hE : responseBallDomain S ν θ₀ = (fun z : 𝕍 ↦ chV θ₀ + z) ⁻¹' Set.range chV := by
    ext z
    simp only [responseBallDomain, mem_preimage, mem_range_chartV_iff hS ν, Submodule.coe_add,
      chartV_apply, Set.mem_ofPred_eq]
    have e2 : mean (0 : J → ℝ) + (mean (θ₀ : J → ℝ) - mean (0 : J → ℝ) + (z : J → ℝ)) =
        mean (θ₀ : J → ℝ) + (z : J → ℝ) := by module
    rw [e2]
  rw [hE]
  exact (isOpen_range_chartV hS ν).preimage (continuous_const.add continuous_id)

/-- The response of a mean displacement is `C^∞` on the open domain. -/
theorem contDiffOn_responseTheta_meanAdd (θ₀ : 𝕍) :
    ContDiffOn ℝ ∞ (fun z : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)))
      (responseBallDomain S ν θ₀) := by
  have hE : (fun z : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ))) =
      (fun v : 𝕍 ↦ θr (mean (0 : J → ℝ) + (v : J → ℝ))) ∘ fun z : 𝕍 ↦ chV θ₀ + z := by
    funext z
    simp only [Function.comp_def, Submodule.coe_add, chartV_apply]
    congr 1
    module
  rw [hE]
  refine (contDiffOn_responseTheta_add hS ν).comp (contDiff_const.add contDiff_id).contDiffOn
    fun z hz ↦ ?_
  change mean (0 : J → ℝ) + ((chV θ₀ + z : 𝕍) : J → ℝ) ∈ Ω
  simp only [Submodule.coe_add, chartV_apply]
  have e2 : mean (0 : J → ℝ) + (mean (θ₀ : J → ℝ) - mean (0 : J → ℝ) + (z : J → ℝ)) =
      mean (θ₀ : J → ℝ) + (z : J → ℝ) := by module
  rw [e2]
  exact hz

/-- The derivative of the response in the mean displacement at `0` is `A_{θ₀}⁻¹`. -/
theorem fderiv_responseTheta_meanAdd_zero (θ₀ : 𝕍) :
    fderiv ℝ (fun z : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ))) 0 =
      ((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) := by
  have h :=
    (hasStrictFDerivAt_responseTheta_add hS ν (zero_mem_responseBallDomain hS ν θ₀)).hasFDerivAt
  simp only [Submodule.coe_zero, add_zero, responseTheta_meanMap hS ν] at h
  exact h.fderiv

/-- **The quantitative second jet of the response**: on a ball of mean displacements,
`‖m⁻¹(m(θ₀) + z) − θ₀ − A_{θ₀}⁻¹ z‖ ≤ K ‖z‖²`. -/
theorem exists_responseTheta_quadratic_remainder (θ₀ : 𝕍) :
    ∃ δ > 0, ∃ K, 0 ≤ K ∧ ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2 := by
  obtain ⟨δ, hδ, K, hK, h⟩ := exists_quadratic_remainder (isOpen_responseBallDomain hS ν θ₀)
    (zero_mem_responseBallDomain hS ν θ₀)
    ((contDiffOn_responseTheta_meanAdd hS ν θ₀).of_le (by exact_mod_cast natCast_le_infty 2))
  refine ⟨δ, hδ, K, hK, fun z hz ↦ ?_⟩
  have := h z hz
  rw [fderiv_responseTheta_meanAdd_zero hS ν] at this
  simp only [Submodule.coe_zero, add_zero, responseTheta_meanMap hS ν] at this
  exact this

/-- **The two-scale sign certificate**: for a truth displacement `t e` and a sampling displacement
`ξ` with `‖ξ‖ ≤ r`, the response shift across the wall `ℓ` satisfies
`ℓ(θ̂) − ℓ(θ₀) ≥ t ℓ(B e) − ‖ℓ‖ ‖B‖ r − ‖ℓ‖ K (|t| ‖e‖ + r)²`. -/
theorem twoScale_sign_certificate (θ₀ : 𝕍) {δ K : ℝ} (hK : 0 ≤ K)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2)
    (ℓ : 𝕍 →L[ℝ] ℝ) (e ξ : 𝕍) (t r : ℝ) (hr : ‖ξ‖ ≤ r) (hδ : ‖t • e + ξ‖ ≤ δ) :
    t * ℓ (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) e) - ‖ℓ‖ * ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * r -
        ‖ℓ‖ * K * (|t| * ‖e‖ + r) ^ 2 ≤
      ℓ (θr (mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ))) - ℓ θ₀ := by
  set B : 𝕍 →L[ℝ] 𝕍 := ((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) with hB
  set z : 𝕍 := t • e + ξ with hz
  set R : 𝕍 := θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - B z with hR
  have hR' : ‖R‖ ≤ K * ‖z‖ ^ 2 := hrem z hδ
  have hznorm : ‖z‖ ≤ |t| * ‖e‖ + r := by
    rw [hz]
    calc ‖t • e + ξ‖ ≤ ‖t • e‖ + ‖ξ‖ := norm_add_le _ _
      _ ≤ |t| * ‖e‖ + r := by rw [norm_smul, Real.norm_eq_abs]; linarith
  have hsq : ‖z‖ ^ 2 ≤ (|t| * ‖e‖ + r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hznorm 2
  have hdecomp : θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ = R + B z := by rw [hR]; abel
  have hℓR : -(‖ℓ‖ * K * (|t| * ‖e‖ + r) ^ 2) ≤ ℓ R := by
    have h1 : |ℓ R| ≤ ‖ℓ‖ * ‖R‖ := by
      have := ℓ.le_opNorm R
      rwa [Real.norm_eq_abs] at this
    have h2 : ‖ℓ‖ * ‖R‖ ≤ ‖ℓ‖ * K * (|t| * ‖e‖ + r) ^ 2 := by
      calc ‖ℓ‖ * ‖R‖ ≤ ‖ℓ‖ * (K * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hR' (norm_nonneg _)
        _ ≤ ‖ℓ‖ * (K * (|t| * ‖e‖ + r) ^ 2) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hK) (norm_nonneg _)
        _ = ‖ℓ‖ * K * (|t| * ‖e‖ + r) ^ 2 := by ring
    linarith [neg_abs_le (ℓ R)]
  have hℓξ : -(‖ℓ‖ * ‖B‖ * r) ≤ ℓ (B ξ) := by
    have h1 : |ℓ (B ξ)| ≤ ‖ℓ‖ * ‖B ξ‖ := by
      have := ℓ.le_opNorm (B ξ)
      rwa [Real.norm_eq_abs] at this
    have h2 : ‖B ξ‖ ≤ ‖B‖ * r :=
      (B.le_opNorm ξ).trans (mul_le_mul_of_nonneg_left hr (norm_nonneg _))
    have h3 : ‖ℓ‖ * ‖B ξ‖ ≤ ‖ℓ‖ * ‖B‖ * r := by
      calc ‖ℓ‖ * ‖B ξ‖ ≤ ‖ℓ‖ * (‖B‖ * r) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖ℓ‖ * ‖B‖ * r := by ring
    linarith [neg_abs_le (ℓ (B ξ))]
  have hlin : ℓ (B z) = t * ℓ (B e) + ℓ (B ξ) := by
    rw [hz, map_add, map_smul, map_add, map_smul, smul_eq_mul]
  have hsplit : ℓ (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ))) - ℓ θ₀ = ℓ R + ℓ (B z) := by
    rw [← map_sub, hdecomp, map_add]
  rw [hsplit, hlin]
  linarith

/-- **Sign resolution on the event `‖ξ‖ ≤ r`**: if the certificate is positive, the response moves
across the wall in the direction of the truth shift. -/
theorem twoScale_sign_of_certificate (θ₀ : 𝕍) {δ K : ℝ} (hK : 0 ≤ K)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2)
    (ℓ : 𝕍 →L[ℝ] ℝ) (e ξ : 𝕍) (t r : ℝ) (hr : ‖ξ‖ ≤ r) (hδ : ‖t • e + ξ‖ ≤ δ)
    (hcert : 0 < t * ℓ (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) e) - ‖ℓ‖ * ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * r -
      ‖ℓ‖ * K * (|t| * ‖e‖ + r) ^ 2) :
    ℓ θ₀ < ℓ (θr (mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ))) := by
  have := twoScale_sign_certificate hS ν θ₀ hK hrem ℓ e ξ t r hr hδ
  linarith

end Response

end Laplace.Multi
