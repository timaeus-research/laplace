/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseEndpointInformationAction
import Laplace.Multi.ResponseClassResolution
import Mathlib.Analysis.Calculus.Taylor

/-!
# The second jet of the response to a mean displacement: truth and sampling

Two sources displace the structural coordinate: the truth moves along a mean path `μ(t)` in the
interior response domain, and sampling displaces the empirical mean by `e_n = M̂_n − μ`. Both are
read through the **same second jet of the inverse mean map** `θ = m⁻¹`:

* `hasDerivAt_responseTheta_meanPath`: along `μ(t) = m(θ₀) + z(t)` the response has velocity
  `θ' = A_θ⁻¹ z'`;
* `hasDerivAt_meanPathVel`: **the truth second jet** `θ'' = A_θ⁻¹ z'' − C_θ(θ', θ')`;
* `responseLine_taylor_two`: **the deterministic expansion in a mean displacement** `e ∈ W`,
  `θ(μ + t e) = θ + t A⁻¹e − (t²/2) C(A⁻¹e, A⁻¹e) + o(t²)`.

Applied to the truth displacement this is the curvature of a moving truth; applied to the sampling
displacement `e_n` (whose Fisher-normalised size is `tr(R_θ C_D)/n` in expectation,
`integral_samplingEnergy`, with the chamber guarantee `measureReal_sampleResponse_notMem_le`) it
is the second-order sampling response. The m-Christoffel term is the same in both: it is the
response chart's own curvature, not a property of either source.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ContDiff

namespace Laplace.Multi

section Jet

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

/-- **The response velocity along a mean path** `μ(t) = m(θ₀) + z(t)`: `θ' = A_θ⁻¹ z'`, at every
time where the mean is interior. -/
theorem hasDerivAt_responseTheta_meanPath (θ₀ : 𝕍) {z z' : ℝ → 𝕍} (hz : ∀ t, HasDerivAt z (z' t) t)
    {t₀ : ℝ} (hΩ : mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ) ∈ Ω) :
    HasDerivAt (fun t ↦ θr (mean (θ₀ : J → ℝ) + (z t : J → ℝ)))
      ((CDE (θr (mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ)))).symm (z' t₀)) t₀ := by
  have hstrict := hasStrictFDerivAt_responseTheta_add hS ν hΩ
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → 𝕍, w = fun t ↦ z t - z t₀ := ⟨_, rfl⟩
  have hw : HasDerivAt w (z' t₀) t₀ := by
    rw [hwdef]
    exact (hz t₀).sub_const _
  have hw0 : w t₀ = 0 := by rw [hwdef]; exact sub_self _
  have hF : HasFDerivAt (fun v : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ) + v))
      ((CDE (θr (mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ)))).symm : 𝕍 →L[ℝ] 𝕍) (w t₀) := by
    rw [hw0]
    exact hstrict.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt t₀ hw
  refine (hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv rfl
  change θr (mean (θ₀ : J → ℝ) + (z t : J → ℝ)) =
    θr (mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ) + (w t : J → ℝ))
  rw [hwdef]
  simp only [Submodule.coe_sub]
  congr 1
  abel

/-- **The truth second jet**: along a `C²` mean path `μ(t) = m(θ₀) + z(t)` the response velocity
`V = A_θ⁻¹ z'` satisfies `V' = A_θ⁻¹ z'' − C_θ(V, V)`. -/
theorem hasDerivAt_meanPathVel (θ₀ : 𝕍) {z z' z'' : ℝ → 𝕍} (hz : ∀ t, HasDerivAt z (z' t) t)
    (hz' : ∀ t, HasDerivAt z' (z'' t) t) {t₀ : ℝ}
    (hΩ : mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ) ∈ Ω) :
    HasDerivAt (fun t ↦ (CDE (θr (mean (θ₀ : J → ℝ) + (z t : J → ℝ)))).symm (z' t))
      ((CDE (θr (mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ)))).symm (z'' t₀) -
        mChristoffel hS ν (θr (mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ)))
          ((CDE (θr (mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ)))).symm (z' t₀))
          ((CDE (θr (mean (θ₀ : J → ℝ) + (z t₀ : J → ℝ)))).symm (z' t₀))) t₀ := by
  set θ : ℝ → 𝕍 := fun t ↦ θr (mean (θ₀ : J → ℝ) + (z t : J → ℝ)) with hθ
  have hθd : HasDerivAt θ ((CDE (θ t₀)).symm (z' t₀)) t₀ :=
    hasDerivAt_responseTheta_meanPath hS ν θ₀ hz hΩ
  have h0 := (hasFDerivAt_inverse_natural hS ν (θ t₀)).comp_hasDerivAt t₀ hθd
  have h1 : HasDerivAt (fun s ↦ (ContinuousLinearEquiv.symm (CDE (θ s)) : 𝕍 →L[ℝ] 𝕍))
      ((-ContinuousLinearMap.mulLeftRight ℝ _
        (ContinuousLinearEquiv.symm (CDE (θ t₀)) : 𝕍 →L[ℝ] 𝕍)
        (ContinuousLinearEquiv.symm (CDE (θ t₀)) : 𝕍 →L[ℝ] 𝕍))
          (thirdOp hS ν (θ t₀) ((CDE (θ t₀)).symm (z' t₀)))) t₀ := h0
  have h2 := h1.clm_apply (hz' t₀)
  refine h2.congr_deriv ?_
  simp only [_root_.neg_apply]
  rw [add_comm, ← sub_eq_add_neg]
  rfl

/-- **The response line** `t ↦ θ(m(θ₀) + t e)` in a mean displacement `e ∈ W`. -/
noncomputable def responseLine (θ₀ e : 𝕍) (t : ℝ) : 𝕍 := θr (mean (θ₀ : J → ℝ) + t • (e : J → ℝ))

variable (S) in
omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The parameters at which the response line is interior. -/
def responseLineDomain (θ₀ e : 𝕍) : Set ℝ := {t | mean (θ₀ : J → ℝ) + t • (e : J → ℝ) ∈ Ω}

omit [Nonempty J] in
/-- The base point of a response line is interior. -/
theorem zero_mem_responseLineDomain (θ₀ e : 𝕍) : (0 : ℝ) ∈ responseLineDomain S ν θ₀ e := by
  change mean (θ₀ : J → ℝ) + (0 : ℝ) • (e : J → ℝ) ∈ Ω
  rw [zero_smul, add_zero, ← tiltedMean_modelTilt hS ν]
  exact mean_tilted_mem_intrinsicInterior hS ν (bdd_modelTilt hS _)

/-- The response line domain is open. -/
theorem isOpen_responseLineDomain (θ₀ e : 𝕍) : IsOpen (responseLineDomain S ν θ₀ e) := by
  have hE : responseLineDomain S ν θ₀ e = (fun t : ℝ ↦ chV θ₀ + t • e) ⁻¹' Set.range chV := by
    ext t
    simp only [responseLineDomain, mem_preimage, mem_range_chartV_iff hS ν, Submodule.coe_add,
      Submodule.coe_smul, chartV_apply, Set.mem_ofPred_eq]
    have e2 : mean (0 : J → ℝ) + (mean (θ₀ : J → ℝ) - mean (0 : J → ℝ) + t • (e : J → ℝ)) =
        mean (θ₀ : J → ℝ) + t • (e : J → ℝ) := by module
    rw [e2]
  rw [hE]
  exact (isOpen_range_chartV hS ν).preimage (continuous_const.add (continuous_id.smul
    continuous_const))

/-- The response line is `C^∞` on its open domain. -/
theorem contDiffOn_responseLine (θ₀ e : 𝕍) :
    ContDiffOn ℝ ∞ (responseLine hS ν θ₀ e) (responseLineDomain S ν θ₀ e) := by
  have hE : responseLine hS ν θ₀ e =
      (fun v : 𝕍 ↦ θr (mean (0 : J → ℝ) + (v : J → ℝ))) ∘ fun t : ℝ ↦ chV θ₀ + t • e := by
    funext t
    simp only [Function.comp_def, responseLine, Submodule.coe_add, Submodule.coe_smul,
      chartV_apply]
    congr 1
    module
  rw [hE]
  refine (contDiffOn_responseTheta_add hS ν).comp
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn fun t ht ↦ ?_
  change mean (0 : J → ℝ) + ((chV θ₀ + t • e : 𝕍) : J → ℝ) ∈ Ω
  simp only [Submodule.coe_add, Submodule.coe_smul, chartV_apply]
  have e2 : mean (0 : J → ℝ) + (mean (θ₀ : J → ℝ) - mean (0 : J → ℝ) + t • (e : J → ℝ)) =
      mean (θ₀ : J → ℝ) + t • (e : J → ℝ) := by module
  rw [e2]
  exact ht

/-- The velocity of the response line, `A_θ⁻¹ e`. -/
noncomputable def responseLineVel (θ₀ e : 𝕍) (t : ℝ) : 𝕍 :=
  (CDE (responseLine hS ν θ₀ e t)).symm e

theorem hasDerivAt_responseLine (θ₀ e : 𝕍) {t₀ : ℝ} (ht : t₀ ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (responseLine hS ν θ₀ e) (responseLineVel hS ν θ₀ e t₀) t₀ := by
  have hz : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ t • e) e t := fun t ↦ by
    simpa using (hasDerivAt_id t).smul_const e
  have h := hasDerivAt_responseTheta_meanPath hS ν θ₀ hz (t₀ := t₀) ht
  exact h

/-- **The response line bends by the m-Christoffel symbol**: `V' = −C_θ(V, V)`. -/
theorem hasDerivAt_responseLineVel (θ₀ e : 𝕍) {t₀ : ℝ} (ht : t₀ ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (responseLineVel hS ν θ₀ e)
      (-mChristoffel hS ν (responseLine hS ν θ₀ e t₀) (responseLineVel hS ν θ₀ e t₀)
        (responseLineVel hS ν θ₀ e t₀)) t₀ := by
  have hz : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ t • e) e t := fun t ↦ by
    simpa using (hasDerivAt_id t).smul_const e
  have hz' : ∀ t : ℝ, HasDerivAt (fun _ : ℝ ↦ e) (0 : 𝕍) t := fun t ↦ hasDerivAt_const t e
  have h := hasDerivAt_meanPathVel hS ν θ₀ hz hz' (t₀ := t₀) ht
  simp only [map_zero, zero_sub] at h
  exact h

/-- **The second-order expansion of the response in a mean displacement**:
`θ(m(θ₀) + t e) = θ₀ + t A⁻¹e − (t²/2) C_{θ₀}(A⁻¹e, A⁻¹e) + o(t²)`. Applied to the truth
displacement and to the sampling displacement alike. -/
theorem responseLine_taylor_two (θ₀ e : 𝕍) :
    (fun t : ℝ ↦ responseLine hS ν θ₀ e t - θ₀ - t • responseLineVel hS ν θ₀ e 0 +
        (t ^ 2 / 2) • mChristoffel hS ν θ₀ (responseLineVel hS ν θ₀ e 0)
          (responseLineVel hS ν θ₀ e 0))
      =o[𝓝 (0 : ℝ)] fun t ↦ t ^ 2 := by
  -- a ball around `0` inside the domain
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_responseLineDomain hS ν θ₀ e) 0
    (zero_mem_responseLineDomain hS ν θ₀ e)
  have hnhds : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
  have h2 : ContDiffOn ℝ 2 (responseLine hS ν θ₀ e) (Metric.ball 0 δ) :=
    ((contDiffOn_responseLine hS ν θ₀ e).mono hball).of_le (by exact_mod_cast natCast_le_infty 2)
  have h := taylor_isLittleO (convex_ball (0 : ℝ) δ) (Metric.mem_ball_self hδ) h2
  rw [Metric.isOpen_ball.nhdsWithin_eq (Metric.mem_ball_self hδ)] at h
  simp only [sub_zero] at h
  refine h.congr_left fun t ↦ ?_
  -- identify the Taylor coefficients
  have hline0 : responseLine hS ν θ₀ e 0 = θ₀ := by
    unfold responseLine
    rw [zero_smul, add_zero, responseTheta_meanMap hS ν]
  have hd1 : deriv (responseLine hS ν θ₀ e) 0 = responseLineVel hS ν θ₀ e 0 :=
    (hasDerivAt_responseLine hS ν θ₀ e (zero_mem_responseLineDomain hS ν θ₀ e)).deriv
  have hdev : deriv (responseLine hS ν θ₀ e) =ᶠ[𝓝 (0 : ℝ)] responseLineVel hS ν θ₀ e := by
    filter_upwards [(isOpen_responseLineDomain hS ν θ₀ e).mem_nhds
      (zero_mem_responseLineDomain hS ν θ₀ e)] with s hs
    exact (hasDerivAt_responseLine hS ν θ₀ e hs).deriv
  have hd2 : deriv (deriv (responseLine hS ν θ₀ e)) 0 =
      -mChristoffel hS ν θ₀ (responseLineVel hS ν θ₀ e 0) (responseLineVel hS ν θ₀ e 0) := by
    rw [hdev.deriv_eq, (hasDerivAt_responseLineVel hS ν θ₀ e
      (zero_mem_responseLineDomain hS ν θ₀ e)).deriv, hline0]
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
    iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hδ),
    iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hδ),
    iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one, hd1, hd2, hline0]
  simp only [Nat.factorial, Nat.cast_one, sub_zero]
  norm_num [sub_sub]
  module

end Jet

end Laplace.Multi
