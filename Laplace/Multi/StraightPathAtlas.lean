/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ChartContinuity
import Laplace.Multi.EndpointConvergence

/-!
# The atlas of the straight path from the featureless response to the data

For a response `M` of finite rate, the straight mean path `M_s = (1 − s) m₀ + s M` from the
featureless response `m₀ = E_ν S` to `M` is the canonical bridge across the response space. This
file collects its atlas:

* `atlas_mem_intrinsicInterior`: `M_s` lies in the relative interior for `0 ≤ s < 1`, so its
  canonical representative is the family member at the natural coordinates `atlasTheta s`;
* `hasDerivAt_atlasTheta`: the natural coordinates are `C¹` on `[0, 1)`, with velocity
  `atlasVel s = (Dm(θ_s)|_𝕍)⁻¹ Δ`, `Δ = M − m₀`;
* `hasDerivAt_atlasRate`: `d/ds 𝓘(M_s) = −⟨θ_s, Δ⟩`, and `hasDerivAt_atlasVelocity`: the curvature
  `atlasCurv s` is the variance of the dual velocity contrast `⟨atlasVel s, S⟩` under the
  representative (`atlasCurv_eq_priorCov`, `atlasCurv_nonneg`) — `⟨Δ, C_{θ_s}⁻¹ Δ⟩` in the dual
  Fisher metric;
* **`genRate_atlasPath_eq_integral`**: the integrated Fisher budget
  `𝓘(M_r) = ∫₀ʳ (r − s) atlasCurv s ds` for `0 ≤ r < 1`, and **`tendsto_integral_atlasCurv`**:
  `∫₀ʳ (r − s) atlasCurv s ds → 𝓘(M)` as `r ↑ 1` — finite endpoint information is the limit of the
  weighted dual-Fisher energy along the bridge;
* `atlas_decomposition_mixture`: for a data law `D` with response `M` and finite information, the
  mixtures `(1 − b) ν + b D` have responses `M_b` and satisfy the information decomposition
  `KL(D_b ‖ ν) = 𝓘(M_b) + KL(D_b ‖ Π(M_b))` — the actual journey, the visible journey and the
  invisible information.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}

variable (S M) in
/-- **The straight mean path** `M_s = (1 − s) m₀ + s M`. -/
noncomputable def atlasPath (s : ℝ) : J → ℝ :=
  (1 - s) • meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 + s • M

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem atlasPath_zero :
    atlasPath S ν M 0 = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 := by
  simp [atlasPath]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem atlasPath_one : atlasPath S ν M 1 = M := by
  simp [atlasPath]

omit [Nonempty X] [Nonempty J] in
theorem atlasPath_eq (s : ℝ) :
    atlasPath S ν M s = (1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M := by
  rw [atlasPath, meanMap_zero_eq_mean ν]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem atlasPath_sub (s : ℝ) :
    atlasPath S ν M s - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 =
      s • (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  unfold atlasPath
  module

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem hasDerivAt_atlasPath (s : ℝ) :
    HasDerivAt (atlasPath S ν M) (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) s := by
  have h := (((hasDerivAt_id s).const_sub (1 : ℝ)).smul_const
    (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)).add ((hasDerivAt_id s).smul_const M)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp [atlasPath]
  · module

variable (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The canonical representative of `M` is absolutely continuous with respect to `ν`. -/
theorem responseProjection_absolutelyContinuous : responseProjection hS ν M ≪ ν := by
  obtain ⟨hP, -, hkl, -⟩ := responseProjection_spec hS ν hfin
  have := hP
  refine (klDiv_ne_top_iff.1 ?_).1
  rw [hkl]
  exact hfin

/-- **The straight path lies in the relative interior before the endpoint.** -/
theorem atlas_mem_intrinsicInterior {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    atlasPath S ν M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  obtain ⟨hP, hM, -, -⟩ := responseProjection_spec hS ν hfin
  have := hP
  have h := segment_mem_intrinsicInterior hS ν (responseProjection hS ν M)
    (responseProjection_absolutelyContinuous hS ν hfin) hs0 hs1
  rw [hM] at h
  rw [atlasPath_eq]
  exact h

/-- A response of finite rate lies in the moment body. -/
theorem mem_momentBody_of_genRate_ne_top : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
  refine (isClosed_momentBody S).mem_of_tendsto (f := atlasPath S ν M) (b := 𝓝[<] 1) ?_ ?_
  · have hc : Continuous (atlasPath S ν M) := by
      unfold atlasPath
      fun_prop
    have : Tendsto (atlasPath S ν M) (𝓝[<] 1) (𝓝 (atlasPath S ν M 1)) :=
      (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    rwa [atlasPath_one] at this
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
    exact intrinsicInterior_subset (atlas_mem_intrinsicInterior hS ν hfin hs.1.le hs.2)

/-- The displacement `Δ = M − m₀` is visible. -/
theorem sub_mem_dirSpan_of_genRate_ne_top :
    M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (mem_momentBody_of_genRate_ne_top hS ν hfin)

theorem atlasPath_sub_mem_dirSpan (s : ℝ) :
    atlasPath S ν M s - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈
      dirSpan ν (fun _ ↦ (1 : ℝ)) S := by
  rw [atlasPath_sub]
  exact Submodule.smul_mem _ _ (sub_mem_dirSpan_of_genRate_ne_top hS ν hfin)

omit hfin in
variable (M) in
/-- **The natural coordinates along the straight path**, `θ_s = θ(M_s)`. -/
noncomputable def atlasTheta (s : ℝ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
    (atlasPath S ν M s)

/-- **The velocity of the natural coordinates**, `(Dm(θ_s)|_𝕍)⁻¹ Δ`. -/
noncomputable def atlasVel (s : ℝ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
    (atlasTheta hS ν M s)).symm
    ⟨M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0,
      sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩

/-- **The curvature of the rate along the straight path**, `⟨Δ, C_{θ_s}⁻¹ Δ⟩`. -/
noncomputable def atlasCurv (s : ℝ) : ℝ :=
  -dotJ (atlasVel hS ν hfin s : J → ℝ) (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)

omit hfin in
theorem atlasTheta_zero : atlasTheta hS ν M 0 = 0 := by
  unfold atlasTheta responseTheta
  rw [atlasPath_zero]
  have h0 : toV ν (fun _ ↦ (1 : ℝ)) S (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) =
      0 := by
    apply Subtype.ext
    rw [toV_apply (by rw [sub_self]; exact Submodule.zero_mem _)]
    simp
  rw [h0]
  have hc : chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
      (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) = 0 := by
    apply Subtype.ext
    rw [chartV_apply]
    simp
  have := chartVInv_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  rwa [hc] at this

/-- **The natural coordinates are differentiable along the straight path before the endpoint.** -/
theorem hasDerivAt_atlasTheta {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (atlasTheta hS ν M) (atlasVel hS ν hfin s) s :=
  hasDerivAt_responseTheta_path measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (atlasPath_sub_mem_dirSpan hS ν hfin)
    (atlas_mem_intrinsicInterior hS ν hfin hs0 hs1) (hasDerivAt_atlasPath ν s)

/-- **The rate along the straight path**: `d/ds 𝓘(M_s) = −⟨θ_s, Δ⟩`. -/
theorem hasDerivAt_atlasRate {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (fun s ↦ (genRate ν S (atlasPath S ν M s)).toReal)
      (-dotJ (atlasTheta hS ν M s : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) s :=
  hasDerivAt_genRate_path hS ν (atlasPath_sub_mem_dirSpan hS ν hfin)
    (atlas_mem_intrinsicInterior hS ν hfin hs0 hs1) (hasDerivAt_atlasPath ν s)

/-- **The velocity of the rate is differentiable, with derivative the curvature.** -/
theorem hasDerivAt_atlasVelocity {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (fun s ↦ -dotJ (atlasTheta hS ν M s : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0))
      (atlasCurv hS ν hfin s) s := by
  have hθ := (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_atlasTheta hS ν hfin hs0 hs1)
  have h := ((dotCLM (M - meanMap ν (fun _ ↦ (1 : ℝ))
    (fun _ ↦ (0 : ℝ)) S 1 0)).hasFDerivAt.comp_hasDerivAt s hθ).neg
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp only [Pi.neg_apply, Function.comp_apply, dotCLM_apply, Submodule.subtypeL_apply]
  · simp only [dotCLM_apply, Submodule.subtypeL_apply, atlasCurv]

/-- **The curvature is the variance of the dual velocity contrast under the representative.** -/
theorem atlasCurv_eq_priorCov (s : ℝ) :
    atlasCurv hS ν hfin s =
      priorCov ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S (atlasTheta hS ν M s))
        (dirLoss S (atlasVel hS ν hfin s)) (dirLoss S (atlasVel hS ν hfin s)) 1 := by
  have hcd : ∀ w, chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (atlasTheta hS ν M s) w =
      chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        (atlasTheta hS ν M s) w :=
    fun w ↦ by
      rw [← coe_chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (atlasTheta hS ν M s)]
      rfl
  have hΔ : chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS (atlasTheta hS ν M s) (atlasVel hS ν hfin s) =
      ⟨M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0,
        sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ := by
    unfold atlasVel
    rw [← hcd]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have h := congrArg (fun v : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦
    dotJ (atlasVel hS ν hfin s : J → ℝ) (v : J → ℝ)) hΔ
  simp only at h
  rw [dotJ_chartDeriv] at h
  unfold atlasCurv
  rw [← h, neg_neg]

theorem atlasCurv_nonneg (s : ℝ) : 0 ≤ atlasCurv hS ν hfin s := by
  rw [atlasCurv_eq_priorCov, priorCov_eq_lawCov_familyMeasure hS ν]
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have := isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const h0 hS (t := 1) (atlasTheta hS ν M s)
  exact lawCov_self_nonneg _ (bdd_dirLoss hS _)

/-- The curvature is continuous before the endpoint. -/
theorem continuousAt_atlasCurv {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ContinuousAt (atlasCurv hS ν hfin) s := by
  have hθ : ContinuousAt (atlasTheta hS ν M) s :=
    (hasDerivAt_atlasTheta hS ν hfin hs0 hs1).continuousAt
  have hsymm : ContinuousAt (fun s ↦ ((chartDerivEquiv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M s)).symm :
        dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S)) s :=
    (continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).continuousAt.comp hθ
  have hvel : ContinuousAt (atlasVel hS ν hfin) s := hsymm.clm_apply continuousAt_const
  have e : atlasCurv hS ν hfin = fun s ↦
      -(dotCLM (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
        (atlasVel hS ν hfin s : J → ℝ)) :=
    funext fun s ↦ by simp [atlasCurv, dotCLM_apply]
  rw [e]
  exact ((dotCLM (M - meanMap ν (fun _ ↦ (1 : ℝ))
    (fun _ ↦ (0 : ℝ)) S 1 0)).continuous.continuousAt.comp
    (continuous_subtype_val.continuousAt.comp hvel)).neg

omit [Nonempty X] [Nonempty J] hfin in
/-- The rate vanishes at the start of the path. -/
theorem genRate_atlasPath_zero : genRate ν S (atlasPath S ν M 0) = 0 := by
  rw [atlasPath_zero, meanMap_zero_eq_mean ν]
  exact genRate_mean_eq_zero ν hS

/-- **The velocity of the rate is the integrated curvature**: `−⟨θ_r, Δ⟩ = ∫₀ʳ atlasCurv`. -/
theorem neg_dotJ_atlasTheta_eq_integral {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    -dotJ (atlasTheta hS ν M r : J → ℝ) (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) =
      ∫ s in (0 : ℝ)..r, atlasCurv hS ν hfin s := by
  have hint : IntervalIntegrable (atlasCurv hS ν hfin) volume 0 r := by
    refine ContinuousOn.intervalIntegrable fun s hs ↦ ?_
    rw [uIcc_of_le hr0] at hs
    exact (continuousAt_atlasCurv hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ -dotJ (atlasTheta hS ν M s : J → ℝ)
      (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) (fun s hs ↦ ?_) hint]
  · rw [atlasTheta_zero, Submodule.coe_zero, dotJ_zero_left, neg_zero, sub_zero]
  · rw [uIcc_of_le hr0] at hs
    exact hasDerivAt_atlasVelocity hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)

/-- **The integrated Fisher budget**: `𝓘(M_r) = ∫₀ʳ (r − s) atlasCurv s ds` for `0 ≤ r < 1`. -/
theorem genRate_atlasPath_eq_integral {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (genRate ν S (atlasPath S ν M r)).toReal =
      ∫ s in (0 : ℝ)..r, (r - s) * atlasCurv hS ν hfin s := by
  have hcurv : IntervalIntegrable (atlasCurv hS ν hfin) volume 0 r := by
    refine ContinuousOn.intervalIntegrable fun s hs ↦ ?_
    rw [uIcc_of_le hr0] at hs
    exact (continuousAt_atlasCurv hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)).continuousWithinAt
  have hvel : IntervalIntegrable (fun s ↦ -dotJ (atlasTheta hS ν M s : J → ℝ)
      (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) volume 0 r := by
    refine ContinuousOn.intervalIntegrable fun s hs ↦ ?_
    rw [uIcc_of_le hr0] at hs
    exact (hasDerivAt_atlasVelocity hS ν hfin hs.1
      (lt_of_le_of_lt hs.2 hr1)).continuousAt.continuousWithinAt
  -- first integration
  have h1 : (genRate ν S (atlasPath S ν M r)).toReal = ∫ s in (0 : ℝ)..r,
      -dotJ (atlasTheta hS ν M s : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s ↦ (genRate ν S (atlasPath S ν M s)).toReal) (fun s hs ↦ ?_) hvel]
    · rw [genRate_atlasPath_zero hS ν, ENNReal.toReal_zero, sub_zero]
    · rw [uIcc_of_le hr0] at hs
      exact hasDerivAt_atlasRate hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)
  -- integration by parts with `u s = s − r`
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub (u := fun s ↦ s - r) (u' := fun _ ↦ 1)
    (v := fun s ↦ -dotJ (atlasTheta hS ν M s : J → ℝ)
      (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0))
    (v' := atlasCurv hS ν hfin) (a := 0) (b := r)
    (fun s _ ↦ (hasDerivAt_id s).sub_const r)
    (fun s hs ↦ by
      rw [uIcc_of_le hr0] at hs
      exact hasDerivAt_atlasVelocity hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1))
    (continuousOn_const.intervalIntegrable) hcurv
  simp only [sub_self, zero_mul, zero_sub, atlasTheta_zero, Submodule.coe_zero, dotJ_zero_left,
    neg_zero, mul_zero, one_mul] at hibp
  rw [intervalIntegral.integral_add hvel (hcurv.continuousOn_mul (by
    exact (continuous_id.sub continuous_const).continuousOn))] at hibp
  have e2 : ∫ s in (0 : ℝ)..r, (r - s) * atlasCurv hS ν hfin s =
      -∫ s in (0 : ℝ)..r, (s - r) * atlasCurv hS ν hfin s := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun s _ ↦ by ring
  rw [h1, e2]
  linarith

/-- **The finite endpoint information is the limit of the weighted dual-Fisher energy along the
bridge**: `∫₀ʳ (r − s) atlasCurv s ds → 𝓘(M)` as `r ↑ 1`. -/
theorem tendsto_integral_atlasCurv :
    Tendsto (fun r ↦ ∫ s in (0 : ℝ)..r, (r - s) * atlasCurv hS ν hfin s) (𝓝[<] 1)
      (𝓝 (genRate ν S M).toReal) := by
  have h := (ENNReal.tendsto_toReal hfin).comp (tendsto_genRate_segment hS ν hfin)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
  simp only [Function.comp]
  rw [← atlasPath_eq, genRate_atlasPath_eq_integral hS ν hfin hr.1.le hr.2]

/-- **The information decomposition along the mixture bridge**: for a data law `D` with response
`M` and finite information, the mixture `(1 − b) ν + b D` has response `M_b` and
`KL(D_b ‖ ν) = 𝓘(M_b) + KL(D_b ‖ Π(M_b))`. -/
theorem atlas_decomposition_mixture (D : Measure X) [IsProbabilityMeasure D]
    (hD : (fun i ↦ ∫ x, S i x ∂D) = M) (a b : ℝ≥0) (hab : a + b = 1) :
    klDiv (a • ν + b • D) ν =
      genRate ν S (atlasPath S ν M b) +
        klDiv (a • ν + b • D) (responseProjection hS ν (atlasPath S ν M b)) := by
  have hP := isProbabilityMeasure_mixture ν D hab
  have hmean : (fun i ↦ ∫ x, S i x ∂(a • ν + b • D)) = atlasPath S ν M b := by
    rw [mean_mixture hS ν D a b, hD, atlasPath_eq]
    congr 2
    have : (a : ℝ) = 1 - b := by
      have h := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hab
      simp only [NNReal.coe_add, NNReal.coe_one] at h
      linarith
    rw [this]
  have hb1 : (b : ℝ) ≤ 1 := by
    have h := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hab
    simp only [NNReal.coe_add, NNReal.coe_one] at h
    linarith [a.coe_nonneg]
  have hfinb : genRate ν S (atlasPath S ν M b) ≠ ⊤ := by
    intro h
    have := genRate_segment_le hS ν b.coe_nonneg hb1 (M := M)
    rw [← atlasPath_eq, h, top_le_iff, ENNReal.mul_eq_top] at this
    rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hfin h2
    · exact ENNReal.ofReal_ne_top h1
  have := information_decomposition hS ν (a • ν + b • D) (by rw [hmean]; exact hfinb)
  rw [hmean] at this
  exact this

end Laplace.Multi
