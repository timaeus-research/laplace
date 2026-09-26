/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DifferentialRetraction
import Laplace.Multi.EmpiricalTotalVariation
import Laplace.Multi.DensityPeanoUniform

/-!
# The reconstruction density is `C¹` into `L¹`

The derivative `M ↦ Dp_M = (u ↦ [q_M ℓ_{M,u}])` of the reconstruction density is continuous in
operator norm on the relative interior (`continuousWithinAt_reconstructionDeriv`), by the explicit
bound

`‖Dp_{M'} − Dp_M‖ ≤ |J|(‖M‖+B)‖R_M‖ ∫|q_{M'} − q_M| + |J|(‖M‖+B)‖R_{M'} − R_M‖`
`+ |J|‖R_{M'}‖‖M' − M‖` (`norm_reconstructionDeriv_sub_le`),

whose three terms vanish as `M' → M` by the compact-uniform total-variation Lipschitz bound, the
continuity of the inverse chart derivative, and the boundedness of `R` near `M`. Together with
`hasFDerivAt_reconstructionL1` this makes `p : M ↦ [q_M]` a `C¹` map of the relative interior into
`L¹(ν)` whose differential is the regression tangent map.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The inverse chart derivative at a response, as a continuous linear map. -/
local notation "Rat" M => (ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)

/-- The difference of two response scores in the same direction. -/
theorem responseScore_sub_responseScore (M M' : J → ℝ) (u : 𝕍) (x : X) :
    responseScore hS ν M' u x - responseScore hS ν M u x =
      affScoreAt S M (((Rat M') u : 𝕍) - (Rat M) u : J → ℝ) x +
        dotJ ((Rat M') u : J → ℝ) (M' - M) := by
  unfold responseScore affScoreAt dotJ dirLoss
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, ContinuousLinearEquiv.coe_coe]
  ring

/-- **The explicit modulus of the derivative**: `‖Dp_{M'} − Dp_M‖ ≤ |J|(‖M‖+B)‖R_M‖ ∫|q_{M'} − q_M|`
`+ |J|(‖M‖+B)‖R_{M'} − R_M‖ + |J|‖R_{M'}‖‖M' − M‖`. -/
theorem norm_reconstructionDeriv_sub_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B)
    (M M' : J → ℝ) :
    ‖reconstructionDeriv hS ν M' - reconstructionDeriv hS ν M‖ ≤
      (Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖ *
          (∫ x, |famDens S ν (θr M') x - famDens S ν (θr M) x| ∂ν) +
        (Fintype.card J : ℝ) * (‖M‖ + B) * ‖(Rat M') - Rat M‖ +
        (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖ := by
  have hK0 : 0 ≤ (Fintype.card J : ℝ) * (‖M‖ + B) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  rw [sub_apply, reconstructionDeriv_apply, reconstructionDeriv_apply,
    ← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  -- the score bounds
  have hℓ : ∀ x, |responseScore hS ν M u x| ≤ (Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖ * ‖u‖ := by
    intro x
    have h := abs_affScoreAt_le hB0 hB M ((Rat M) u : J → ℝ) x
    rw [Submodule.norm_coe] at h
    refine h.trans ?_
    rw [mul_assoc ((Fintype.card J : ℝ) * (‖M‖ + B))]
    exact mul_le_mul_of_nonneg_left ((Rat M).le_opNorm u) hK0
  have hℓd : ∀ x, |responseScore hS ν M' u x - responseScore hS ν M u x| ≤
      (Fintype.card J : ℝ) * (‖M‖ + B) * ‖(Rat M') - Rat M‖ * ‖u‖ +
        (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖ * ‖u‖ := by
    intro x
    rw [responseScore_sub_responseScore]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · have h := abs_affScoreAt_le hB0 hB M (((Rat M') u : 𝕍) - (Rat M) u : J → ℝ) x
      rw [← Submodule.coe_sub, Submodule.norm_coe, ← sub_apply] at h
      refine h.trans ?_
      rw [mul_assoc ((Fintype.card J : ℝ) * (‖M‖ + B))]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ u) hK0
    · refine (abs_dotJ_le_card_mul _ _).trans ?_
      rw [Submodule.norm_coe]
      calc (Fintype.card J : ℝ) * ‖(Rat M') u‖ * ‖M' - M‖
          ≤ (Fintype.card J : ℝ) * (‖Rat M'‖ * ‖u‖) * ‖M' - M‖ := by
            gcongr
            exact (Rat M').le_opNorm u
        _ = (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖ * ‖u‖ := by ring
  -- the pointwise bound on the integrand
  have hpt : ∀ x, ‖famDens S ν (θr M') x * responseScore hS ν M' u x -
      famDens S ν (θr M) x * responseScore hS ν M u x‖ ≤
      |famDens S ν (θr M') x - famDens S ν (θr M) x| *
          ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖ * ‖u‖) +
        famDens S ν (θr M') x * ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖(Rat M') - Rat M‖ * ‖u‖ +
          (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖ * ‖u‖) := by
    intro x
    have e : famDens S ν (θr M') x * responseScore hS ν M' u x -
        famDens S ν (θr M) x * responseScore hS ν M u x =
        (famDens S ν (θr M') x - famDens S ν (θr M) x) * responseScore hS ν M u x +
          famDens S ν (θr M') x * (responseScore hS ν M' u x - responseScore hS ν M u x) := by
      ring
    rw [e, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hℓ x) (abs_nonneg _)
    · rw [abs_mul, abs_of_nonneg (famDens_nonneg hS ν _ x)]
      exact mul_le_mul_of_nonneg_left (hℓd x) (famDens_nonneg hS ν _ x)
  -- integrate
  have hI1 : Integrable (fun x ↦ |famDens S ν (θr M') x - famDens S ν (θr M) x| *
      ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖ * ‖u‖)) ν :=
    ((integrable_famDens hS ν _).sub (integrable_famDens hS ν _)).abs.mul_const _
  have hI2 : Integrable (fun x ↦ famDens S ν (θr M') x *
      ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖(Rat M') - Rat M‖ * ‖u‖ +
        (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖ * ‖u‖)) ν :=
    (integrable_famDens hS ν _).mul_const _
  have hI12 : Integrable (fun x ↦ |famDens S ν (θr M') x - famDens S ν (θr M) x| *
      ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖ * ‖u‖) +
      famDens S ν (θr M') x * ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖(Rat M') - Rat M‖ * ‖u‖ +
        (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖ * ‖u‖)) ν := hI1.add hI2
  calc ∫ x, ‖famDens S ν (θr M') x * responseScore hS ν M' u x -
        famDens S ν (θr M) x * responseScore hS ν M u x‖ ∂ν
      ≤ ∫ x, |famDens S ν (θr M') x - famDens S ν (θr M) x| *
          ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖ * ‖u‖) +
        famDens S ν (θr M') x * ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖(Rat M') - Rat M‖ * ‖u‖ +
          (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖ * ‖u‖) ∂ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun x ↦ norm_nonneg _) hI12
          (Eventually.of_forall hpt)
    _ = (∫ x, |famDens S ν (θr M') x - famDens S ν (θr M) x| ∂ν) *
          ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖ * ‖u‖) +
        (∫ x, famDens S ν (θr M') x ∂ν) *
          ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖(Rat M') - Rat M‖ * ‖u‖ +
            (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖ * ‖u‖) := by
        rw [integral_add hI1 hI2, integral_mul_const, integral_mul_const]
    _ = _ := by
        rw [integral_famDens hS ν]
        ring

/-- The inverse chart derivative is continuous on the relative interior. -/
theorem continuousOn_inverse_chart :
    ContinuousOn (fun M : J → ℝ ↦ (Rat M))
      (intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)).domRestrict
      (fun M : J → ℝ ↦ (Rat M)) = fun m ↦
        (ContinuousLinearEquiv.symm (CDE ((relintChart hS ν).symm m)) : 𝕍 →L[ℝ] 𝕍) := by
    funext m
    simp only [Set.domRestrict_apply, relintChart_symm_apply]
  rw [e]
  exact (continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS).comp (relintChart hS ν).symm.continuous

/-- **The derivative of the reconstruction density is continuous on the relative interior**: `p` is
`C¹` into `L¹(ν)`. -/
theorem continuousWithinAt_reconstructionDeriv {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ContinuousWithinAt (fun M' : J → ℝ ↦ reconstructionDeriv hS ν M')
      (intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) M := by
  -- constants
  choose Mj hMj using fun j ↦ (hS j).2
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B :=
    ⟨∑ j, |Mj j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j x ↦
      (hMj j x).trans ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j ↦ |Mj j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  -- the total-variation Lipschitz bound near `M`
  obtain ⟨r, hr, C, hC, hCc, hCK, hCr⟩ := exists_compact_convex_nhd hS ν hrel
  obtain ⟨L, hL0, hL⟩ := exists_tv_lipschitz_of_isCompact_convex hS ν hC hCc hCK
  have hMC : M ∈ C := hCr M (intrinsicInterior_subset hrel) (by simp [hr.le])
  -- continuity of `R` within the interior
  have hRc : ContinuousWithinAt (fun M' : J → ℝ ↦ (Rat M'))
      (intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) M :=
    continuousOn_inverse_chart hS ν M hrel
  have hRsub : Tendsto (fun M' : J → ℝ ↦ ‖(Rat M') - Rat M‖)
      (𝓝[intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)] M) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hRc)
    exact this
  have hRn : Tendsto (fun M' : J → ℝ ↦ ‖Rat M'‖)
      (𝓝[intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)] M) (𝓝 ‖Rat M‖) :=
    (continuous_norm.tendsto _).comp hRc
  have hMM : Tendsto (fun M' : J → ℝ ↦ ‖M' - M‖)
      (𝓝[intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)] M) (𝓝 0) := by
    have hc : Continuous fun M' : J → ℝ ↦ ‖M' - M‖ := by fun_prop
    have := (hc.tendsto M).mono_left
      (nhdsWithin_le_nhds (s := intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)))
    simpa using this
  -- the upper bound tends to zero
  have hup : Tendsto (fun M' : J → ℝ ↦ (Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖ * (L * ‖M' - M‖) +
      (Fintype.card J : ℝ) * (‖M‖ + B) * ‖(Rat M') - Rat M‖ +
      (Fintype.card J : ℝ) * ‖Rat M'‖ * ‖M' - M‖)
      (𝓝[intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)] M) (𝓝 0) := by
    have h1 := (hMM.const_mul L).const_mul ((Fintype.card J : ℝ) * (‖M‖ + B) * ‖Rat M‖)
    have h2 := hRsub.const_mul ((Fintype.card J : ℝ) * (‖M‖ + B))
    have h3 := (hRn.const_mul (Fintype.card J : ℝ)).mul hMM
    have := (h1.add h2).add h3
    simpa using this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
  have hball : ∀ᶠ M' in 𝓝[intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)] M,
      M' ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) ∧ ‖M' - M‖ ≤ r := by
    have h2 : ∀ᶠ M' in 𝓝[intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)] M,
        ‖M' - M‖ ≤ r := by
      filter_upwards [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds M hr)] with M' hM'
      rwa [Metric.mem_closedBall, dist_eq_norm] at hM'
    exact eventually_mem_nhdsWithin.and h2
  filter_upwards [hball] with M' ⟨hM'i, hM'r⟩
  have hM'C : M' ∈ C := hCr M' (intrinsicInterior_subset hM'i) hM'r
  refine (norm_reconstructionDeriv_sub_le hS ν hB0 hB M M').trans ?_
  gcongr
  exact hL M hMC M' hM'C

end Laplace.Multi
