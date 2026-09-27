/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FlatC1Paths
import Laplace.Multi.ChartContinuity
import Laplace.Multi.ResponseTransport
import Laplace.Multi.CovarianceFrechet
import Laplace.Multi.FisherCauchyRealisation
import Laplace.Multi.InverseStability

/-!
# Local metric control of the response map by covariance coercivity

On a convex set `U` of interior means where the family covariance is coercive on the direction
space, `λ ⟨w,w⟩ ≤ Var_{P_{θ(M)}}⟨w,S⟩`, the response `θ(M) = m⁻¹(M)` is `λ^{-1/2}`-Lipschitz from
the Euclidean mean geometry into the intrinsic Fisher geometry:

`d_F(θ(M₀), θ(M₁)) ≤ ‖M₁ − M₀‖₂ / √λ`.

The proof pulls back the straight mean segment `M₀ + t (M₁ − M₀)` through the inverse chart. Its
velocity `θ'_t = (Dm(θ_t))⁻¹ Δ` has Fisher norm squared `−⟨θ'_t, Dm(θ_t) θ'_t⟩ = −⟨θ'_t, Δ⟩`, and
Cauchy–Schwarz with coercivity gives `|θ'_t|²_F ≤ |θ'_t|_F ‖Δ‖₂/√λ`. A clamped smooth step turns the
segment into a globally `C¹` path so that the intrinsic distance bound `d_F ≤ ∫ |θ'|_F` applies.
This is the **local Lipschitz continuity of the response map in the mean**, the first half of the
Hellinger-to-Fisher local Lipschitz continuity of the response on the data manifold (the second
half, `‖m(Q) − m(R)‖₂ ≤ 2B H(Q,R)`, is the boundedness of the statistics).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Clamp

/-- The clamp of `ℝ` onto `[0, 1]`. -/
noncomputable def clampArg (s : ℝ) : ℝ := max 0 (min 1 s)

/-- The smooth step, constant outside `[0, 1]`. -/
noncomputable def clampStep (s : ℝ) : ℝ := smoothStep (clampArg s)

/-- Its derivative (zero outside `[0, 1]`). -/
noncomputable def clampStepDeriv (s : ℝ) : ℝ := smoothStepDeriv (clampArg s)

theorem clampArg_of_le {s : ℝ} (h : s ≤ 0) : clampArg s = 0 := by
  unfold clampArg
  rw [min_eq_right (h.trans zero_le_one), max_eq_left h]

theorem clampArg_of_ge {s : ℝ} (h : 1 ≤ s) : clampArg s = 1 := by
  unfold clampArg
  rw [min_eq_left h, max_eq_right zero_le_one]

theorem clampArg_of_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : clampArg s = s := by
  unfold clampArg
  rw [min_eq_right h1, max_eq_right h0]

theorem clampArg_mem_Icc (s : ℝ) : clampArg s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clampStep_zero : clampStep 0 = 0 := by
  rw [clampStep, clampArg_of_mem le_rfl zero_le_one, smoothStep_zero]

theorem clampStep_one : clampStep 1 = 1 := by
  rw [clampStep, clampArg_of_mem zero_le_one le_rfl, smoothStep_one]

theorem clampStep_mem_Icc (s : ℝ) : clampStep s ∈ Icc (0 : ℝ) 1 :=
  smoothStep_mem_Icc (clampArg_mem_Icc s).1 (clampArg_mem_Icc s).2

theorem continuous_clampArg : Continuous clampArg :=
  continuous_const.max (continuous_const.min continuous_id)

theorem continuous_clampStepDeriv : Continuous clampStepDeriv :=
  continuous_smoothStepDeriv.comp continuous_clampArg

theorem clampStepDeriv_nonneg (s : ℝ) : 0 ≤ clampStepDeriv s :=
  smoothStepDeriv_nonneg (clampArg_mem_Icc s).1 (clampArg_mem_Icc s).2

theorem hasDerivAt_clampStep (s : ℝ) : HasDerivAt clampStep (clampStepDeriv s) s := by
  have h1 : HasDerivWithinAt clampStep (clampStepDeriv s) (Iic 0) s := by
    by_cases hs : s ∈ closure (Iic (0 : ℝ))
    · rw [closure_Iic] at hs
      have e : clampStepDeriv s = 0 := by
        rw [clampStepDeriv, clampArg_of_le hs, smoothStepDeriv_zero]
      rw [e]
      refine (hasDerivWithinAt_const s (Iic (0 : ℝ)) (0 : ℝ)).congr (fun t ht ↦ ?_) ?_
      · rw [clampStep, clampArg_of_le ht, smoothStep_zero]
      · rw [clampStep, clampArg_of_le hs, smoothStep_zero]
    · exact HasFDerivWithinAt.of_notMem_closure hs
  have h2 : HasDerivWithinAt clampStep (clampStepDeriv s) (Icc 0 1) s := by
    by_cases hs : s ∈ closure (Icc (0 : ℝ) 1)
    · rw [closure_Icc] at hs
      have e : clampStepDeriv s = smoothStepDeriv s := by
        rw [clampStepDeriv, clampArg_of_mem hs.1 hs.2]
      rw [e]
      refine (hasDerivAt_smoothStep s).hasDerivWithinAt.congr (fun t ht ↦ ?_) ?_
      · rw [clampStep, clampArg_of_mem ht.1 ht.2]
      · rw [clampStep, clampArg_of_mem hs.1 hs.2]
    · exact HasFDerivWithinAt.of_notMem_closure hs
  have h3 : HasDerivWithinAt clampStep (clampStepDeriv s) (Ici 1) s := by
    by_cases hs : s ∈ closure (Ici (1 : ℝ))
    · rw [closure_Ici] at hs
      have e : clampStepDeriv s = 0 := by
        rw [clampStepDeriv, clampArg_of_ge hs, smoothStepDeriv_one]
      rw [e]
      refine (hasDerivWithinAt_const s (Ici (1 : ℝ)) (1 : ℝ)).congr (fun t ht ↦ ?_) ?_
      · rw [clampStep, clampArg_of_ge ht, smoothStep_one]
      · rw [clampStep, clampArg_of_ge hs, smoothStep_one]
    · exact HasFDerivWithinAt.of_notMem_closure hs
  have h := h1.union (h2.union h3)
  rw [Icc_union_Ici_eq_Ici zero_le_one, Iic_union_Ici] at h
  exact hasDerivWithinAt_univ.1 h

theorem integral_clampStepDeriv : ∫ s in (0 : ℝ)..1, clampStepDeriv s = 1 := by
  have e : ∫ s in (0 : ℝ)..1, clampStepDeriv s = ∫ s in (0 : ℝ)..1, smoothStepDeriv s := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le zero_le_one] at hs
    simp only [clampStepDeriv, clampArg_of_mem hs.1 hs.2]
  rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_smoothStep x)
    (continuous_smoothStepDeriv.intervalIntegrable _ _), smoothStep_one, smoothStep_zero, sub_zero]

end Clamp

section Metric

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless mean. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- **The Fisher norm of a pulled-back mean velocity** is controlled by coercivity:
`|(Dm(θ))⁻¹ v|_F ≤ ‖v‖₂ / √λ` whenever `λ ⟨w,w⟩ ≤ Var_{P_θ}⟨w,S⟩` for all `w`. -/
theorem fisherNorm_symm_le {lam : ℝ} (hlam : 0 < lam) (θ : 𝕍)
    (hcoer : ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θ : J → ℝ) w) (v : 𝕍) :
    fisherNorm S ν (θ : J → ℝ) ((CDE θ).symm v : J → ℝ) ≤ √(dotJ (v : J → ℝ) v) / √lam := by
  obtain ⟨w, hw⟩ : ∃ w : J → ℝ, w = ((CDE θ).symm v : J → ℝ) := ⟨_, rfl⟩
  rw [← hw]
  have hF : fisherVar S ν (θ : J → ℝ) w = -dotJ w v := by
    rw [fisherVar_eq_neg_dotJ hS ν, hw]
    congr 2
    have : meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ : J → ℝ)
        ((CDE θ).symm v : J → ℝ) =
        (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
          θ ((CDE θ).symm v) : J → ℝ) := rfl
    rw [this, ← ContinuousLinearMap.coe_coe (chartDeriv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS θ), ← coe_chartDerivEquiv,
      ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  have hF0 : 0 ≤ fisherVar S ν (θ : J → ℝ) w := fisherVar_nonneg hS ν _ _
  have hcs := sq_dotJ_le w (v : J → ℝ)
  have hww := hcoer w
  have hvv : 0 ≤ dotJ (v : J → ℝ) v := by
    unfold dotJ
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  -- `F² = ⟨w,v⟩² ≤ ⟨w,w⟩⟨v,v⟩ ≤ (F/λ)⟨v,v⟩`
  have key : lam * fisherVar S ν (θ : J → ℝ) w ^ 2 ≤
      fisherVar S ν (θ : J → ℝ) w * dotJ (v : J → ℝ) v := by
    have h1 : fisherVar S ν (θ : J → ℝ) w ^ 2 = dotJ w v ^ 2 := by rw [hF]; ring
    rw [h1]
    calc lam * dotJ w (v : J → ℝ) ^ 2 ≤ lam * (dotJ w w * dotJ (v : J → ℝ) v) :=
          mul_le_mul_of_nonneg_left hcs hlam.le
      _ = (lam * dotJ w w) * dotJ (v : J → ℝ) v := by ring
      _ ≤ fisherVar S ν (θ : J → ℝ) w * dotJ (v : J → ℝ) v :=
          mul_le_mul_of_nonneg_right hww hvv
  rw [fisherNorm, ← Real.sqrt_div' _ hlam.le]
  refine Real.sqrt_le_sqrt ?_
  rcases hF0.lt_or_eq with hpos | hzero
  · rw [le_div_iff₀ hlam]
    have key' : fisherVar S ν (θ : J → ℝ) w * (lam * fisherVar S ν (θ : J → ℝ) w) ≤
        fisherVar S ν (θ : J → ℝ) w * dotJ (v : J → ℝ) v := by
      have e : fisherVar S ν (θ : J → ℝ) w * (lam * fisherVar S ν (θ : J → ℝ) w) =
          lam * fisherVar S ν (θ : J → ℝ) w ^ 2 := by ring
      rw [e]
      exact key
    have := le_of_mul_le_mul_left key' hpos
    linarith
  · rw [← hzero]
    positivity

variable {U : Set (J → ℝ)} (hU : Convex ℝ U)
  (hUint : U ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hU hUint

/-- **Local metric control of the response**: covariance coercivity on a convex set of interior
means gives `d_F(θ(M₀), θ(M₁)) ≤ ‖M₁ − M₀‖₂ / √λ`. -/
theorem fisherDist_responseTheta_le {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    {M₀ M₁ : J → ℝ} (h₀ : M₀ ∈ U) (h₁ : M₁ ∈ U) :
    fisherDist S ν (θr M₀) (θr M₁) ≤ √(dotJ (M₁ - M₀) (M₁ - M₀)) / √lam := by
  have hmb : ∀ M ∈ U, M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := fun M hM ↦
    intrinsicInterior_subset (hUint hM)
  have hΔ : M₁ - M₀ ∈ 𝕍 := sub_mem_dirSpan_of_mem_momentBody' hS ν (hmb _ h₀) (hmb _ h₁)
  obtain ⟨v, hvdef⟩ : ∃ v : 𝕍, v = ⟨M₁ - M₀, hΔ⟩ := ⟨_, rfl⟩
  -- the mean segment and its pull-back
  obtain ⟨Mt, hMt⟩ : ∃ Mt : ℝ → J → ℝ, Mt = fun s ↦ M₀ + clampStep s • (M₁ - M₀) := ⟨_, rfl⟩
  have hMtU : ∀ s, Mt s ∈ U := fun s ↦ by
    rw [hMt]
    have h1' : M₀ + (M₁ - M₀) ∈ U := by rwa [add_sub_cancel]
    exact hU.add_smul_mem h₀ h1' (clampStep_mem_Icc s)
  have hMtV : ∀ s, Mt s - m₀ ∈ 𝕍 := fun s ↦
    sub_mem_dirSpan_of_mem_momentBody' hS ν (meanMap_mem_momentBody measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS 0) (hmb _ (hMtU s))
  have hMtc : Continuous Mt := by
    rw [hMt]
    exact continuous_const.add ((continuous_smoothStep.comp continuous_clampArg).smul
      continuous_const)
  have hθc : Continuous fun s ↦ θr (Mt s) := by
    rw [← continuousOn_univ]
    exact continuousOn_responseTheta_path hS ν hMtV (fun s _ ↦ hUint (hMtU s)) hMtc.continuousOn
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ → 𝕍, η' = fun s ↦ clampStepDeriv s • (CDE (θr (Mt s))).symm v :=
    ⟨_, rfl⟩
  have hd : ∀ s, HasDerivAt (fun s ↦ θr (Mt s)) (η' s) s := fun s ↦ by
    have hstrict := hasStrictFDerivAt_responseTheta_add hS ν (hUint (hMtU s))
    obtain ⟨z, hz⟩ : ∃ z : ℝ → 𝕍, z = fun s' ↦ clampStep s' • v - clampStep s • v := ⟨_, rfl⟩
    have hz0 : z s = 0 := by rw [hz]; simp
    have hzd : HasDerivAt z (clampStepDeriv s • v) s := by
      rw [hz]
      exact ((hasDerivAt_clampStep s).smul_const v).sub_const _
    have hF : HasFDerivAt (fun z : 𝕍 ↦ θr (Mt s + (z : J → ℝ)))
        ((CDE (θr (Mt s))).symm : 𝕍 →L[ℝ] 𝕍) (z s) := by
      rw [hz0]
      exact hstrict.hasFDerivAt
    have hcomp := hF.comp_hasDerivAt s hzd
    refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun s' ↦ ?_) |>.congr_deriv ?_
    · simp only [Function.comp_def, hz, hMt, hvdef, Submodule.coe_sub, Submodule.coe_smul]
      congr 1
      abel
    · rw [hη', map_smul]
      rfl
  have hd' : Continuous η' := by
    rw [hη']
    exact continuous_clampStepDeriv.smul
      (((continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS).comp hθc).clm_apply continuous_const)
  have h0 : θr (Mt 0) = θr M₀ := by rw [hMt]; simp [clampStep_zero]
  have h1 : θr (Mt 1) = θr M₁ := by rw [hMt]; simp [clampStep_one]
  have hle := fisherDist_le_integral hS ν (η := fun s ↦ (θr (Mt s) : J → ℝ))
    (η' := fun s ↦ (η' s : J → ℝ)) (fun s ↦ (θr (Mt s)).2)
    (fun s ↦ (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt s (hd s))
    (continuous_subtype_val.comp hd') zero_le_one
  have e0 : (⟨(θr (Mt 0) : J → ℝ), (θr (Mt 0)).2⟩ : 𝕍) = θr M₀ := by
    rw [← h0]
  have e1 : (⟨(θr (Mt 1) : J → ℝ), (θr (Mt 1)).2⟩ : 𝕍) = θr M₁ := by
    rw [← h1]
  rw [e0, e1] at hle
  refine hle.trans ?_
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, fisherNorm S ν (θr (Mt s) : J → ℝ) (η' s : J → ℝ) ≤
      clampStepDeriv s * (√(dotJ (M₁ - M₀) (M₁ - M₀)) / √lam) := fun s _ ↦ by
    rw [hη']
    simp only [Submodule.coe_smul]
    rw [fisherNorm_smul hS ν, abs_of_nonneg (clampStepDeriv_nonneg s)]
    refine mul_le_mul_of_nonneg_left ?_ (clampStepDeriv_nonneg s)
    have := fisherNorm_symm_le hS ν hlam (θr (Mt s)) (hcoer _ (hMtU s)) v
    have hvc : (v : J → ℝ) = M₁ - M₀ := by rw [hvdef]
    rwa [hvc] at this
  calc ∫ s in (0 : ℝ)..1, fisherNorm S ν (θr (Mt s) : J → ℝ) (η' s : J → ℝ)
      ≤ ∫ s in (0 : ℝ)..1, clampStepDeriv s * (√(dotJ (M₁ - M₀) (M₁ - M₀)) / √lam) :=
        intervalIntegral.integral_mono_on zero_le_one
          ((continuous_fisherNorm_comp hS ν (continuous_subtype_val.comp hθc)
            (continuous_subtype_val.comp hd')).intervalIntegrable _ _)
          ((continuous_clampStepDeriv.mul continuous_const).intervalIntegrable _ _) hpt
    _ = √(dotJ (M₁ - M₀) (M₁ - M₀)) / √lam := by
        rw [intervalIntegral.integral_mul_const, integral_clampStepDeriv, one_mul]

end Metric

end Laplace.Multi
