/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CubicRemainder
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The tilt map is real-analytic

The weighted tilt `θ ↦ [g e^{−⟨θ,S⟩}] ∈ L¹(ν)` factors through the Banach algebra `A = C(K, ℝ)` on
the compact feature ball `K = closedBall 0 B ⊂ ℝ^J` as
`T_g (exp_A (featureCLM θ))`, where `featureCLM θ = (z ↦ −⟨θ, z⟩)` is linear in `θ` and
`T_g u = [g · (u ∘ S)]` is linear in `u`. Since `exp_A` is analytic (`NormedSpace.exp_analytic`) and
continuous linear maps are analytic, the tilt map is analytic at every `θ`
(`analyticAt_weightL1`, `contDiff_omega_weightL1`), and so are the scalar numerators
`θ ↦ ∫ g e^{−⟨θ,S⟩} dν` (`analyticAt_famNum`) and the normaliser `famZ` (`contDiff_omega_famZ`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Ball

variable (J : Type*) [Fintype J]

/-- The compact feature ball `closedBall 0 B` in `ℝ^J`. -/
abbrev featureBall (B : ℝ) : Set (J → ℝ) := Metric.closedBall (0 : J → ℝ) B

instance compactSpace_featureBall (B : ℝ) : CompactSpace (featureBall J B) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/-- `h ↦ (z ↦ −⟨h, z⟩)` as a linear map into `C(K, ℝ)`. -/
noncomputable def featureLin (B : ℝ) : (J → ℝ) →ₗ[ℝ] C(featureBall J B, ℝ) where
  toFun h := ⟨fun z ↦ -dotJ h (z : J → ℝ), by
    unfold dotJ
    exact (continuous_finsetSum _ fun j _ ↦
      continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)).neg⟩
  map_add' h₁ h₂ := by
    ext z
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, dotJ_add_left]
    ring
  map_smul' c h := by
    ext z
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul, dotJ_smul_left,
      RingHom.id_apply]
    ring

theorem featureLin_apply (B : ℝ) (h : J → ℝ) (z : featureBall J B) :
    featureLin J B h z = -dotJ h (z : J → ℝ) := rfl

theorem exists_bound_featureLin (B : ℝ) :
    ∃ C : ℝ, ∀ h : J → ℝ, ‖featureLin J B h‖ ≤ C * ‖h‖ := by
  refine ⟨(Fintype.card J : ℝ) * |B|, fun h ↦ ?_⟩
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro z
  rw [featureLin_apply, Real.norm_eq_abs, abs_neg]
  have hz : ‖(z : J → ℝ)‖ ≤ |B| := (mem_closedBall_zero_iff.1 z.2).trans (le_abs_self B)
  have hsum : ∑ j, |h j| ≤ (Fintype.card J : ℝ) * ‖h‖ := by
    calc ∑ j, |h j| ≤ ∑ _j : J, ‖h‖ := Finset.sum_le_sum fun j _ ↦ by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm h j
      _ = (Fintype.card J : ℝ) * ‖h‖ := by simp
  calc |dotJ h (z : J → ℝ)| ≤ (∑ j, |h j|) * ‖(z : J → ℝ)‖ := abs_dotJ_le _ _
    _ ≤ ((Fintype.card J : ℝ) * ‖h‖) * |B| :=
        mul_le_mul hsum hz (norm_nonneg _) (by positivity)
    _ = (Fintype.card J : ℝ) * |B| * ‖h‖ := by ring

/-- The feature map `θ ↦ (z ↦ −⟨θ, z⟩)` as a continuous linear map into `C(K, ℝ)`. -/
noncomputable def featureCLM (B : ℝ) : (J → ℝ) →L[ℝ] C(featureBall J B, ℝ) :=
  (featureLin J B).mkContinuousOfExistsBound (exists_bound_featureLin J B)

theorem featureCLM_apply (B : ℝ) (h : J → ℝ) (z : featureBall J B) :
    featureCLM J B h z = -dotJ h (z : J → ℝ) := rfl

/-- The Banach-algebra exponential of `C(K, ℝ)` evaluates pointwise. -/
theorem exp_apply_featureBall (B : ℝ) (u : C(featureBall J B, ℝ)) (z : featureBall J B) :
    NormedSpace.exp u z = Real.exp (u z) := by
  let e : C(featureBall J B, ℝ) →+* ℝ :=
    { toFun := fun v ↦ v z, map_one' := rfl, map_mul' := fun _ _ ↦ rfl, map_zero' := rfl,
      map_add' := fun _ _ ↦ rfl }
  have h := NormedSpace.map_exp e (continuous_eval_const z) u
  rw [Real.exp_eq_exp_ℝ]
  exact h

end Ball

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

section Pullback

variable {B : ℝ} (hB : ∀ j x, |S j x| ≤ B)
include hB

/-- The feature point `S(x)` in the compact feature ball. -/
noncomputable def featPt (x : X) : featureBall J B :=
  ⟨fun j ↦ S j x, by
    have h0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary J) x)
    exact mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg h0).2 fun j ↦ by
      rw [Real.norm_eq_abs]; exact hB j x)⟩

omit [MeasurableSpace X] [Nonempty X] hS in
theorem featPt_coe (x : X) : (featPt hB x : J → ℝ) = fun j ↦ S j x := rfl

omit [Nonempty X] in
theorem measurable_featPt : Measurable (featPt hB) :=
  Measurable.subtype_mk (measurable_pi_iff.2 fun j ↦ (hS j).1)

variable {g : X → ℝ} (hg : Bdd g)
include hg

omit [Nonempty X] in
theorem integrable_pullback (u : C(featureBall J B, ℝ)) :
    Integrable (fun x ↦ u (featPt hB x) * g x) ν :=
  (integrable_of_bdd_prob ν hg).bdd_mul
    (u.continuous.measurable.comp (measurable_featPt hS hB)).aestronglyMeasurable
    (Eventually.of_forall fun _ ↦ ContinuousMap.norm_coe_le_norm u _)

/-- The weighted pullback `u ↦ [g · (u ∘ S)]` as a linear map `C(K, ℝ) → L¹(ν)`. -/
noncomputable def pullbackLin : C(featureBall J B, ℝ) →ₗ[ℝ] (X →₁[ν] ℝ) where
  toFun u := (integrable_pullback hS ν hB hg u).toL1 _
  map_add' u v := by
    rw [← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff]
    exact Eventually.of_forall fun x ↦ by
      simp only [ContinuousMap.add_apply, Pi.add_apply]
      ring
  map_smul' c u := by
    rw [RingHom.id_apply, ← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]
    exact Eventually.of_forall fun x ↦ by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      ring

omit [Nonempty X] in
theorem exists_bound_pullbackLin :
    ∃ C : ℝ, ∀ u : C(featureBall J B, ℝ), ‖pullbackLin hS ν hB hg u‖ ≤ C * ‖u‖ := by
  refine ⟨∫ x, |g x| ∂ν, fun u ↦ ?_⟩
  change ‖(integrable_pullback hS ν hB hg u).toL1 _‖ ≤ _
  rw [L1.norm_of_fun_eq_integral_norm, ← integral_mul_const]
  refine integral_mono (integrable_pullback hS ν hB hg u).norm
    ((integrable_of_bdd_prob ν hg).abs.mul_const _) fun x ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm u _) (abs_nonneg _)

/-- The weighted pullback `C(K, ℝ) →L L¹(ν)`. -/
noncomputable def pullbackCLM : C(featureBall J B, ℝ) →L[ℝ] (X →₁[ν] ℝ) :=
  (pullbackLin hS ν hB hg).mkContinuousOfExistsBound (exists_bound_pullbackLin hS ν hB hg)

omit [Nonempty X] in
theorem pullbackCLM_apply (u : C(featureBall J B, ℝ)) :
    pullbackCLM hS ν hB hg u = (integrable_pullback hS ν hB hg u).toL1 _ := rfl

omit [Nonempty X] in
/-- **The tilt map through the Banach algebra**: `weightL1 θ = T_g (exp_A (featureCLM θ))`. -/
theorem weightL1_eq_pullback_exp (θ : J → ℝ) :
    weightL1 hS ν hg θ = pullbackCLM hS ν hB hg (NormedSpace.exp (featureCLM J B θ)) := by
  rw [pullbackCLM_apply]
  unfold weightL1
  rw [Integrable.toL1_eq_toL1_iff]
  refine Eventually.of_forall fun x ↦ ?_
  beta_reduce
  rw [exp_apply_featureBall, featureCLM_apply, featPt_coe]
  unfold famWeight dirLoss dotJ
  ring

omit [Nonempty X] in
/-- **The tilt map is analytic** at every natural parameter. -/
theorem analyticAt_weightL1 (θ : J → ℝ) : AnalyticAt ℝ (weightL1 hS ν hg) θ := by
  have e : weightL1 hS ν hg =
      fun θ ↦ pullbackCLM hS ν hB hg (NormedSpace.exp (featureCLM J B θ)) :=
    funext fun θ ↦ weightL1_eq_pullback_exp hS ν hB hg θ
  rw [e]
  exact ((pullbackCLM hS ν hB hg).analyticAt _).comp
    ((NormedSpace.exp_analytic (𝕂 := ℝ) _).comp ((featureCLM J B).analyticAt θ))

end Pullback

section Omega

variable {g : X → ℝ} (hg : Bdd g)
include hg

omit [Nonempty X] in
/-- The tilt map is `C^ω`. -/
theorem contDiff_omega_weightL1 : ContDiff ℝ ω (weightL1 hS ν hg) := by
  obtain ⟨B, _, hB⟩ := exists_feature_bound hS
  exact contDiff_omega_iff_analyticOnNhd.2 fun θ _ ↦ analyticAt_weightL1 hS ν hB hg θ

omit [Nonempty X] [Nonempty J] in
/-- The scalar numerator is the integral of the tilt map. -/
theorem famNum_eq_integralCLM_weightL1 (θ : J → ℝ) :
    famNum S ν g θ = L1.integralCLM (weightL1 hS ν hg θ) := by
  rw [← L1.integral_eq, L1.integral_eq_integral]
  unfold famNum
  exact integral_congr_ae (Integrable.coeFn_toL1 _).symm

omit [Nonempty X] in
/-- **The numerators `θ ↦ ∫ g e^{−⟨θ,S⟩} dν` are analytic.** -/
theorem analyticAt_famNum (θ : J → ℝ) : AnalyticAt ℝ (famNum S ν g) θ := by
  have e : famNum S ν g = fun θ ↦ L1.integralCLM (weightL1 hS ν hg θ) :=
    funext fun θ ↦ famNum_eq_integralCLM_weightL1 hS ν hg θ
  rw [e]
  obtain ⟨B, _, hB⟩ := exists_feature_bound hS
  exact ((L1.integralCLM : (X →₁[ν] ℝ) →L[ℝ] ℝ).analyticAt _).comp
    (analyticAt_weightL1 hS ν hB hg θ)

omit [Nonempty X] in
theorem contDiff_omega_famNum : ContDiff ℝ ω (famNum S ν g) :=
  contDiff_omega_iff_analyticOnNhd.2 fun θ _ ↦ analyticAt_famNum hS ν hg θ

omit [Nonempty X] hg in
/-- **The normaliser is analytic.** -/
theorem contDiff_omega_famZ : ContDiff ℝ ω (famZ S ν) := by
  rw [famZ_eq_famNum ν]
  exact contDiff_omega_famNum hS ν (Bdd.const 1)

end Omega

end Laplace.Multi
