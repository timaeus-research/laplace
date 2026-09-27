/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseInformationPythagoras
import Laplace.Multi.ResponseNoiseCalibration
import Laplace.Multi.IntrinsicLegendre
import Laplace.Multi.ResponsePullbackVariation
import Mathlib.Analysis.Convex.Deriv

/-!
# The information objective: Fisher Hessian and the response as its critical point

For a data law `ρ_g` the **information objective** `K_g(θ) = KL(ρ_g ‖ P_θ)` (`informationObjective`)
is, up to a constant, `⟨θ, E_{ρ_g} S⟩ + log Z(θ)`. Its Fréchet derivative is the moment mismatch
`DK_g(θ)[u] = ⟨u, E_{ρ_g}S − m(θ)⟩` (`hasFDerivAt_informationObjective`), its Hessian is the
Fisher form `D²K_g(θ)[u,v] = Cov_{P_θ}(⟨u,S⟩,⟨v,S⟩)` (`fderiv_fderiv_informationObjective`, on the
direction space `fisherInner`), and on the direction space its differential vanishes **exactly at
the response** `θ = Φ(g)` (`fderiv_informationObjective_eq_zero_iff`). Along every nonconstant
natural line the objective is strictly convex (`strictConvexOn_informationObjective_line`): the
Fisher metric of programme D is the Hessian of the model-fitting objective, and the response is its
unique nondegenerate critical point.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Hessian

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean map derivative. -/
local notation "Dmean" => meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable (S) in
omit [Nonempty X] [Nonempty J] hS in
/-- **The information objective** `K_g(θ) = KL(ρ_g ‖ P_θ)`. -/
noncomputable def informationObjective (g : X → ℝ) (θ : J → ℝ) : ℝ :=
  (klDiv (ν.tilted g) (Pfam θ)).toReal

omit [Nonempty J] in
theorem informationObjective_eq {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    informationObjective S ν g θ =
      ∫ x, g x ∂ν.tilted g - Real.log (∫ x, Real.exp (g x) ∂ν) + dotJ θ (tiltedMean S ν g) +
        Real.log (famZ S ν θ) :=
  toReal_klDiv_tilted_model hS ν hg θ

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS in
theorem dotCLM_sub (a b : J → ℝ) : dotCLM (a - b) = dotCLM a - dotCLM b := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [dotCLM_apply, _root_.sub_apply, (isLinearMap_dotJ v).map_sub]

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS in
theorem dotCLM_eq_zero_iff (w : J → ℝ) : dotCLM w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun T : (J → ℝ) →L[ℝ] ℝ ↦ T w) h
    simp only [dotCLM_apply, _root_.zero_apply, dotJ] at h1
    have h2 : ∀ j ∈ Finset.univ, w j * w j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ mul_self_nonneg (w j)).1 h1
    funext j
    exact mul_self_eq_zero.1 (h2 j (Finset.mem_univ j))
  · rintro rfl
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [dotCLM_apply, dotJ]

omit [Nonempty J] in
/-- **The differential of the information objective is the moment mismatch**:
`DK_g(θ)[u] = ⟨u, E_{ρ_g} S − m(θ)⟩`. -/
theorem hasFDerivAt_informationObjective {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    HasFDerivAt (informationObjective S ν g) (dotCLM (tiltedMean S ν g - mean θ)) θ := by
  have e : informationObjective S ν g = fun θ ↦
      (∫ x, g x ∂ν.tilted g - Real.log (∫ x, Real.exp (g x) ∂ν)) + dotCLM (tiltedMean S ν g) θ +
        Real.log (famZ S ν θ) := by
    funext θ
    rw [informationObjective_eq hS ν hg, dotCLM_apply]
  rw [e]
  have h1 : HasFDerivAt (fun θ : J → ℝ ↦ dotCLM (tiltedMean S ν g) θ)
      (dotCLM (tiltedMean S ν g)) θ := (dotCLM (tiltedMean S ν g)).hasFDerivAt
  have h2 := (hasFDerivAt_famZ hS ν θ).log (famZ_pos hS ν θ).ne'
  refine (((hasFDerivAt_const _ θ).add h1).add h2).congr_fderiv ?_
  rw [smul_smul, show (famZ S ν θ)⁻¹ * (-famZ S ν θ) = -1 by
    rw [mul_neg, inv_mul_cancel₀ (famZ_pos hS ν θ).ne'], neg_one_smul, zero_add,
    famMean_eq_meanMap hS ν, dotCLM_sub, sub_eq_add_neg]

omit [Nonempty J] in
/-- The differential as a function of the base point. -/
theorem fderiv_informationObjective {g : X → ℝ} (hg : Bdd g) :
    fderiv ℝ (informationObjective S ν g) = fun θ ↦ dotCLM (tiltedMean S ν g - mean θ) :=
  funext fun θ ↦ (hasFDerivAt_informationObjective hS ν hg θ).fderiv

omit [Nonempty J] in
/-- **The Hessian of the information objective is the Fisher form**:
`D²K_g(θ)[u,v] = Cov_{P_θ}(⟨u,S⟩, ⟨v,S⟩)`. -/
theorem fderiv_fderiv_informationObjective {g : X → ℝ} (hg : Bdd g) (θ u v : J → ℝ) :
    fderiv ℝ (fderiv ℝ (informationObjective S ν g)) θ u v =
      lawCov (Pfam θ) (dirLoss S u) (dirLoss S v) := by
  rw [fderiv_informationObjective hS ν hg]
  have e : (fun θ ↦ dotCLM (tiltedMean S ν g - mean θ)) =
      fun θ ↦ dotCLMlin (tiltedMean S ν g - mean θ) := funext fun θ ↦ (dotCLMlin_apply _).symm
  rw [e]
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hm := (hasStrictFDerivAt_meanMap measurable_const (integrable_const 1)
    (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos θ).hasFDerivAt
  have h0' := dotCLMlin.hasFDerivAt.comp θ ((hasFDerivAt_const (tiltedMean S ν g) θ).sub hm)
  have h : HasFDerivAt (fun θ ↦ dotCLMlin (tiltedMean S ν g - mean θ))
      (dotCLMlin.comp ((0 : (J → ℝ) →L[ℝ] (J → ℝ)) - Dmean θ)) θ := h0'
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, map_neg, _root_.neg_apply, dotCLMlin_apply,
    dotCLM_apply]
  rw [dotJ_meanMapDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ v u, priorCov_eq_lawCov_familyMeasure hS ν, neg_neg]
  have := isProbabilityMeasure_family hS ν θ
  exact lawCov_comm _ _ _

omit [Nonempty J] in
/-- On the direction space the Hessian is the Fisher inner product. -/
theorem fderiv_fderiv_informationObjective_dirSpan {g : X → ℝ} (hg : Bdd g) (θ u v : 𝕍) :
    fderiv ℝ (fderiv ℝ (informationObjective S ν g)) (θ : J → ℝ) (u : J → ℝ) (v : J → ℝ) =
      fisherInner S ν θ u v :=
  fderiv_fderiv_informationObjective hS ν hg _ _ _

/-- **The response is the unique critical point of the information objective** on the direction
space: `DK_g(θ) = 0 ↔ θ = Φ(g)`. -/
theorem fderiv_informationObjective_eq_zero_iff {g : X → ℝ} (hg : Bdd g) (θ : 𝕍) :
    fderiv ℝ (informationObjective S ν g) (θ : J → ℝ) = 0 ↔ θ = responseOf hS ν g := by
  rw [fderiv_informationObjective hS ν hg]
  simp only
  rw [dotCLM_eq_zero_iff, sub_eq_zero, ← responseOf_eq_iff_tiltedMean_eq_meanMap hS ν hg θ]
  exact eq_comm

omit [Nonempty J] in
/-- The objective along a natural line has derivative the moment mismatch in the direction. -/
theorem hasDerivAt_informationObjective_line {g : X → ℝ} (hg : Bdd g) (θ u : J → ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ informationObjective S ν g (θ + t • u))
      (dotJ u (tiltedMean S ν g - mean (θ + t • u))) t := by
  have hline : HasDerivAt (fun t : ℝ ↦ θ + t • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add θ
  have h := (hasFDerivAt_informationObjective hS ν hg (θ + t • u)).comp_hasDerivAt t hline
  rw [dotCLM_apply] at h
  exact h

omit [Nonempty J] in
/-- The second derivative along a natural line is the Fisher variance of the direction. -/
theorem hasDerivAt_deriv_informationObjective_line {g : X → ℝ} (hg : Bdd g) (θ u : J → ℝ)
    (t : ℝ) :
    HasDerivAt (deriv fun t : ℝ ↦ informationObjective S ν g (θ + t • u))
      (fisherVar S ν (θ + t • u) u) t := by
  have e : (deriv fun t : ℝ ↦ informationObjective S ν g (θ + t • u)) =
      fun t ↦ dotJ u (tiltedMean S ν g - mean (θ + t • u)) :=
    funext fun t ↦ (hasDerivAt_informationObjective_line hS ν hg θ u t).deriv
  rw [e]
  have hline : HasDerivAt (fun t : ℝ ↦ θ + t • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add θ
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hm := ((hasStrictFDerivAt_meanMap measurable_const (integrable_const 1)
    (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos
    (θ + t • u)).hasFDerivAt).comp_hasDerivAt t hline
  have h := (hasDerivAt_dotJ (hasDerivAt_const t u)
    ((hasDerivAt_const t (tiltedMean S ν g)).sub hm))
  refine h.congr_deriv ?_
  rw [dotJ_zero_left, zero_add, (isLinearMap_dotJ u).map_sub, dotJ_zero_right, zero_sub,
    dotJ_meanMapDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS _ u u, priorCov_eq_lawCov_familyMeasure hS ν, neg_neg]
  rfl

/-- **Strict convexity along natural lines of the direction space**: for `u ∈ W`, `u ≠ 0`, the
information objective is strictly convex along `t ↦ θ + t u`. -/
theorem strictConvexOn_informationObjective_line {g : X → ℝ} (hg : Bdd g) (θ : 𝕍) {u : 𝕍}
    (hu : u ≠ 0) :
    StrictConvexOn ℝ univ
      fun t : ℝ ↦ informationObjective S ν g ((θ : J → ℝ) + t • (u : J → ℝ)) := by
  refine strictConvexOn_of_deriv2_pos convex_univ ?_ fun t _ ↦ ?_
  · exact (continuous_iff_continuousAt.2 fun t ↦
      (hasDerivAt_informationObjective_line hS ν hg _ _ t).continuousAt).continuousOn
  · change 0 < deriv
      (deriv fun t : ℝ ↦ informationObjective S ν g ((θ : J → ℝ) + t • (u : J → ℝ))) t
    rw [(hasDerivAt_deriv_informationObjective_line hS ν hg _ _ t).deriv]
    have := fisherVar_pos_of_ne_zero hS ν (θ + t • u) hu
    rwa [Submodule.coe_add, Submodule.coe_smul] at this

end Hessian

end Laplace.Multi
