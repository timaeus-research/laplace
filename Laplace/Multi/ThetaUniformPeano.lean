/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.UniformPeano
import Laplace.Multi.ThetaPeano
import Laplace.Multi.GlobalChart

/-!
# The compact-uniform second-order expansion of the natural coordinate

The natural coordinate `θ = (relintChart)⁻¹` is `C²` on the relative interior of the moment body:
its derivative field is `R_M = −Σ_M⁻¹`, and the derivative of `R` at `M` is `w ↦ −R_M T_{θ(M)}(R_M
w, ·) R_M` where `T` is the third-cumulant operator, which is continuous in `θ`
(`continuous_thirdOp`). The generic compact-uniform Peano lemma therefore gives, on every compact
convex set `C` in the relative interior (transported to the direction subspace as `C' = {z : m₀ +
z ∈ C}`):

`‖θ(M') − θ(M) − R_M(M' − M) + ½ R_M T(R_M(M'−M), R_M(M'−M))‖ ≤ ε ‖M' − M‖²`

for `M, M' ∈ C` with `‖M' − M‖ ≤ δ(ε)` (`uniform_responseTheta_peano`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section ThirdOp

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty J] in
/-- The response of a bounded observable is continuous in the natural coordinates. -/
theorem continuous_integral_family {φ : X → ℝ} (hφ : Bdd φ) :
    Continuous fun θ : J → ℝ ↦ ∫ x, φ x ∂(Pfam θ) :=
  continuous_iff_continuousAt.2 fun θ ↦ (hasFDerivAt_integral_family hS ν hφ θ).continuousAt

/-- **The third-cumulant operator is continuous in the natural coordinates.** -/
theorem continuous_thirdOp : Continuous (thirdOp hS ν) := by
  refine continuous_clm_apply.2 fun η ↦ continuous_clm_apply.2 fun v ↦ ?_
  refine continuous_induced_rng.2 ?_
  change Continuous (fun θ : 𝕍 ↦ ((thirdOp hS ν θ η v : 𝕍) : J → ℝ))
  have e : (fun θ : 𝕍 ↦ ((thirdOp hS ν θ η v : 𝕍) : J → ℝ)) =
      fun θ : 𝕍 ↦ thirdVec S ν (θ : J → ℝ) η v :=
    funext fun θ ↦ thirdOp_coe_apply hS ν θ η v
  rw [e]
  refine continuous_pi fun j ↦ ?_
  have e2 : (fun θ : 𝕍 ↦ thirdVec S ν (θ : J → ℝ) η v j) = fun θ : 𝕍 ↦
      (∫ x, S j x * dirLoss S v x * dirLoss S η x ∂(Pfam θ)) -
        (∫ x, S j x * dirLoss S v x ∂(Pfam θ)) * (∫ x, dirLoss S η x ∂(Pfam θ)) -
        (∫ x, S j x * dirLoss S η x ∂(Pfam θ)) * (∫ x, dirLoss S v x ∂(Pfam θ)) -
        (∫ x, dirLoss S v x * dirLoss S η x ∂(Pfam θ)) * (∫ x, S j x ∂(Pfam θ)) +
        2 * ((∫ x, S j x ∂(Pfam θ)) * (∫ x, dirLoss S v x ∂(Pfam θ)) *
          ∫ x, dirLoss S η x ∂(Pfam θ)) := funext fun θ ↦ by
    have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
    exact thirdCentral_eq _ (hS j) (bdd_dirLoss hS _) (bdd_dirLoss hS _)
  rw [e2]
  have hc : ∀ φ : X → ℝ, Bdd φ → Continuous fun θ : 𝕍 ↦ ∫ x, φ x ∂(Pfam θ) := fun φ hφ ↦
    (continuous_integral_family hS ν hφ).comp continuous_subtype_val
  have h1 := hc _ ((hS j).mul (bdd_dirLoss hS v) |>.mul (bdd_dirLoss hS η))
  have h2 := hc _ ((hS j).mul (bdd_dirLoss hS v))
  have h3 := hc _ (bdd_dirLoss hS η)
  have h4 := hc _ ((hS j).mul (bdd_dirLoss hS η))
  have h5 := hc _ (bdd_dirLoss hS v)
  have h6 := hc _ ((bdd_dirLoss hS v).mul (bdd_dirLoss hS η))
  have h7 := hc _ (hS j)
  exact (((h1.sub (h2.mul h3)).sub (h4.mul h5)).sub (h6.mul h7)).add
    (continuous_const.mul ((h7.mul h5).mul h3))

end ThirdOp

section ThetaUniform

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

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The inverse chart derivative at the response `m₀ + z`. -/
local notation "Rat" z => (ContinuousLinearEquiv.symm (CDE (θr (m₀ + (z : J → ℝ)))) : 𝕍 →L[ℝ] 𝕍)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The direction-subspace picture of a set of responses: `{z : m₀ + z ∈ C}`. -/
theorem isCompact_preimage_add_mean {C : Set (J → ℝ)} (hC : IsCompact C) :
    IsCompact {z : 𝕍 | m₀ + (z : J → ℝ) ∈ C} := by
  have hcont : Continuous fun z : 𝕍 ↦ m₀ + (z : J → ℝ) :=
    continuous_const.add continuous_subtype_val
  refine Metric.isCompact_of_isClosed_isBounded (hC.isClosed.preimage hcont) ?_
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hC.isBounded
  refine isBounded_iff_forall_norm_le.2 ⟨R + ‖m₀‖, fun z hz ↦ ?_⟩
  have h := hR _ hz
  rw [← Submodule.norm_coe]
  calc ‖(z : J → ℝ)‖ = ‖(m₀ + (z : J → ℝ)) - m₀‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖m₀ + (z : J → ℝ)‖ + ‖m₀‖ := norm_sub_le _ _
    _ ≤ R + ‖m₀‖ := by gcongr

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem convex_preimage_add_mean {C : Set (J → ℝ)} (hCc : Convex ℝ C) :
    Convex ℝ {z : 𝕍 | m₀ + (z : J → ℝ) ∈ C} := by
  intro z hz z' hz' a b ha hb hab
  have h := hCc hz hz' ha hb hab
  have e : m₀ + ((a • z + b • z' : 𝕍) : J → ℝ) =
      a • (m₀ + (z : J → ℝ)) + b • (m₀ + (z' : J → ℝ)) := by
    simp only [Submodule.coe_add, Submodule.coe_smul]
    calc m₀ + (a • (z : J → ℝ) + b • (z' : J → ℝ))
        = (a + b) • m₀ + (a • (z : J → ℝ) + b • (z' : J → ℝ)) := by rw [hab, one_smul]
      _ = a • (m₀ + (z : J → ℝ)) + b • (m₀ + (z' : J → ℝ)) := by module
  change m₀ + ((a • z + b • z' : 𝕍) : J → ℝ) ∈ C
  rw [e]
  exact h

/-- The inverse chart derivative is differentiable at every interior point, with derivative
`w ↦ −R T(R w, ·) R`. -/
theorem hasFDerivAt_inverse_add_at {z : 𝕍}
    (hz : m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasFDerivAt (fun w : 𝕍 ↦ Rat w)
      ((-ContinuousLinearMap.mulLeftRight ℝ _ (Rat z) (Rat z)).comp
        ((thirdOp hS ν (θr (m₀ + (z : J → ℝ)))).comp (Rat z))) z := by
  have h := hasFDerivAt_inverse_response hS ν hz
  have h2 : HasFDerivAt (fun w : 𝕍 ↦ w - z) (ContinuousLinearMap.id ℝ 𝕍) z :=
    (hasFDerivAt_id z).sub_const z
  rw [show (0 : 𝕍) = z - z by simp] at h
  have h3 := HasFDerivAt.comp (f := fun w : 𝕍 ↦ w - z) z h h2
  rw [ContinuousLinearMap.comp_id] at h3
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun w ↦ ?_)
  simp only [Function.comp_def, Submodule.coe_sub]
  congr 4
  abel

/-- The inverse chart derivative is continuous on the interior. -/
theorem continuousOn_inverse_add {C' : Set 𝕍}
    (hC' : ∀ z ∈ C', m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ContinuousOn (fun w : 𝕍 ↦ Rat w) C' := fun z hz ↦
  (hasFDerivAt_inverse_add_at hS ν (hC' z hz)).continuousAt.continuousWithinAt

/-- The natural coordinate is continuous on the interior. -/
theorem continuousOn_responseTheta_add {C' : Set 𝕍}
    (hC' : ∀ z ∈ C', m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ContinuousOn (fun w : 𝕍 ↦ θr (m₀ + (w : J → ℝ))) C' := fun z hz ↦
  (hasFDerivAt_responseTheta_add_at hS ν (hC' z hz)).continuousAt.continuousWithinAt

/-- **The compact-uniform second-order expansion of the natural coordinate**, in the direction
subspace: for a compact convex `C'` of directions whose responses `m₀ + z` are interior,
`θ(m₀ + z') − θ(m₀ + z) − R_z(z' − z) − ½ (−R_z T_z(R_z(z'−z), R_z(z'−z)))` is uniformly
`ε ‖z' − z‖²`-small. -/
theorem uniform_responseTheta_peano {C' : Set 𝕍} (hC : IsCompact C') (hCc : Convex ℝ C')
    (hC' : ∀ z ∈ C', m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∀ ε > 0, ∃ δ > 0, ∀ z ∈ C', ∀ z' ∈ C', ‖z' - z‖ ≤ δ →
      ‖θr (m₀ + (z' : J → ℝ)) - θr (m₀ + (z : J → ℝ)) - (Rat z) (z' - z) -
        (1 / 2 : ℝ) • (-((Rat z) (thirdOp hS ν (θr (m₀ + (z : J → ℝ)))
          ((Rat z) (z' - z)) ((Rat z) (z' - z)))))‖ ≤ ε * ‖z' - z‖ ^ 2 := by
  have hF : ∀ z ∈ C', HasFDerivAt (fun w : 𝕍 ↦ θr (m₀ + (w : J → ℝ))) (Rat z) z := fun z hz ↦
    hasFDerivAt_responseTheta_add_at hS ν (hC' z hz)
  have hA : ∀ z ∈ C', HasFDerivAt (fun w : 𝕍 ↦ Rat w)
      ((-ContinuousLinearMap.mulLeftRight ℝ _ (Rat z) (Rat z)).comp
        ((thirdOp hS ν (θr (m₀ + (z : J → ℝ)))).comp (Rat z))) z := fun z hz ↦
    hasFDerivAt_inverse_add_at hS ν (hC' z hz)
  have hR := continuousOn_inverse_add hS ν hC'
  have hθ := continuousOn_responseTheta_add hS ν hC'
  have hB : ContinuousOn (fun z : 𝕍 ↦ (-ContinuousLinearMap.mulLeftRight ℝ _ (Rat z) (Rat z)).comp
      ((thirdOp hS ν (θr (m₀ + (z : J → ℝ)))).comp (Rat z))) C' := by
    have hT : ContinuousOn (fun z : 𝕍 ↦ thirdOp hS ν (θr (m₀ + (z : J → ℝ)))) C' :=
      (continuous_thirdOp hS ν).comp_continuousOn hθ
    have hmul : ContinuousOn (fun z : 𝕍 ↦
        -ContinuousLinearMap.mulLeftRight ℝ _ (Rat z) (Rat z)) C' :=
      (((ContinuousLinearMap.mulLeftRight ℝ (𝕍 →L[ℝ] 𝕍)).continuous.comp_continuousOn hR).clm_apply
        hR).neg
    exact hmul.clm_comp (hT.clm_comp hR)
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := uniform_peano_of_hasFDerivAt hC hCc hF hA hB ε hε
  refine ⟨δ, hδ, fun z hz z' hz' hzz ↦ ?_⟩
  have := h z hz z' hz' hzz
  simpa only [ContinuousLinearMap.comp_apply, neg_mulLeftRight_apply,
    ContinuousLinearEquiv.coe_coe] using this

end ThetaUniform

end Laplace.Multi
