/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteResponse

/-!
# The fibre-independent KL Hessian

The relative interior of the moment body is open in the direction subspace
(`eventually_add_mem_intrinsicInterior`), so the response map can be differentiated in response
coordinates at every interior point. For a data law `D` with response `M` and finite information,
the exponential-family Pythagoras identity and the Bregman identity give, for `M + z` interior,

`KL(D‖Π(M+z)) = KL(D‖Π(M)) + 𝓘(M) − 𝓘(M+z) − ⟨θ(M+z), z⟩` (`klDiv_fibre_eq`):

the whole dependence on `D` is an additive constant. Hence `z ↦ KL(D‖Π(M+z))` has derivative
`w ↦ −⟨R_{M+z} w, z⟩` at every interior `z` (`hasFDerivAt_klDiv_fibre`), vanishing at `z = 0`, and
the derivative field has derivative `u ↦ E_Q[ℓ_{M,u} ℓ_{M,w}] = ⟨Σ_M⁻¹ u, w⟩` at `0`
(`hasFDerivAt_klDiv_fibre_field`): the transverse KL profile towards reconstructed responses is the
Fisher metric of the family, identical on the whole response fibre. There is no fibre-specific
normal term; the forward divergence forgets everything but the sufficient statistic.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Fibre

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

set_option linter.unusedFintypeInType false in
/-- **The relative interior is open in the direction subspace**: `M + z` is an interior response for
all `z ∈ 𝕍` near `0`. -/
theorem eventually_add_mem_intrinsicInterior :
    ∀ᶠ z : 𝕍 in 𝓝 0, M + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  have hM := intrinsicInterior_subset hrel
  have hM' := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS hM
  have hstrict := hasStrictFDerivAt_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (θr M)
  rw [← coe_chartDerivEquiv] at hstrict
  have hmap := hstrict.map_nhds_eq_of_equiv
  rw [chartV_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel] at hmap
  have hrange : ∀ᶠ v in 𝓝 (toV ν (fun _ ↦ (1 : ℝ)) S M), v ∈ Set.range
      (chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS) := by
    rw [← hmap]
    exact eventually_map.2 (Eventually.of_forall fun θ ↦ ⟨θ, rfl⟩)
  have h2 : Tendsto (fun z : 𝕍 ↦ toV ν (fun _ ↦ (1 : ℝ)) S M + z) (𝓝 0)
      (𝓝 (toV ν (fun _ ↦ (1 : ℝ)) S M)) := by
    have := (continuous_const.add continuous_id).tendsto (0 : 𝕍)
      (f := fun z : 𝕍 ↦ toV ν (fun _ ↦ (1 : ℝ)) S M + z)
    simpa using this
  filter_upwards [h2.eventually hrange] with z hz
  obtain ⟨θ, hθ⟩ := hz
  have e := chartV_apply measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ
  rw [hθ, Submodule.coe_add, toV_apply hM'] at e
  have hmean : meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ = M + z := by
    have := congrArg (· + meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) e
    simp only [sub_add_cancel] at this
    rw [← this]
    abel
  rw [← hmean, ← range_meanMap_eq_intrinsicInterior_momentBody measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS]
  exact ⟨θ, rfl⟩

omit hrel in
/-- The natural coordinate `z ↦ θ(M + z)` is differentiable at every interior point `z₀`, with
derivative the inverse chart derivative at `M + z₀`. -/
theorem hasFDerivAt_responseTheta_add_at {z₀ : 𝕍}
    (hz₀ : M + (z₀ : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasFDerivAt (fun z : 𝕍 ↦ θr (M + z))
      (ContinuousLinearEquiv.symm (CDE (θr (M + z₀))) : 𝕍 →L[ℝ] 𝕍) z₀ := by
  have h := (hasStrictFDerivAt_responseTheta_add hS ν hz₀).hasFDerivAt
  have h2 : HasFDerivAt (fun z : 𝕍 ↦ z - z₀) (ContinuousLinearMap.id ℝ 𝕍) z₀ :=
    (hasFDerivAt_id z₀).sub_const z₀
  rw [show (0 : 𝕍) = z₀ - z₀ by simp] at h
  have h3 := HasFDerivAt.comp (f := fun z : 𝕍 ↦ z - z₀) z₀ h h2
  rw [ContinuousLinearMap.comp_id] at h3
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp only [Function.comp_def, Submodule.coe_sub]
  congr 1
  abel

omit hrel in
/-- The rate `z ↦ 𝓘(M + z)` is differentiable at every interior point, with derivative
`w ↦ −⟨θ(M+z₀), w⟩` (`∇𝓘 = −θ`). -/
theorem hasFDerivAt_genRate_response_at {z₀ : 𝕍}
    (hz₀ : M + (z₀ : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasFDerivAt (fun z : 𝕍 ↦ (genRate ν S (M + z)).toReal)
      (-(dotCLM (θr (M + z₀) : J → ℝ)).comp (𝕍).subtypeL) z₀ := by
  have hM := intrinsicInterior_subset hz₀
  have hM' := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS hM
  have h := hasFDerivAt_genRate_chart hS ν (θr (M + z₀))
  rw [chartV_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hz₀] at h
  have h2 : HasFDerivAt (fun z : 𝕍 ↦ toV ν (fun _ ↦ (1 : ℝ)) S (M + z₀) + (z - z₀))
      (ContinuousLinearMap.id ℝ 𝕍) z₀ :=
    ((hasFDerivAt_id z₀).sub_const z₀).const_add _
  rw [show toV ν (fun _ ↦ (1 : ℝ)) S (M + z₀) = toV ν (fun _ ↦ (1 : ℝ)) S (M + z₀) + (z₀ - z₀) by
    simp] at h
  have h3 := h.comp z₀ h2
  rw [ContinuousLinearMap.comp_id] at h3
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp only [Function.comp_def]
  congr 2
  rw [Submodule.coe_add, toV_apply hM', Submodule.coe_sub]
  abel

omit hrel in
/-- The pairing `z ↦ ⟨θ(M + z), z⟩` is differentiable at every interior point. -/
theorem hasFDerivAt_dotJ_responseTheta_at {z₀ : 𝕍}
    (hz₀ : M + (z₀ : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ L : 𝕍 →L[ℝ] ℝ, HasFDerivAt (fun z : 𝕍 ↦ dotJ (θr (M + z) : J → ℝ) z) L z₀ ∧
      ∀ w, L w = dotJ (ContinuousLinearEquiv.symm (CDE (θr (M + z₀))) w : J → ℝ) z₀ +
        dotJ (θr (M + z₀) : J → ℝ) w := by
  have hu := (𝕍).subtypeL.hasFDerivAt.comp z₀ (hasFDerivAt_responseTheta_add_at hS ν hz₀)
  have hc : HasFDerivAt (fun z : 𝕍 ↦ dotCLMlin (z : J → ℝ)) (dotCLMlin.comp (𝕍).subtypeL) z₀ :=
    (dotCLMlin.comp (𝕍).subtypeL).hasFDerivAt
  have h := hc.clm_apply hu
  refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_), fun w ↦ ?_⟩
  · simp only [dotCLMlin_apply, dotCLM_apply, Function.comp_def, Submodule.subtypeL_apply]
  · simp only [add_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.flip_apply, Function.comp_def, dotCLMlin_apply, dotCLM_apply,
      ContinuousLinearEquiv.coe_coe]

/-- **The Pythagoras–Bregman identity on the fibre**: for a data law `D` with response `M` and
finite information and an interior `M + z`,
`KL(D‖Π(M+z)) = KL(D‖Π(M)) + 𝓘(M) − 𝓘(M+z) − ⟨θ(M+z), z⟩`. -/
theorem klDiv_fibre_eq (D : Measure X) [IsProbabilityMeasure D] (hDkl : klDiv D ν ≠ ⊤)
    (hD : (fun j ↦ ∫ x, S j x ∂D) = M) {z : 𝕍}
    (hz : M + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (klDiv D (responseProjection hS ν (M + z))).toReal =
      (klDiv D (responseProjection hS ν M)).toReal + (genRate ν S M).toReal -
        (genRate ν S (M + z)).toReal - dotJ (θr (M + z) : J → ℝ) z := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  obtain ⟨hQP, hQM, hQkl, hpyth⟩ := responseProjection_spec hS ν hfin
  have hDQ : klDiv D (responseProjection hS ν M) ≠ ⊤ := by
    have h := hpyth D inferInstance hD
    rw [h] at hDkl
    exact (ENNReal.add_ne_top.1 hDkl).1
  have hQQ := klDiv_responseProjection_interior_ne_top hS ν hfin hz
  have h1 := klDiv_responseProjection_target_eq hS ν D hDkl hrel
  have h2 := klDiv_responseProjection_target_eq hS ν D hDkl hz
  rw [hD] at h1 h2
  rw [klDiv_self, add_zero] at h1
  rw [← h1] at h2
  rw [h2, ENNReal.toReal_add hDQ hQQ, toReal_klDiv_responseProjection_interior hS ν hfin hz,
    sub_add_cancel_left, (isLinearMap_dotJ _).map_neg]
  ring

/-- **The KL profile towards reconstructed responses is differentiable at every interior point**,
with derivative `w ↦ −⟨R_{M+z₀} w, z₀⟩`, independent of the data law on the fibre. -/
theorem hasFDerivAt_klDiv_fibre (D : Measure X) [IsProbabilityMeasure D] (hDkl : klDiv D ν ≠ ⊤)
    (hD : (fun j ↦ ∫ x, S j x ∂D) = M) {z₀ : 𝕍}
    (hz₀ : M + (z₀ : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ L : 𝕍 →L[ℝ] ℝ,
      HasFDerivAt (fun z : 𝕍 ↦ (klDiv D (responseProjection hS ν (M + z))).toReal) L z₀ ∧
      ∀ w, L w = -dotJ (ContinuousLinearEquiv.symm (CDE (θr (M + z₀))) w : J → ℝ) z₀ := by
  have hev : ∀ᶠ z : 𝕍 in 𝓝 z₀,
      M + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    have h := eventually_add_mem_intrinsicInterior hS ν hz₀
    have ht : Tendsto (fun z : 𝕍 ↦ z - z₀) (𝓝 z₀) (𝓝 0) := by
      have := (continuous_id.sub continuous_const).tendsto z₀ (f := fun z : 𝕍 ↦ z - z₀)
      simpa using this
    filter_upwards [ht.eventually h] with z hz
    simpa [add_assoc, Submodule.coe_sub] using hz
  have hI := hasFDerivAt_genRate_response_at hS ν hz₀
  obtain ⟨L₂, hL₂, hL₂v⟩ := hasFDerivAt_dotJ_responseTheta_at hS ν hz₀
  have h := (hI.const_sub ((klDiv D (responseProjection hS ν M)).toReal +
    (genRate ν S M).toReal)).sub hL₂
  refine ⟨_, h.congr_of_eventuallyEq ?_, fun w ↦ ?_⟩
  · filter_upwards [hev] with z hz
    rw [klDiv_fibre_eq hS ν hrel D hDkl hD hz, Pi.sub_apply]
  · rw [_root_.sub_apply, hL₂v, neg_apply, neg_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, dotCLM_apply, dotJ_comm]
    ring

/-- The KL profile is critical at the reconstruction: the derivative at `z = 0` vanishes. -/
theorem hasFDerivAt_klDiv_fibre_zero (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) (hD : (fun j ↦ ∫ x, S j x ∂D) = M) :
    HasFDerivAt (fun z : 𝕍 ↦ (klDiv D (responseProjection hS ν (M + z))).toReal)
      (0 : 𝕍 →L[ℝ] ℝ) 0 := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_klDiv_fibre hS ν hrel D hDkl hD (z₀ := 0)
    (by simpa using hrel)
  have : L = 0 := ContinuousLinearMap.ext fun w ↦ by
    have e := hLv w
    simp only [Submodule.coe_zero] at e
    rw [e]
    simp [dotJ]
  rwa [this] at hL

/-- **The fibre-independent KL Hessian**: the derivative field `z ↦ −⟨R_{M+z} w, z⟩` of the KL
profile is differentiable at `0`, with derivative `u ↦ E_Q[ℓ_{M,u} ℓ_{M,w}] = ⟨Σ_M⁻¹ u, w⟩`, the
Fisher metric of the family — the same for every data law on the fibre. -/
theorem hasFDerivAt_klDiv_fibre_field (w : 𝕍) :
    ∃ L : 𝕍 →L[ℝ] ℝ,
      HasFDerivAt (fun z : 𝕍 ↦ -dotJ (ContinuousLinearEquiv.symm (CDE (θr (M + z))) w : J → ℝ) z)
        L 0 ∧
      ∀ u, L u = ∫ x, responseScore hS ν M u x * responseScore hS ν M w x
        ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θr M) := by
  have hR := hasFDerivAt_inverse_response_apply hS ν hrel w
  have hRc := (𝕍).subtypeL.hasFDerivAt.comp 0 hR
  have hc : HasFDerivAt (fun z : 𝕍 ↦ dotCLMlin (z : J → ℝ)) (dotCLMlin.comp (𝕍).subtypeL) 0 :=
    (dotCLMlin.comp (𝕍).subtypeL).hasFDerivAt
  have h := (hc.clm_apply hRc).neg
  refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_), fun u ↦ ?_⟩
  · simp only [dotCLMlin_apply, dotCLM_apply, Function.comp_def, Submodule.subtypeL_apply,
      Pi.neg_apply]
  · have hsym : dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) w : J → ℝ) u =
        dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ) w := by
      have a := integral_responseScore_mul hS ν hrel w u
      have b := integral_responseScore_mul hS ν hrel u w
      have e : ∫ y, responseScore hS ν M w y * responseScore hS ν M u y
          ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θr M) =
          ∫ y, responseScore hS ν M u y * responseScore hS ν M w y
          ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θr M) :=
        integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
      linarith
    simp only [neg_apply, add_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.flip_apply, Function.comp_def, dotCLMlin_apply, dotCLM_apply,
      Submodule.coe_zero, add_zero, integral_responseScore_mul hS ν hrel u w]
    rw [hsym]
    simp [dotJ]

end Fibre

end Laplace.Multi
