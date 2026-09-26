/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FibreHessian

/-!
# The second-order Peano expansion of the response map

A generic lemma: if `F` is differentiable near `0` with derivative field `A`, and `A` is
differentiable at `0` with derivative `B`, then `F z − F 0 − A 0 z − ½ B z z = o(‖z‖²)`
(`isLittleO_peano_of_hasFDerivAt`, by the mean value inequality along the segment).

Applied to the response map `F_φ(M+z) = E_{Π(M+z)} φ` of a bounded observable: the derivative field
`A z = (w ↦ E_{Π(M+z)}[φ ℓ_{M+z,w}])` is a continuous linear functional for every `z`, it is the
derivative of `F_φ` at every interior point (`hasFDerivAt_integral_response_at`), it is
differentiable at `0` with derivative the response Hessian `B u w = E_Q[φ N_M(ℓ_{M,u} ℓ_{M,w})]`
(`hasFDerivAt_responseDerivField`, assembled on a basis, identified by uniqueness of derivatives),
and therefore (`response_peano`)

`E_{Π(M+z)} φ = E_Q φ + Cov_Q(φ, ℓ_{M,z}) + ½ E_Q[φ N_M(ℓ_{M,z}²)] + o(‖z‖²)`.
-/

open MeasureTheory Filter Topology Set Asymptotics

namespace Laplace.Multi

section Peano

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order Peano expansion from a differentiable derivative field.** -/
theorem isLittleO_peano_of_hasFDerivAt {F : E → ℝ} {A : E → (E →L[ℝ] ℝ)}
    {B : E →L[ℝ] (E →L[ℝ] ℝ)} (hF : ∀ᶠ z in 𝓝 (0 : E), HasFDerivAt F (A z) z)
    (hA : HasFDerivAt A B 0) :
    (fun z ↦ F z - F 0 - A 0 z - (1 / 2) * B z z) =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hA'⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hA).def hε)
  obtain ⟨δ₂, hδ₂, hF'⟩ := Metric.eventually_nhds_iff.1 hF
  rw [Metric.eventually_nhds_iff]
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z hz ↦ ?_⟩
  rw [dist_zero_right] at hz
  have hz₁ : ‖z‖ < δ₁ := hz.trans_le (min_le_left _ _)
  have hz₂ : ‖z‖ < δ₂ := hz.trans_le (min_le_right _ _)
  -- the segment function
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t ↦ F (t • z) - t * A 0 z - (t ^ 2 / 2) * B z z :=
    ⟨_, rfl⟩
  have hgd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (A (t • z) z - A 0 z - t * B z z) t := by
    intro t ht
    have htz : ‖t • z‖ < δ₂ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ < δ₂ := by simpa using hz₂
    have h1 : HasDerivAt (fun t : ℝ ↦ F (t • z)) (A (t • z) z) t := by
      have hl : HasDerivAt (fun t : ℝ ↦ t • z) z t := by
        simpa using (hasDerivAt_id t).smul_const z
      have := (hF' (by rwa [dist_zero_right])).comp_hasDerivAt t hl
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun t : ℝ ↦ t * A 0 z) (A 0 z) t := by
      simpa using (hasDerivAt_id t).mul_const (A 0 z)
    have h3 : HasDerivAt (fun t : ℝ ↦ (t ^ 2 / 2) * B z z) (t * B z z) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).mul_const (B z z)
      refine this.congr_deriv ?_
      ring
    rw [hg]
    exact (h1.sub h2).sub h3
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖A (t • z) z - A 0 z - t * B z z‖ ≤ ε * ‖z‖ ^ 2 := by
    intro t ht
    have htz : ‖t • z‖ < δ₁ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
        _ < δ₁ := by simpa using hz₁
    have hAt := hA' (by rwa [dist_zero_right])
    rw [zero_add] at hAt
    have e : A (t • z) z - A 0 z - t * B z z = (A (t • z) - A 0 - B (t • z)) z := by
      simp only [sub_apply, map_smul, smul_apply, smul_eq_mul]
    rw [e]
    calc ‖(A (t • z) - A 0 - B (t • z)) z‖
        ≤ ‖A (t • z) - A 0 - B (t • z)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖t • z‖ * ‖z‖ := mul_le_mul_of_nonneg_right hAt (norm_nonneg _)
      _ ≤ ε * ‖z‖ * ‖z‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          have : t * ‖z‖ ≤ ‖z‖ := by
            calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
              _ = ‖z‖ := one_mul _
          gcongr
      _ = ε * ‖z‖ ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (f' := fun t ↦ A (t • z) z - A 0 z - t * B z z) (a := 0) (b := 1)
    (fun t ht ↦ (hgd t ht).hasDerivWithinAt) hbound 1 (right_mem_Icc.mpr zero_le_one)
  rw [hg] at hmv
  simp only [one_smul, one_mul, one_pow, zero_smul, zero_mul, sub_zero, mul_one] at hmv
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z‖)]
  calc |F z - F 0 - A 0 z - 1 / 2 * B z z| = |F z - A 0 z - 1 / 2 * B z z - F 0| := by ring_nf
    _ ≤ ε * ‖z‖ ^ 2 := by simpa using hmv

end Peano

section Response

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

include hS

/-- **The derivative field of an observable's response**, `A_z(w) = E_{Π(M+z)}[φ ℓ_{M+z,w}]` at
interior points, as a continuous linear functional defined for every `z`. -/
noncomputable def responseDerivField (M : J → ℝ) (φ : X → ℝ) (z : 𝕍) : 𝕍 →L[ℝ] ℝ :=
  (covCLM S (Pfam (θr (M + z))) φ).comp
    ((𝕍).subtypeL.comp (ContinuousLinearEquiv.symm (CDE (θr (M + z))) : 𝕍 →L[ℝ] 𝕍))

variable {M : J → ℝ}

/-- At interior points the derivative field is `w ↦ E_{Π(M+z)}[φ ℓ_{M+z,w}]`. -/
theorem responseDerivField_apply {φ : X → ℝ} (hφ : Bdd φ) {z : 𝕍}
    (hz : M + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (w : 𝕍) :
    responseDerivField hS ν M φ z w =
      ∫ x, φ x * responseScore hS ν (M + z) w x ∂(Pfam (θr (M + z))) :=
  integral_response_deriv_apply hS ν hz hφ w

/-- **The response of a bounded observable is differentiable at every interior point**, with
derivative the derivative field. -/
theorem hasFDerivAt_integral_response_at {φ : X → ℝ} (hφ : Bdd φ) {z₀ : 𝕍}
    (hz₀ : M + (z₀ : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasFDerivAt (fun z : 𝕍 ↦ ∫ x, φ x ∂(Pfam (θr (M + z)))) (responseDerivField hS ν M φ z₀)
      z₀ := by
  have h := hasFDerivAt_integral_response hS ν hz₀ hφ
  have h2 : HasFDerivAt (fun z : 𝕍 ↦ z - z₀) (ContinuousLinearMap.id ℝ 𝕍) z₀ :=
    (hasFDerivAt_id z₀).sub_const z₀
  rw [show (0 : 𝕍) = z₀ - z₀ by simp] at h
  have h3 := HasFDerivAt.comp (f := fun z : 𝕍 ↦ z - z₀) z₀ h h2
  rw [ContinuousLinearMap.comp_id] at h3
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp only [Function.comp_def, Submodule.coe_sub]
  congr 3
  abel

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The derivative field is differentiable at `0`**, with derivative the response Hessian
`B u w = E_Q[φ N_M(ℓ_{M,u} ℓ_{M,w})]`. -/
theorem hasFDerivAt_responseDerivField {φ : X → ℝ} (hφ : Bdd φ) :
    ∃ B : 𝕍 →L[ℝ] (𝕍 →L[ℝ] ℝ), HasFDerivAt (responseDerivField hS ν M φ) B 0 ∧
      ∀ u w, B u w = ∫ x, φ x * normalProj hS ν M
        ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w)) x ∂(Pfam (θr M)) := by
  have hev := eventually_add_mem_intrinsicInterior hS ν hrel
  -- the field applied to a fixed direction is differentiable at `0`
  have hdir : ∀ w : 𝕍, ∃ L : 𝕍 →L[ℝ] ℝ,
      HasFDerivAt (fun z ↦ responseDerivField hS ν M φ z w) L 0 ∧
      ∀ u, L u = ∫ x, φ x * normalProj hS ν M
        ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w)) x ∂(Pfam (θr M)) := by
    intro w
    obtain ⟨L, hL, hLv⟩ := hasFDerivAt_integral_responseScore hS ν hrel hφ w
    refine ⟨L, hL.congr_of_eventuallyEq ?_, hLv⟩
    filter_upwards [hev] with z hz
    exact responseDerivField_apply hS ν hφ hz w
  choose Ld hLd hLdv using hdir
  -- basis assembly
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (Module.finrank ℝ (𝕍))) ℝ (𝕍),
    b = Module.finBasis ℝ _ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ (𝕍)) → StrongDual ℝ (𝕍),
    c = fun i ↦ LinearMap.toContinuousLinearMap (b.coord i) := ⟨_, rfl⟩
  have hdecomp : ∀ L : 𝕍 →L[ℝ] ℝ,
      L = ∑ i, ContinuousLinearMap.smulRightL ℝ _ _ (c i) (L (b i)) := fun L ↦ by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [sum_apply]
    simp only [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, hc,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    (ContinuousLinearMap.smulRightL ℝ (𝕍) ℝ (c i)).hasFDerivAt.comp (0 : 𝕍) (hLd (b i))
  have hB : HasFDerivAt (responseDerivField hS ν M φ)
      (∑ i, (ContinuousLinearMap.smulRightL ℝ (𝕍) ℝ (c i)).comp (Ld (b i))) 0 := by
    refine hsum.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
    simp only [Function.comp_def]
    exact hdecomp _
  refine ⟨_, hB, fun u w ↦ ?_⟩
  -- identify the value by uniqueness of derivatives
  have h1 := hB.clm_apply (hasFDerivAt_const w (0 : 𝕍))
  rw [ContinuousLinearMap.comp_zero, zero_add] at h1
  have h2 := h1.unique (hLd w)
  rw [← hLdv w u, ← h2, ContinuousLinearMap.flip_apply]

/-- **The second-order Peano expansion of the response map**: for a bounded observable `φ` and an
interior response `M`,
`E_{Π(M+z)}φ − E_Qφ − E_Q[φ ℓ_{M,z}] − ½ E_Q[φ N_M(ℓ_{M,z}²)] = o(‖z‖²)`. -/
theorem response_peano {φ : X → ℝ} (hφ : Bdd φ) :
    (fun z : 𝕍 ↦ (∫ x, φ x ∂(Pfam (θr (M + z)))) - (∫ x, φ x ∂(Pfam (θr M))) -
      (∫ x, φ x * responseScore hS ν M z x ∂(Pfam (θr M))) -
      (1 / 2) * ∫ x, φ x * normalProj hS ν M
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x ∂(Pfam (θr M)))
      =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
  obtain ⟨B, hB, hBv⟩ := hasFDerivAt_responseDerivField hS ν hrel hφ
  have hF : ∀ᶠ z : 𝕍 in 𝓝 0, HasFDerivAt (fun z : 𝕍 ↦ ∫ x, φ x ∂(Pfam (θr (M + z))))
      (responseDerivField hS ν M φ z) z := by
    filter_upwards [eventually_add_mem_intrinsicInterior hS ν hrel] with z hz
    exact hasFDerivAt_integral_response_at hS ν hφ hz
  have h := isLittleO_peano_of_hasFDerivAt hF hB
  refine h.congr_left fun z ↦ ?_
  have h0 : M + ((0 : 𝕍) : J → ℝ) = M := by simp
  rw [hBv, responseDerivField_apply hS ν hφ (by rw [h0]; exact hrel)]
  simp only [h0]

end Response

end Laplace.Multi
