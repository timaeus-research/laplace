/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasSkewness
import Laplace.Multi.ChartContinuity
import Laplace.Multi.RetractionDerivative

/-!
# The derivative of the atlas velocity

Along the straight response path the restricted covariance operator `Σ_s = −chartDeriv θ_s` is
differentiable, with derivative the third-cumulant operator

`(D_s v)_j = T_{Q_s}(S_j, ⟨v,S⟩, f_s)`, `f_s = ⟨β_s, S⟩`

(`hasDerivAt_chartDeriv_atlas`), and the atlas velocity `β_s = (chartDeriv θ_s)⁻¹ Δ` is
differentiable with derivative `β_s' = −(chartDeriv θ_s)⁻¹ D_s β_s` (`hasDerivAt_atlasVel`), by the
derivative of the ring inverse in the operator algebra (`hasFDerivAt_ringInverse`). The entries of
the covariance operator are differentiated by `hasDerivAt_lawCov_familyMeasure_path`; the operator
derivative is assembled from a basis of the direction subspace, and its values lie in the direction
subspace because the subspace is closed.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal

namespace Laplace.Multi

section Subtype

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve into a submodule is differentiable once its coercion is, with derivative in the
submodule. -/
theorem hasDerivAt_of_subtype_val {V : Submodule ℝ E} {f : ℝ → V} {f' : V} {x : ℝ}
    (h : HasDerivAt (fun t ↦ (f t : E)) (f' : E) x) : HasDerivAt f f' x := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  rw [← isLittleO_norm_left] at h ⊢
  refine h.congr_left fun t ↦ ?_
  rw [Submodule.coe_norm, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul]

end Subtype

section Trilinear

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]

/-- The third central moment is additive in its middle argument. -/
theorem thirdCentral_add₂ {g k₁ k₂ f : X → ℝ} (hg : Bdd g) (hk₁ : Bdd k₁) (hk₂ : Bdd k₂)
    (hf : Bdd f) :
    thirdCentral ρ g (fun x ↦ k₁ x + k₂ x) f = thirdCentral ρ g k₁ f + thirdCentral ρ g k₂ f := by
  unfold thirdCentral
  rw [integral_add (integrable_of_bdd_prob ρ hk₁) (integrable_of_bdd_prob ρ hk₂)]
  have h1 : Integrable (fun x ↦ (g x - ∫ y, g y ∂ρ) * (k₁ x - ∫ y, k₁ y ∂ρ) *
      (f x - ∫ y, f y ∂ρ)) ρ :=
    integrable_of_bdd_prob ρ (((hg.sub (Bdd.const _)).mul (hk₁.sub (Bdd.const _))).mul
      (hf.sub (Bdd.const _)))
  have h2 : Integrable (fun x ↦ (g x - ∫ y, g y ∂ρ) * (k₂ x - ∫ y, k₂ y ∂ρ) *
      (f x - ∫ y, f y ∂ρ)) ρ :=
    integrable_of_bdd_prob ρ (((hg.sub (Bdd.const _)).mul (hk₂.sub (Bdd.const _))).mul
      (hf.sub (Bdd.const _)))
  rw [← integral_add h1 h2]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

omit [IsProbabilityMeasure ρ] in
/-- The third central moment is homogeneous in its middle argument. -/
theorem thirdCentral_smul₂ (g k f : X → ℝ) (c : ℝ) :
    thirdCentral ρ g (fun x ↦ c * k x) f = c * thirdCentral ρ g k f := by
  unfold thirdCentral
  rw [integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

end Trilinear

section Cumulant

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS

omit hfin in
/-- The entries of the restricted covariance operator. -/
theorem chartDeriv_coe_apply (θ v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) (j : J) :
    (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS θ
      v : J → ℝ) j =
      -lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) (S j) (dirLoss S v) := by
  classical
  have h := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ (Pi.single j 1) v
  have hd : dirLoss S (Pi.single j 1) = S j := by
    funext x
    simp [dirLoss, Pi.single_apply]
  rw [dotJ_single, priorCov_eq_lawCov_familyMeasure hS ν, hd] at h
  exact h

include hfin

/-- The third-cumulant vector `(D_s v)_j = T_{Q_s}(S_j, ⟨v,S⟩, f_s)`. -/
noncomputable def cumulantVec (s : ℝ) (v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ :=
  fun j ↦ thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
    (atlasTheta hS ν M s)) (S j) (dirLoss S v) (dirLoss S (atlasVel hS ν hfin s))

theorem cumulantVec_add (s : ℝ) (v w : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    cumulantVec hS ν hfin s (v + w) = cumulantVec hS ν hfin s v + cumulantVec hS ν hfin s w := by
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) _
  funext j
  simp only [cumulantVec, Pi.add_apply]
  rw [Submodule.coe_add, dirLoss_add]
  exact thirdCentral_add₂ _ (hS j) (bdd_dirLoss hS _) (bdd_dirLoss hS _) (bdd_dirLoss hS _)

theorem cumulantVec_smul (s : ℝ) (c : ℝ) (v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    cumulantVec hS ν hfin s (c • v) = c • cumulantVec hS ν hfin s v := by
  funext j
  simp only [cumulantVec, Pi.smul_apply, smul_eq_mul]
  rw [Submodule.coe_smul, dirLoss_smul]
  exact thirdCentral_smul₂ _ _ _ _ c

/-- The third-cumulant vector as a linear map. -/
noncomputable def cumulantLin (s : ℝ) : dirSpan ν (fun _ ↦ (1 : ℝ)) S →ₗ[ℝ] (J → ℝ) where
  toFun := cumulantVec hS ν hfin s
  map_add' := cumulantVec_add hS ν hfin s
  map_smul' := cumulantVec_smul hS ν hfin s

theorem cumulantLin_apply (s : ℝ) (v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    cumulantLin hS ν hfin s v = cumulantVec hS ν hfin s v := rfl

/-- The covariance operator applied to a fixed direction is differentiable along the path, with
derivative the third-cumulant vector. -/
theorem hasDerivAt_chartDeriv_coe {s : ℝ}
    (hθ : HasDerivAt (fun t ↦ (atlasTheta hS ν M t : J → ℝ)) (atlasVel hS ν hfin s : J → ℝ) s)
    (v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    HasDerivAt (fun t ↦ (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (atlasTheta hS ν M t) v : J → ℝ)) (cumulantVec hS ν hfin s v) s := by
  rw [hasDerivAt_pi]
  intro j
  have h := (hasDerivAt_lawCov_familyMeasure_path hS ν hθ (hS j) (bdd_dirLoss hS v)).neg
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · exact chartDeriv_coe_apply hS ν _ v j
  · simp only [cumulantVec, neg_neg]

/-- The third-cumulant vector lies in the direction subspace. -/
theorem cumulantVec_mem_dirSpan {s : ℝ}
    (hθ : HasDerivAt (fun t ↦ (atlasTheta hS ν M t : J → ℝ)) (atlasVel hS ν hfin s : J → ℝ) s)
    (v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    cumulantVec hS ν hfin s v ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := by
  have h := hasDerivAt_chartDeriv_coe hS ν hfin hθ v
  rw [hasDerivAt_iff_tendsto_slope] at h
  refine (Submodule.closed_of_finiteDimensional (dirSpan ν (fun _ ↦ (1 : ℝ)) S)).mem_of_tendsto h
    (Eventually.of_forall fun t ↦ ?_)
  rw [slope_def_module]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (chartDeriv measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M t) v).2
    (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
      (atlasTheta hS ν M s) v).2)

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The third-cumulant operator** `D_s : 𝕍 → 𝕍`, the derivative of the restricted covariance
operator along the atlas. -/
noncomputable def cumulantOp {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  LinearMap.toContinuousLinearMap ((cumulantLin hS ν hfin s).codRestrict
    (dirSpan ν (fun _ ↦ (1 : ℝ)) S) fun v ↦ cumulantVec_mem_dirSpan hS ν hfin
      (hasDerivAt_atlasTheta_coe' hS ν hfin hrel hs0 hs1) v)

theorem cumulantOp_coe_apply {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    (cumulantOp hS ν hfin hrel hs0 hs1 v : J → ℝ) = cumulantVec hS ν hfin s v := rfl

/-- **The restricted covariance operator is differentiable along the atlas**, with derivative the
third-cumulant operator. -/
theorem hasDerivAt_chartDeriv_atlas {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasDerivAt (fun t ↦ chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (atlasTheta hS ν M t)) (cumulantOp hS ν hfin hrel hs0 hs1) s := by
  have hθ := hasDerivAt_atlasTheta_coe' hS ν hfin hrel hs0 hs1
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (Module.finrank ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S))) ℝ
    (dirSpan ν (fun _ ↦ (1 : ℝ)) S), b = Module.finBasis ℝ _ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S)) →
      StrongDual ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S),
    c = fun i ↦ LinearMap.toContinuousLinearMap (b.coord i) := ⟨_, rfl⟩
  have hdecomp : ∀ L : dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      L = ∑ i, ContinuousLinearMap.smulRightL ℝ _ _ (c i) (L (b i)) := fun L ↦ by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [sum_apply]
    simp only [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, hc,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul]
  have hbi : ∀ i, HasDerivAt (fun t ↦ chartDeriv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M t) (b i))
      (cumulantOp hS ν hfin hrel hs0 hs1 (b i)) s := fun i ↦
    hasDerivAt_of_subtype_val (hasDerivAt_chartDeriv_coe hS ν hfin hθ (b i))
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    (ContinuousLinearMap.smulRightL ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S)
      (dirSpan ν (fun _ ↦ (1 : ℝ)) S) (c i)).hasFDerivAt.comp_hasDerivAt s (hbi i)
  refine (hsum.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · simp only [Function.comp_def]
    exact hdecomp _
  · exact (hdecomp _).symm

omit hrel in
/-- The atlas velocity as the ring inverse of the covariance operator. -/
theorem atlasVel_eq_ringInverse (s : ℝ) :
    atlasVel hS ν hfin s = Ring.inverse (chartDeriv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M s))
      ⟨M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0,
        sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ := by
  unfold atlasVel
  rw [← coe_chartDerivEquiv_symm]
  rfl

/-- **The atlas velocity is differentiable**, with derivative `β_s' = −Σ_s⁻¹ D_s β_s`. -/
theorem hasDerivAt_atlasVel {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasDerivAt (atlasVel hS ν hfin)
      (-((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (atlasTheta hS ν M s)).symm
          (cumulantOp hS ν hfin hrel hs0 hs1 (atlasVel hS ν hfin s)))) s := by
  have hG := hasDerivAt_chartDeriv_atlas hS ν hfin hrel hs0 hs1
  have hu : IsUnit (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (atlasTheta hS ν M s)) := by
    rw [← coe_chartDerivEquiv]
    exact ((ContinuousLinearEquiv.unitsEquiv ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S)).symm
      (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (atlasTheta hS ν M s))).isUnit
  obtain ⟨u, hu⟩ := hu
  have hinv : HasDerivAt (fun t ↦ Ring.inverse (chartDeriv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M t)))
      ((-ContinuousLinearMap.mulLeftRight ℝ _ (↑u⁻¹) (↑u⁻¹)) (cumulantOp hS ν hfin hrel hs0 hs1))
      s := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at h
    exact h.comp_hasDerivAt s hG
  have h2 := hinv.clm_apply (hasDerivAt_const s (⟨M - meanMap ν (fun _ ↦ (1 : ℝ))
    (fun _ ↦ (0 : ℝ)) S 1 0, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ :
      dirSpan ν (fun _ ↦ (1 : ℝ)) S))
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun t ↦
    atlasVel_eq_ringInverse hS ν hfin t)).congr_deriv ?_
  have hx : ((↑u⁻¹ : dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S)) =
      ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (atlasTheta hS ν M s)).symm :
          dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S) := by
    rw [coe_chartDerivEquiv_symm, ← hu, Ring.inverse_unit]
  rw [map_zero, add_zero]
  have e : ((-ContinuousLinearMap.mulLeftRight ℝ _ (↑u⁻¹) (↑u⁻¹))
      (cumulantOp hS ν hfin hrel hs0 hs1)) (⟨M - meanMap ν (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 0, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ :
          dirSpan ν (fun _ ↦ (1 : ℝ)) S) =
      -((↑u⁻¹ : dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S)
        (cumulantOp hS ν hfin hrel hs0 hs1 ((↑u⁻¹ : dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ]
          dirSpan ν (fun _ ↦ (1 : ℝ)) S) ⟨M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0,
            sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩))) := rfl
  rw [e, hx]
  rfl

end Cumulant

end Laplace.Multi
