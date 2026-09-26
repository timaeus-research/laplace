/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasVelocityDerivative
import Laplace.Multi.ReconstructionDerivative
import Laplace.Multi.MeanMapFDeriv
import Laplace.Multi.DualPotential

/-!
# The Hessian of the reconstruction density along the atlas

Along the straight response path `M_s`, the reconstruction density `q_s = p_{θ_s}` satisfies
`d/ds q_s = q_s ℓ_s` with the centred score `ℓ_s = ⟨β_s, M_s − S⟩` (`hasDerivAt_famDens_atlas`), and

`d²/ds² q_s = q_s (ℓ_s² − κ(s) + ⟨w_s, S − M_s⟩)`, `w_s = Σ_s⁻¹ D_s β_s`

(`hasDerivAt_famDens_deriv_atlas`), the diagonal of the mixed Hessian
`D²q_M[u,z] = q_M (I − P₀ − B_M)(ℓ_u ℓ_z)`: the constant projection removes `κ = E ℓ²`, and
`⟨w_s, S − M_s⟩` is minus the regression of `ℓ_s²` on the centred features. The structural content
is that this second derivative has zero mass and zero feature moments (`integral_atlasHess`,
`integral_mul_atlasHess`): in affine response coordinates all second-order bending of the atlas
lies in directions invisible to the response map.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Normaliser

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [IsProbabilityMeasure ν] hS in
theorem famZ_eq_priorZ (θ : J → ℝ) :
    famZ S ν θ = priorZ ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := by
  simp [famZ, famWeight, priorZ, affLoss, dirLoss]

omit [Nonempty X] [IsProbabilityMeasure ν] in
theorem measurable_famDens (θ : J → ℝ) : Measurable (famDens S ν θ) := by
  unfold famDens famWeight
  exact ((bdd_dirLoss hS θ).1.neg.exp).div_const _

omit [Nonempty X] in
/-- Integrals against a family member as weighted integrals against `ν`. -/
theorem integral_famDens_mul (θ : J → ℝ) (f : X → ℝ) :
    ∫ x, f x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ =
      ∫ x, famDens S ν θ x * f x ∂ν := by
  rw [familyMeasure_eq_withDensity_famDens, integral_withDensity_eq_integral_toReal_smul₀
    (measurable_famDens hS ν θ).ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (famDens_nonneg hS ν θ x), smul_eq_mul]

/-- **The normaliser is Fréchet differentiable**: `DZ(θ)[η] = −Z(θ) ⟨η, m(θ)⟩`. -/
theorem hasFDerivAt_famZ (θ₀ : J → ℝ) :
    HasFDerivAt (famZ S ν) ((-famZ S ν θ₀) • dotCLM (famMean S ν θ₀)) θ₀ := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  obtain ⟨hint, hD⟩ := hasFDerivAt_affNum (μ := ν) (π := fun _ ↦ (1 : ℝ))
    (L₀ := fun _ ↦ (0 : ℝ)) measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
    measurable_const h0 hS (φ := fun _ ↦ (1 : ℝ)) measurable_const (Mφ := 1) (fun _ ↦ by simp)
    one_pos θ₀
  have e : (fun a : J → ℝ ↦ ∫ x, (fun _ : X ↦ (1 : ℝ)) x *
      Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S a x)) * (fun _ : X ↦ (1 : ℝ)) x ∂ν) =
      famZ S ν := by
    funext a
    simp [famZ, famWeight, affLoss, dirLoss]
  rw [e] at hD
  refine hD.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun η ↦ ?_
  rw [ContinuousLinearMap.integral_apply hint η]
  have e2 : ∀ x, ((-(1 * ((fun _ : X ↦ (1 : ℝ)) x *
      Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ₀ x)) * (fun _ : X ↦ (1 : ℝ)) x))) •
        dirCLM S x) η = -(dirLoss S η x * famWeight S θ₀ x) := fun x ↦ by
    rw [smul_apply, dirCLM_apply, smul_eq_mul]
    simp only [famWeight, affLoss, dirLoss, zero_add, one_mul, mul_one]
    ring
  simp_rw [e2]
  rw [integral_neg, integral_dirLoss_mul_famWeight hS ν θ₀ η, smul_apply, dotCLM_apply,
    smul_eq_mul]
  ring

end Normaliser

section Hessian

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤) (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
  {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
include hS hfin hrel hs0 hs1

/-- The response of the family member at time `s` is the atlas point. -/
theorem meanMap_atlasTheta' :
    meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s) = atlasPath S ν M s :=
  meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1)

/-- The normaliser along the atlas: `d/ds Z(θ_s) = −Z(θ_s) ⟨β_s, M_s⟩`. -/
theorem hasDerivAt_famZ_atlas :
    HasDerivAt (fun t ↦ famZ S ν (atlasTheta hS ν M t))
      (-famZ S ν (atlasTheta hS ν M s) * dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s)) s := by
  have hθ := hasDerivAt_atlasTheta_coe' hS ν hfin hrel hs0 hs1
  have h := (hasFDerivAt_famZ hS ν (atlasTheta hS ν M s : J → ℝ)).comp_hasDerivAt s hθ
  refine h.congr_deriv ?_
  rw [smul_apply, dotCLM_apply, smul_eq_mul, famMean_eq_meanMap hS ν,
    meanMap_atlasTheta' hS ν hfin hrel hs0 hs1]

theorem hasDerivAt_dirLoss_atlas (x : X) :
    HasDerivAt (fun t ↦ dirLoss S (atlasTheta hS ν M t) x) (dirLoss S (atlasVel hS ν hfin s) x)
      s := by
  have hθ := hasDerivAt_atlasTheta_coe' hS ν hfin hrel hs0 hs1
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ (hasDerivAt_pi.1 hθ i).mul_const (S i x)

theorem hasDerivAt_famWeight_atlas (x : X) :
    HasDerivAt (fun t ↦ famWeight S (atlasTheta hS ν M t) x)
      (-(famWeight S (atlasTheta hS ν M s) x * dirLoss S (atlasVel hS ν hfin s) x)) s := by
  have h1 : HasDerivAt (fun t ↦ -dirLoss S (atlasTheta hS ν M t) x)
      (-dirLoss S (atlasVel hS ν hfin s) x) s :=
    (hasDerivAt_dirLoss_atlas hS ν hfin hrel hs0 hs1 x).neg
  refine h1.exp.congr_deriv ?_
  simp only [famWeight]
  ring

/-- **The score of the atlas**: `d/ds q_s = q_s ℓ_s`, `ℓ_s = ⟨β_s, M_s⟩ − ⟨β_s, S⟩`. -/
theorem hasDerivAt_famDens_atlas (x : X) :
    HasDerivAt (fun t ↦ famDens S ν (atlasTheta hS ν M t) x)
      (famDens S ν (atlasTheta hS ν M s) x *
        (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) - dirLoss S (atlasVel hS ν hfin s) x))
      s := by
  have hZ := famZ_pos hS ν (atlasTheta hS ν M s : J → ℝ)
  have h := (hasDerivAt_famWeight_atlas hS ν hfin hrel hs0 hs1 x).div
    (hasDerivAt_famZ_atlas hS ν hfin hrel hs0 hs1) hZ.ne'
  refine h.congr_deriv ?_
  simp only [famDens]
  field_simp
  ring

/-- The acceleration of the natural coordinates, `β_s' = −Σ_s⁻¹ D_s β_s`. -/
noncomputable def atlasAccel : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  -((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
    hS (atlasTheta hS ν M s)).symm (cumulantOp hS ν hfin hrel hs0 hs1 (atlasVel hS ν hfin s)))

theorem hasDerivAt_atlasVel_coe :
    HasDerivAt (fun t ↦ (atlasVel hS ν hfin t : J → ℝ))
      (atlasAccel hS ν hfin hrel hs0 hs1 : J → ℝ) s :=
  (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_atlasVel hS ν hfin hrel hs0 hs1)

/-- The derivative of the centred score along the atlas. -/
theorem hasDerivAt_score_atlas (x : X) :
    HasDerivAt (fun t ↦ dotJ (atlasVel hS ν hfin t) (atlasPath S ν M t) -
        dirLoss S (atlasVel hS ν hfin t) x)
      (dotJ (atlasAccel hS ν hfin hrel hs0 hs1) (atlasPath S ν M s) +
        dotJ (atlasVel hS ν hfin s) (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) -
        dirLoss S (atlasAccel hS ν hfin hrel hs0 hs1) x) s := by
  have hβ := hasDerivAt_atlasVel_coe hS ν hfin hrel hs0 hs1
  have hM := hasDerivAt_atlasPath ν (S := S) (M := M) s
  have h1 : HasDerivAt (fun t ↦ dotJ (atlasVel hS ν hfin t) (atlasPath S ν M t))
      (dotJ (atlasAccel hS ν hfin hrel hs0 hs1) (atlasPath S ν M s) +
        dotJ (atlasVel hS ν hfin s) (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0))
      s := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
      (hasDerivAt_pi.1 hβ i).mul (hasDerivAt_pi.1 hM i)
    refine h.congr_deriv ?_
    simp only [dotJ, Finset.sum_add_distrib]
  have h2 : HasDerivAt (fun t ↦ dirLoss S (atlasVel hS ν hfin t) x)
      (dirLoss S (atlasAccel hS ν hfin hrel hs0 hs1) x) s :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ (hasDerivAt_pi.1 hβ i).mul_const (S i x)
  exact h1.sub h2

/-- The regression direction `w_s = Σ_s⁻¹ D_s β_s` (minus the acceleration). -/
noncomputable def atlasBend : dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
    hS (atlasTheta hS ν M s)).symm (cumulantOp hS ν hfin hrel hs0 hs1 (atlasVel hS ν hfin s))

theorem atlasAccel_eq_neg_atlasBend :
    atlasAccel hS ν hfin hrel hs0 hs1 = -atlasBend hS ν hfin hrel hs0 hs1 := rfl

/-- **The Hessian of the reconstruction density along the atlas**:
`q_s (ℓ_s² − κ(s) + ⟨w_s, S − M_s⟩)`. -/
noncomputable def atlasHess (x : X) : ℝ :=
  famDens S ν (atlasTheta hS ν M s) x *
    ((dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) - dirLoss S (atlasVel hS ν hfin s) x) ^ 2 -
      atlasCurv hS ν hfin s +
      (dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x -
        dotJ (atlasBend hS ν hfin hrel hs0 hs1) (atlasPath S ν M s)))

/-- **Second derivative of the density along the atlas**: `d²/ds² q_s = atlasHess`. -/
theorem hasDerivAt_famDens_deriv_atlas (x : X) :
    HasDerivAt (fun t ↦ famDens S ν (atlasTheta hS ν M t) x *
        (dotJ (atlasVel hS ν hfin t) (atlasPath S ν M t) - dirLoss S (atlasVel hS ν hfin t) x))
      (atlasHess hS ν hfin hrel hs0 hs1 x) s := by
  have h := (hasDerivAt_famDens_atlas hS ν hfin hrel hs0 hs1 x).mul
    (hasDerivAt_score_atlas hS ν hfin hrel hs0 hs1 x)
  refine h.congr_deriv ?_
  unfold atlasHess atlasCurv
  rw [atlasAccel_eq_neg_atlasBend, Submodule.coe_neg, dotJ_neg_left, dirLoss_neg]
  ring

/-- The mean of the family member at time `s` is the atlas point. -/
theorem integral_stat_atlasTheta :
    (fun i ↦ ∫ x, S i x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) = atlasPath S ν M s := by
  rw [mean_familyMeasure_one_zero hS ν, meanMap_atlasTheta' hS ν hfin hrel hs0 hs1]

/-- `E_{Q_s} ⟨v, S⟩ = ⟨v, M_s⟩`. -/
theorem integral_dirLoss_atlasTheta (v : J → ℝ) :
    ∫ x, dirLoss S v x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s) = dotJ v (atlasPath S ν M s) := by
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) _
  rw [← dotJ_integral_eq _ hS v, integral_stat_atlasTheta hS ν hfin hrel hs0 hs1]

/-- The curvature is the second moment of the centred score under `Q_s`. -/
theorem atlasCurv_eq_integral_score_sq :
    atlasCurv hS ν hfin s = ∫ x, (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
      dirLoss S (atlasVel hS ν hfin s) x) ^ 2
        ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s) := by
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) _
  rw [atlasCurv_eq_priorCov, priorCov_eq_lawCov_familyMeasure hS ν,
    lawCov_self_eq_integral_sq _ (bdd_dirLoss hS _),
    integral_dirLoss_atlasTheta hS ν hfin hrel hs0 hs1]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- The third cumulant `(D_s β_s)_j` is the centred feature moment of the squared score. -/
theorem cumulantVec_atlasVel_eq (j : J) :
    cumulantVec hS ν hfin s (atlasVel hS ν hfin s) j =
      ∫ x, (S j x - atlasPath S ν M s j) * (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
        dirLoss S (atlasVel hS ν hfin s) x) ^ 2
        ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s) := by
  unfold cumulantVec thirdCentral
  rw [integral_dirLoss_atlasTheta hS ν hfin hrel hs0 hs1]
  have hM : ∫ y, S j y ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s) = atlasPath S ν M s j :=
    congrFun (integral_stat_atlasTheta hS ν hfin hrel hs0 hs1) j
  rw [hM]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- The covariance of a feature with the bending direction is minus the third cumulant. -/
theorem lawCov_stat_atlasBend (j : J) :
    lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) (S j)
        (dirLoss S (atlasBend hS ν hfin hrel hs0 hs1)) =
      -cumulantVec hS ν hfin s (atlasVel hS ν hfin s) j := by
  have h := chartDeriv_coe_apply hS ν (atlasTheta hS ν M s) (atlasBend hS ν hfin hrel hs0 hs1) j
  have e : chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS (atlasTheta hS ν M s) (atlasBend hS ν hfin hrel hs0 hs1) =
      cumulantOp hS ν hfin hrel hs0 hs1 (atlasVel hS ν hfin s) := by
    unfold atlasBend
    rw [← coe_chartDerivEquiv]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  rw [e, cumulantOp_coe_apply] at h
  linarith

/-- **The Hessian has zero mass**: `∫ d²q_s/ds² dν = 0`. -/
theorem integral_atlasHess : ∫ x, atlasHess hS ν hfin hrel hs0 hs1 x ∂ν = 0 := by
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) _
  unfold atlasHess
  rw [← integral_famDens_mul hS ν]
  have h1 := integral_dirLoss_atlasTheta hS ν hfin hrel hs0 hs1
    (atlasBend hS ν hfin hrel hs0 hs1 : J → ℝ)
  have h2 := atlasCurv_eq_integral_score_sq hS ν hfin hrel hs0 hs1
  have hb : Bdd fun x ↦ (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
      dirLoss S (atlasVel hS ν hfin s) x) ^ 2 := by
    have := (Bdd.const (dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasPath S ν M s))).sub
      (bdd_dirLoss hS (atlasVel hS ν hfin s : J → ℝ))
    simpa [sq] using this.mul this
  have hi1 : Integrable (fun x ↦ (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
      dirLoss S (atlasVel hS ν hfin s) x) ^ 2) (familyMeasure ν (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) := integrable_of_bdd_prob _ hb
  have hi2 : Integrable (fun x ↦ dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x)
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) :=
    integrable_of_bdd_prob _ (bdd_dirLoss hS (atlasBend hS ν hfin hrel hs0 hs1 : J → ℝ))
  have hA : Integrable (fun x ↦ (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
      dirLoss S (atlasVel hS ν hfin s) x) ^ 2 - atlasCurv hS ν hfin s)
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) :=
    hi1.sub (integrable_const _)
  have hB : Integrable (fun x ↦ dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x -
      dotJ (atlasBend hS ν hfin hrel hs0 hs1) (atlasPath S ν M s))
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) :=
    hi2.sub (integrable_const _)
  rw [integral_add hA hB, integral_sub hi1 (integrable_const _),
    integral_sub hi2 (integrable_const _), integral_const, integral_const, probReal_univ, one_smul,
    one_smul, h1, ← h2]
  ring

/-- **The Hessian has zero feature moments**: `∫ S_j d²q_s/ds² dν = 0`. -/
theorem integral_mul_atlasHess (j : J) :
    ∫ x, S j x * atlasHess hS ν hfin hrel hs0 hs1 x ∂ν = 0 := by
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) _
  have e0 : ∀ x, S j x * atlasHess hS ν hfin hrel hs0 hs1 x =
      famDens S ν (atlasTheta hS ν M s) x * (S j x * ((dotJ (atlasVel hS ν hfin s)
        (atlasPath S ν M s) - dirLoss S (atlasVel hS ν hfin s) x) ^ 2 - atlasCurv hS ν hfin s) +
        S j x * (dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x -
          dotJ (atlasBend hS ν hfin hrel hs0 hs1) (atlasPath S ν M s))) := fun x ↦ by
    unfold atlasHess
    ring
  simp_rw [e0]
  rw [← integral_famDens_mul hS ν]
  have hM : ∫ y, S j y ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s) = atlasPath S ν M s j :=
    congrFun (integral_stat_atlasTheta hS ν hfin hrel hs0 hs1) j
  have hb : Bdd fun x ↦ (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
      dirLoss S (atlasVel hS ν hfin s) x) ^ 2 := by
    have := (Bdd.const (dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasPath S ν M s))).sub
      (bdd_dirLoss hS (atlasVel hS ν hfin s : J → ℝ))
    simpa [sq] using this.mul this
  have hi1 : Integrable (fun x ↦ S j x * ((dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
      dirLoss S (atlasVel hS ν hfin s) x) ^ 2 - atlasCurv hS ν hfin s))
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) :=
    integrable_of_bdd_prob _ ((hS j).mul (hb.sub (Bdd.const (atlasCurv hS ν hfin s))))
  have hi2 : Integrable (fun x ↦ S j x * (dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x -
      dotJ (atlasBend hS ν hfin hrel hs0 hs1) (atlasPath S ν M s)))
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) :=
    integrable_of_bdd_prob _ ((hS j).mul
      ((bdd_dirLoss hS (atlasBend hS ν hfin hrel hs0 hs1 : J → ℝ)).sub
        (Bdd.const (dotJ (atlasBend hS ν hfin hrel hs0 hs1 : J → ℝ) (atlasPath S ν M s)))))
  rw [integral_add hi1 hi2]
  -- first term: `E[S_j ℓ²] − κ M_j = T_j`
  have hT := cumulantVec_atlasVel_eq hS ν hfin hrel hs0 hs1 j
  have hκ := atlasCurv_eq_integral_score_sq hS ν hfin hrel hs0 hs1
  have hℓ : Integrable (fun x ↦ (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
      dirLoss S (atlasVel hS ν hfin s) x) ^ 2) (familyMeasure ν (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) := integrable_of_bdd_prob _ hb
  have h1 : ∫ x, S j x * ((dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
      dirLoss S (atlasVel hS ν hfin s) x) ^ 2 - atlasCurv hS ν hfin s)
        ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s) =
      cumulantVec hS ν hfin s (atlasVel hS ν hfin s) j := by
    rw [hT]
    have e1 : ∀ x, S j x * ((dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
        dirLoss S (atlasVel hS ν hfin s) x) ^ 2 - atlasCurv hS ν hfin s) =
        (S j x - atlasPath S ν M s j) * (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
          dirLoss S (atlasVel hS ν hfin s) x) ^ 2 +
        (atlasPath S ν M s j * (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
          dirLoss S (atlasVel hS ν hfin s) x) ^ 2 - S j x * atlasCurv hS ν hfin s) := fun x ↦ by
      ring
    simp_rw [e1]
    have hi3 : Integrable (fun x ↦ (S j x - atlasPath S ν M s j) * (dotJ (atlasVel hS ν hfin s)
        (atlasPath S ν M s) - dirLoss S (atlasVel hS ν hfin s) x) ^ 2)
        (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) :=
      integrable_of_bdd_prob _ (((hS j).sub (Bdd.const (atlasPath S ν M s j))).mul hb)
    have hSj : Integrable (S j) (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) := integrable_of_bdd_prob _ (hS j)
    have hi4 : Integrable (fun x ↦ atlasPath S ν M s j * (dotJ (atlasVel hS ν hfin s)
        (atlasPath S ν M s) - dirLoss S (atlasVel hS ν hfin s) x) ^ 2 -
        S j x * atlasCurv hS ν hfin s)
        (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) :=
      (hℓ.const_mul _).sub (hSj.mul_const _)
    rw [integral_add hi3 hi4, integral_sub (hℓ.const_mul _) (hSj.mul_const _), integral_const_mul,
      integral_mul_const, hM, ← hκ]
    ring
  -- second term: `E[S_j ⟨w,S⟩] − M_j ⟨w, M⟩ = Cov(S_j, ⟨w,S⟩) = −T_j`
  have h2 : ∫ x, S j x * (dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x -
      dotJ (atlasBend hS ν hfin hrel hs0 hs1) (atlasPath S ν M s))
        ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s) =
      -cumulantVec hS ν hfin s (atlasVel hS ν hfin s) j := by
    rw [← lawCov_stat_atlasBend hS ν hfin hrel hs0 hs1 j]
    unfold lawCov
    rw [integral_dirLoss_atlasTheta hS ν hfin hrel hs0 hs1, hM]
    have hSw : Integrable (fun x ↦ S j x * dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x)
        (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) :=
      integrable_of_bdd_prob _ ((hS j).mul (bdd_dirLoss hS _))
    have hSj : Integrable (S j) (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) := integrable_of_bdd_prob _ (hS j)
    have e2 : ∀ x, S j x * (dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x -
        dotJ (atlasBend hS ν hfin hrel hs0 hs1) (atlasPath S ν M s)) =
        S j x * dirLoss S (atlasBend hS ν hfin hrel hs0 hs1) x -
        S j x * dotJ (atlasBend hS ν hfin hrel hs0 hs1) (atlasPath S ν M s) := fun x ↦ by ring
    simp_rw [e2]
    rw [integral_sub hSw (hSj.mul_const _), integral_mul_const, hM]
  rw [h1, h2]
  ring

end Hessian

end Laplace.Multi
