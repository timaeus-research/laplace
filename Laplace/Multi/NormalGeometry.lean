/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasHessian

/-!
# Normal geometry of the response map

At an interior response `M` with reconstruction `Q = Π(M)`, natural coordinate `θ(M)` and inverse
chart derivative `R = (Dm(θ)|_𝕍)⁻¹ = −Σ_M⁻¹`, the **response score** of a direction `u ∈ 𝕍` is
`ℓ_{M,u} = ⟨R u, M − S⟩ = ⟨Σ_M⁻¹ u, S − M⟩`. These are the tangent scores of the family at `Q`:

* `E_Q ℓ_{M,u} = 0` (`integral_responseScore`);
* **differential duality**: `E_Q[ℓ_{M,u} ℓ_{M,z}] = ⟨Σ_M⁻¹ u, z⟩` (`integral_responseScore_mul`) —
  the inverse covariance is at once the inverse-chart derivative and the response-space Fisher
  metric, positive definite on `𝕍` (`integral_responseScore_sq_pos`);
* the **regression projection** `B_M f = ℓ_{M, Cov_Q(S,f)}` onto the tangent scores fixes them
  (`regProj_responseScore`), and the **normal projection** `N_M f = f − E_Q f − B_M f` kills the
  tangent scores and has zero mass and zero feature moments (`normalProj_responseScore`,
  `integral_normalProj`, `integral_stat_mul_normalProj`);
* **the density-acceleration theorem**: along the atlas, `q_s''/q_s = N_{M_s}(ℓ_s²)`
  (`atlasHess_eq_normalProj`) — the second derivative of the reconstruction density is the normal
  projection of the squared score.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Score

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hS in
theorem lawCov_const_left_eq_zero (ρ : Measure X) [IsProbabilityMeasure ρ] (c : ℝ) (g : X → ℝ) :
    lawCov ρ (fun _ ↦ c) g = 0 := by
  simp [lawCov, integral_const_mul, integral_const]

variable {M : J → ℝ}

/-- The reconstruction `Π(M)` in natural coordinates. -/
local notation "Qresp" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
  (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS M)

/-- The inverse chart derivative `R = (Dm(θ(M))|_𝕍)⁻¹`. -/
local notation "Rinv" => ContinuousLinearEquiv.symm (chartDerivEquiv measurable_const
  (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (responseTheta measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS M))

/-- The response score `ℓ_{M,u} = ⟨R u, M⟩ − ⟨R u, S⟩`, `R = (Dm(θ(M))|_𝕍)⁻¹`. -/
noncomputable def responseScore (M : J → ℝ) (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : X → ℝ :=
  fun x ↦ dotJ ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS M)).symm u) M -
    dirLoss S ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos ν) hS M)).symm u) x

theorem bdd_responseScore (M : J → ℝ) (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    Bdd (responseScore hS ν M u) :=
  (Bdd.const _).sub (bdd_dirLoss hS _)

/-- The covariance vector `Cov_Q(S, f)` of an observable under the reconstruction. -/
noncomputable def respCov (M : J → ℝ) (f : X → ℝ) : J → ℝ :=
  fun j ↦ lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
    (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS M)) (S j) f

theorem isProbabilityMeasure_family_responseTheta : IsProbabilityMeasure Qresp :=
  isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) _

/-- The chart derivative inverts on the inverse chart derivative. -/
theorem chartDeriv_symm_apply (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS M) (Rinv u) = u := by
  rw [← coe_chartDerivEquiv]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

/-- The covariance vector of a bounded observable lies in the direction subspace. -/
theorem respCov_mem_dirSpan {f : X → ℝ} (hf : Bdd f) :
    respCov hS ν M f ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := by
  obtain ⟨a, ha, hreg⟩ := exists_regression_coefficient hS ν (M := M) 1 hf
  rw [atlasTheta_one hS ν] at hreg
  have h := lawCov_eq_chartDeriv_neg hS ν ha hreg
  unfold respCov
  rw [h]
  exact (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
    hS _ (-⟨a, ha⟩)).2

/-- **The regression projection** `B_M f = ℓ_{M, Cov_Q(S,f)}` onto the tangent scores. -/
noncomputable def regProj (M : J → ℝ) {f : X → ℝ} (hf : Bdd f) : X → ℝ :=
  responseScore hS ν M ⟨respCov hS ν M f, respCov_mem_dirSpan hS ν hf⟩

/-- **The normal projection** `N_M f = f − E_Q f − B_M f`. -/
noncomputable def normalProj (M : J → ℝ) {f : X → ℝ} (hf : Bdd f) : X → ℝ :=
  fun x ↦ f x - (∫ y, f y ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
    (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      hS M)) - regProj hS ν M hf x

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The reconstruction has response `M`. -/
theorem integral_stat_responseTheta : (fun i ↦ ∫ x, S i x ∂Qresp) = M := by
  rw [mean_familyMeasure_one_zero hS ν]
  exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel

theorem integral_dirLoss_responseTheta (v : J → ℝ) : ∫ x, dirLoss S v x ∂Qresp = dotJ v M := by
  have := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  rw [← dotJ_integral_eq _ hS v, integral_stat_responseTheta hS ν hrel]

/-- Response scores are centred. -/
theorem integral_responseScore (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    ∫ x, responseScore hS ν M u x ∂Qresp = 0 := by
  have := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  unfold responseScore
  rw [integral_sub (integrable_const _) (integrable_of_bdd_prob _ (bdd_dirLoss hS _)),
    integral_const, probReal_univ, one_smul, integral_dirLoss_responseTheta hS ν hrel, sub_self]

omit hrel in
/-- The covariance of a feature with a response score is the direction itself:
`Cov_Q(S_j, ℓ_{M,u}) = u_j`. -/
theorem lawCov_stat_responseScore (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) (j : J) :
    lawCov Qresp (S j) (responseScore hS ν M u) = (u : J → ℝ) j := by
  have := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  unfold responseScore
  rw [lawCov_comm, lawCov_sub_left_eq _ (Bdd.const _) (bdd_dirLoss hS _) (hS j),
    lawCov_const_left_eq_zero, zero_sub, lawCov_comm, ← chartDeriv_coe_apply hS ν,
    chartDeriv_symm_apply hS ν]

/-- **Differential duality / the response-space Fisher metric**:
`E_Q[ℓ_{M,u} ℓ_{M,z}] = ⟨Σ_M⁻¹ u, z⟩ = −⟨R u, z⟩`. -/
theorem integral_responseScore_mul (u z : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    ∫ x, responseScore hS ν M u x * responseScore hS ν M z x ∂Qresp =
      -dotJ (Rinv u : J → ℝ) (z : J → ℝ) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have h : ∫ x, responseScore hS ν M u x * responseScore hS ν M z x ∂Qresp =
      lawCov Qresp (responseScore hS ν M u) (responseScore hS ν M z) := by
    unfold lawCov
    rw [integral_responseScore hS ν hrel, zero_mul, sub_zero]
  rw [h]
  unfold responseScore
  rw [lawCov_sub_left_eq _ (Bdd.const _) (bdd_dirLoss hS _) ((Bdd.const _).sub (bdd_dirLoss hS _)),
    lawCov_const_left_eq_zero, zero_sub, lawCov_comm,
    lawCov_sub_left_eq _ (Bdd.const _) (bdd_dirLoss hS _) (bdd_dirLoss hS _),
    lawCov_const_left_eq_zero, zero_sub, neg_neg, lawCov_comm]
  have := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS M) (Rinv u : J → ℝ) (Rinv z)
  rw [priorCov_eq_lawCov_familyMeasure hS ν, chartDeriv_symm_apply hS ν] at this
  linarith

/-- **The Fisher metric is positive definite on the direction subspace.** -/
theorem integral_responseScore_sq_pos {u : dirSpan ν (fun _ ↦ (1 : ℝ)) S} (hu : u ≠ 0) :
    0 < ∫ x, responseScore hS ν M u x * responseScore hS ν M u x ∂Qresp := by
  rw [integral_responseScore_mul hS ν hrel]
  have hRu : Rinv u ≠ 0 := by
    intro h
    apply hu
    have := congrArg (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos ν) hS M)) h
    rwa [ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
  have := dotJ_chartDeriv_self_neg measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS M) hRu
  rw [chartDeriv_symm_apply hS ν] at this
  linarith

omit hrel in
/-- The covariance vector of a response score is the direction itself. -/
theorem respCov_responseScore (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    respCov hS ν M (responseScore hS ν M u) = u := by
  funext j
  exact lawCov_stat_responseScore hS ν u j

omit hrel in
/-- The regression projection fixes the tangent scores. -/
theorem regProj_responseScore (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    regProj hS ν M (bdd_responseScore hS ν M u) = responseScore hS ν M u := by
  unfold regProj
  congr 1
  exact Subtype.ext (respCov_responseScore hS ν u)

/-- The normal projection kills the tangent scores. -/
theorem normalProj_responseScore (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    normalProj hS ν M (bdd_responseScore hS ν M u) = fun _ ↦ (0 : ℝ) := by
  funext x
  unfold normalProj
  rw [regProj_responseScore hS ν, integral_responseScore hS ν hrel]
  ring

/-- The normal projection has zero mass. -/
theorem integral_normalProj {f : X → ℝ} (hf : Bdd f) :
    ∫ x, normalProj hS ν M hf x ∂Qresp = 0 := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have h1 : Integrable (fun x ↦ f x - ∫ y, f y ∂Qresp) Qresp :=
    (integrable_of_bdd_prob _ hf).sub (integrable_const _)
  have h3 : Integrable (regProj hS ν M hf) Qresp :=
    integrable_of_bdd_prob _ (bdd_responseScore hS ν M _)
  unfold normalProj
  rw [integral_sub h1 h3, integral_sub (integrable_of_bdd_prob _ hf) (integrable_const _),
    integral_const, probReal_univ, one_smul]
  unfold regProj
  rw [integral_responseScore hS ν hrel]
  ring

/-- The normal projection has zero feature moments. -/
theorem integral_stat_mul_normalProj {f : X → ℝ} (hf : Bdd f) (j : J) :
    ∫ x, S j x * normalProj hS ν M hf x ∂Qresp = 0 := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hM : ∫ y, S j y ∂Qresp = M j := congrFun (integral_stat_responseTheta hS ν hrel) j
  have hcov := lawCov_stat_responseScore hS ν (M := M)
    ⟨respCov hS ν M f, respCov_mem_dirSpan hS ν hf⟩ j
  unfold lawCov at hcov
  rw [integral_responseScore hS ν hrel, mul_zero, sub_zero] at hcov
  have e : ∀ x, S j x * normalProj hS ν M hf x =
      S j x * f x - S j x * (∫ y, f y ∂Qresp) - S j x * regProj hS ν M hf x := fun x ↦ by
    unfold normalProj
    ring
  simp_rw [e]
  have h1 : Integrable (fun x ↦ S j x * f x) Qresp := integrable_of_bdd_prob _ ((hS j).mul hf)
  have h2 : Integrable (fun x ↦ S j x * (∫ y, f y ∂Qresp)) Qresp :=
    (integrable_of_bdd_prob _ (hS j)).mul_const _
  have h3 : Integrable (fun x ↦ S j x * regProj hS ν M hf x) Qresp :=
    integrable_of_bdd_prob _ ((hS j).mul (bdd_responseScore hS ν M _))
  have h12 : Integrable (fun x ↦ S j x * f x - S j x * (∫ y, f y ∂Qresp)) Qresp := h1.sub h2
  rw [integral_sub h12 h3, integral_sub h1 h2, integral_mul_const, hM]
  unfold regProj
  rw [hcov]
  simp only [respCov, lawCov]
  rw [hM]
  ring

end Score

section Acceleration

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤) {s : ℝ}
include hS hfin

/-- The atlas score `ℓ_s = ⟨β_s, M_s − S⟩`. -/
noncomputable def atlasScore (s : ℝ) (x : X) : ℝ :=
  dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasPath S ν M s) -
    dirLoss S (atlasVel hS ν hfin s : J → ℝ) x

/-- The atlas score is the response score of the displacement at the atlas point. -/
theorem atlasScore_eq_responseScore (x : X) :
    atlasScore hS ν hfin s x =
      responseScore hS ν (atlasPath S ν M s)
        ⟨M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0,
          sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ x := rfl

theorem bdd_atlasScore : Bdd (atlasScore hS ν hfin s) :=
  bdd_responseScore hS ν _ _

theorem bdd_atlasScore_sq : Bdd fun x ↦ atlasScore hS ν hfin s x ^ 2 := by
  have e : (fun x ↦ atlasScore hS ν hfin s x ^ 2) =
      fun x ↦ atlasScore hS ν hfin s x * atlasScore hS ν hfin s x := funext fun x ↦ sq _
  rw [e]
  exact (bdd_atlasScore hS ν hfin).mul (bdd_atlasScore hS ν hfin)

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
  (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
include hrel hs0 hs1

/-- The reconstruction at the atlas point. -/
local notation "Qs" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
  (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
    (atlasPath S ν M s))

/-- The bending direction is the covariance vector of the squared score. -/
theorem atlasBend_eq_respCov :
    atlasBend hS ν hfin hrel hs0 hs1 =
      (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
          (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasPath S ν M s))).symm
        ⟨respCov hS ν (atlasPath S ν M s) (fun x ↦ atlasScore hS ν hfin s x ^ 2),
          respCov_mem_dirSpan hS ν (bdd_atlasScore_sq hS ν hfin)⟩ := by
  unfold atlasBend
  congr 1
  refine Subtype.ext ?_
  rw [cumulantOp_coe_apply]
  funext j
  rw [cumulantVec_atlasVel_eq hS ν hfin hrel hs0 hs1 j]
  unfold atlasTheta
  have hP : IsProbabilityMeasure Qs :=
    isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have hM : ∫ y, S j y ∂Qs = atlasPath S ν M s j :=
    congrFun (integral_stat_atlasTheta hS ν hfin hrel hs0 hs1) j
  have hb := bdd_atlasScore_sq hS ν hfin (s := s)
  have h1 : Integrable (fun x ↦ S j x * atlasScore hS ν hfin s x ^ 2) Qs :=
    integrable_of_bdd_prob _ ((hS j).mul hb)
  have h2 : Integrable (fun x ↦ atlasPath S ν M s j * atlasScore hS ν hfin s x ^ 2) Qs :=
    (integrable_of_bdd_prob _ hb).const_mul _
  simp only [respCov, lawCov]
  rw [hM, ← integral_const_mul, ← integral_sub h1 h2]
  unfold atlasScore
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- **The density-acceleration theorem**: `q_s'' = q_s · N_{M_s}(ℓ_s²)`. -/
theorem atlasHess_eq_normalProj (x : X) :
    atlasHess hS ν hfin hrel hs0 hs1 x =
      famDens S ν (atlasTheta hS ν M s) x *
        normalProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x := by
  unfold atlasHess normalProj regProj
  rw [atlasBend_eq_respCov hS ν hfin hrel hs0 hs1,
    atlasCurv_eq_integral_score_sq hS ν hfin hrel hs0 hs1]
  unfold responseScore atlasScore atlasTheta
  ring

end Acceleration

end Laplace.Multi
