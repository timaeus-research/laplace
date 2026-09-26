/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ObservableHessian

/-!
# The Fisher–Rao second fundamental form along the atlas

Embed the atlas `s ↦ Q_s = Π(M_s)` into `L²(ν)` by the square root `r_s = 2√q_s`, so that
`∫ r_s² dν = 4` (the curve lies on the sphere of radius `2`) and `∫ (r_s')² dν = κ(s)` (the Fisher
energy is the speed squared). The velocity is `r_s' = r_s ℓ_s / 2` and the acceleration splits into
three mutually orthogonal pieces,

`r_s'' = (r_s/4) N_{M_s}(ℓ_s²)  −  (κ(s)/4) r_s  −  (r_s/4) B_{M_s}(ℓ_s²)`,

the normal part (the second fundamental form of the family inside the sphere), the radial part
(the curvature of the sphere itself, `−|r'|²/|r|² · r`) and the part tangent to the family (the
atlas is not a geodesic of the family unless `B(ℓ²) = 0`). The orthogonality relations follow from
`N` having zero mass and zero feature moments and `B(ℓ²)` being a tangent score.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Curvature

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤) {s : ℝ}
include hS

omit [Nonempty X] [Nonempty J] hfin in
theorem famDens_pos (θ : J → ℝ) (x : X) : 0 < famDens S ν θ x :=
  div_pos (famWeight_pos θ x) (famZ_pos hS ν θ)

omit hfin in
/-- The normal projection of a bounded observable is bounded. -/
theorem bdd_normalProj {M : J → ℝ} {f : X → ℝ} (hf : Bdd f) : Bdd (normalProj hS ν M hf) :=
  (hf.sub (Bdd.const _)).sub (bdd_responseScore hS ν M _)

/-- The square-root embedding `r_s = 2√q_s` of the atlas into `L²(ν)`. -/
noncomputable def sqrtDens (s : ℝ) (x : X) : ℝ :=
  2 * Real.sqrt (famDens S ν (atlasTheta hS ν M s) x)

omit hfin in
theorem sqrtDens_pos (s : ℝ) (x : X) : 0 < sqrtDens hS ν (M := M) s x :=
  mul_pos two_pos (Real.sqrt_pos.2 (famDens_pos hS ν _ x))

omit hfin in
theorem sqrtDens_sq (s : ℝ) (x : X) :
    sqrtDens hS ν (M := M) s x ^ 2 = 4 * famDens S ν (atlasTheta hS ν M s) x := by
  unfold sqrtDens
  rw [mul_pow, Real.sq_sqrt (famDens_nonneg hS ν _ x)]
  norm_num

omit hfin in
/-- The curve lies on the sphere of radius `2` in `L²(ν)`. -/
theorem integral_sqrtDens_sq (s : ℝ) : ∫ x, sqrtDens hS ν (M := M) s x ^ 2 ∂ν = 4 := by
  simp_rw [sqrtDens_sq hS ν]
  rw [integral_const_mul, integral_famDens hS ν, mul_one]

omit hfin in
/-- Integrals of `r_s² g` against `ν` are integrals of `4g` against `Q_s`. -/
theorem integral_sqrtDens_sq_mul (s : ℝ) (g : X → ℝ) :
    ∫ x, sqrtDens hS ν (M := M) s x ^ 2 * g x ∂ν =
      4 * ∫ x, g x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν M s) := by
  rw [integral_famDens_mul hS ν, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [sqrtDens_sq hS ν]
  ring

include hfin

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
  (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
include hrel hs0 hs1

/-- **The velocity of the square-root embedding is half the score**: `r_s' = r_s ℓ_s / 2`. -/
theorem hasDerivAt_sqrtDens (x : X) :
    HasDerivAt (fun t ↦ sqrtDens hS ν (M := M) t x)
      (sqrtDens hS ν (M := M) s x * atlasScore hS ν hfin s x / 2) s := by
  have hq := hasDerivAt_famDens_atlas hS ν hfin hrel hs0 hs1 x
  have hpos := famDens_pos hS ν (atlasTheta hS ν M s : J → ℝ) x
  have h := (hq.sqrt hpos.ne').const_mul 2
  refine h.congr_deriv ?_
  unfold sqrtDens atlasScore
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (famDens S ν (atlasTheta hS ν M s) x) := ⟨_, rfl⟩
  have hsq : r ^ 2 = famDens S ν (atlasTheta hS ν M s) x := by
    rw [hr]
    exact Real.sq_sqrt hpos.le
  have hr0 : r ≠ 0 := by
    rw [hr]
    exact (Real.sqrt_pos.2 hpos).ne'
  rw [← hr, ← hsq]
  field_simp

/-- The Fisher energy is the speed squared: `∫ (r_s')² dν = κ(s)`. -/
theorem integral_sqrtDens_velocity_sq :
    ∫ x, (sqrtDens hS ν (M := M) s x * atlasScore hS ν hfin s x / 2) ^ 2 ∂ν =
      atlasCurv hS ν hfin s := by
  rw [atlasCurv_eq_integral_score_sq hS ν hfin hrel hs0 hs1, integral_famDens_mul hS ν]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  have := sqrtDens_sq hS ν (M := M) s x
  unfold atlasScore
  linear_combination (dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasPath S ν M s) -
    dirLoss S (atlasVel hS ν hfin s : J → ℝ) x) ^ 2 / 4 * this

/-- **The acceleration of the square-root embedding**, split into normal, radial and tangential
parts: `r_s'' = (r_s/4) N(ℓ_s²) − (κ/4) r_s − (r_s/4) B(ℓ_s²)`. -/
theorem hasDerivAt_sqrtDens_velocity (x : X) :
    HasDerivAt
      (fun t ↦ sqrtDens hS ν (M := M) t x * atlasScore hS ν hfin t x / 2)
      (sqrtDens hS ν (M := M) s x / 4 *
          normalProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x -
        atlasCurv hS ν hfin s / 4 * sqrtDens hS ν (M := M) s x -
        sqrtDens hS ν (M := M) s x / 4 *
          regProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x) s := by
  have h := ((hasDerivAt_sqrtDens hS ν hfin hrel hs0 hs1 x).mul
    (hasDerivAt_score_atlas hS ν hfin hrel hs0 hs1 x)).div_const 2
  refine h.congr_deriv ?_
  have hb := atlasBend_eq_respCov hS ν hfin hrel hs0 hs1
  have hκ := atlasCurv_eq_integral_score_sq hS ν hfin hrel hs0 hs1
  rw [atlasAccel_eq_neg_atlasBend, hb, Submodule.coe_neg, dotJ_neg_left, dirLoss_neg]
  unfold normalProj regProj
  rw [responseScore_apply]
  unfold atlasScore
  beta_reduce
  unfold atlasTheta at hκ
  rw [← hκ]
  unfold atlasCurv
  ring

/-- The normal part is orthogonal to the radial part: `∫ r_s · r_s N(ℓ²) dν = 0`. -/
theorem integral_sqrtDens_mul_normal :
    ∫ x, sqrtDens hS ν (M := M) s x * (sqrtDens hS ν (M := M) s x / 4 *
      normalProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x) ∂ν = 0 := by
  have e : (fun x ↦ sqrtDens hS ν (M := M) s x * (sqrtDens hS ν (M := M) s x / 4 *
      normalProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x)) =
      fun x ↦ sqrtDens hS ν (M := M) s x ^ 2 * (normalProj hS ν (atlasPath S ν M s)
        (bdd_atlasScore_sq hS ν hfin (s := s)) x / 4) := funext fun x ↦ by ring
  rw [e, integral_sqrtDens_sq_mul hS ν, integral_div]
  unfold atlasTheta
  rw [integral_normalProj hS ν (atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1)]
  ring

/-- The tangential part is orthogonal to the radial part: `∫ r_s · r_s B(ℓ²) dν = 0`. -/
theorem integral_sqrtDens_mul_tangential :
    ∫ x, sqrtDens hS ν (M := M) s x * (sqrtDens hS ν (M := M) s x / 4 *
      regProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x) ∂ν = 0 := by
  have e : (fun x ↦ sqrtDens hS ν (M := M) s x * (sqrtDens hS ν (M := M) s x / 4 *
      regProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x)) =
      fun x ↦ sqrtDens hS ν (M := M) s x ^ 2 * (regProj hS ν (atlasPath S ν M s)
        (bdd_atlasScore_sq hS ν hfin (s := s)) x / 4) := funext fun x ↦ by ring
  rw [e, integral_sqrtDens_sq_mul hS ν, integral_div]
  unfold atlasTheta regProj
  rw [integral_responseScore hS ν (atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1)]
  ring

/-- The normal part is orthogonal to the tangential part: `∫ r_s² N(ℓ²) B(ℓ²) dν = 0`. -/
theorem integral_normal_mul_tangential :
    ∫ x, (sqrtDens hS ν (M := M) s x / 4 *
        normalProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x) *
      (sqrtDens hS ν (M := M) s x / 4 *
        regProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x) ∂ν = 0 := by
  have hrel' := atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) := isProbabilityMeasure_family hS ν _
  have e : (fun x ↦ (sqrtDens hS ν (M := M) s x / 4 *
        normalProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x) *
      (sqrtDens hS ν (M := M) s x / 4 *
        regProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x)) =
      fun x ↦ sqrtDens hS ν (M := M) s x ^ 2 * (normalProj hS ν (atlasPath S ν M s)
        (bdd_atlasScore_sq hS ν hfin (s := s)) x * regProj hS ν (atlasPath S ν M s)
          (bdd_atlasScore_sq hS ν hfin (s := s)) x / 16) := funext fun x ↦ by ring
  rw [e, integral_sqrtDens_sq_mul hS ν, integral_div]
  unfold regProj
  simp only [responseScore_apply]
  unfold atlasTheta
  have hP' := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have hj : ∀ j, ∫ x, normalProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x *
      S j x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
          hS (atlasPath S ν M s)) = 0 := fun j ↦ by
    refine (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)).trans
      (integral_stat_mul_normalProj hS ν hrel' (bdd_atlasScore_sq hS ν hfin (s := s)) j)
    exact mul_comm _ _
  rw [integral_mul_sub_dirLoss hS _ (bdd_normalProj hS ν _), integral_normalProj hS ν hrel']
  simp only [hj, mul_zero, Finset.sum_const_zero]
  ring

end Curvature

end Laplace.Multi
