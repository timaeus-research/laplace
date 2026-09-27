/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseObservableHessian
import Laplace.Multi.ResponseFaceCalculus

/-!
# The response Hessian is a residual third moment

The first response of an observable `F` along a mean displacement is its regression on the
features, `⟨u_F, e⟩`. The second response is the interaction of two scores with the part of the
observable that the regression does **not** explain: with the centred regression residual
`r_F = F − E_θF − ⟨u_F(θ), S − m_θ⟩` (`regResidual`, mean zero and orthogonal to every score,
`integral_regResidual`, `integral_regResidual_mul_modelScore`), the second response of
`ResponseObservableHessian` is
`secondResponse F θ u v = E_θ[r_F · ℓ_u ℓ_v]` (`secondResponse_eq_integral_regResidual`),
the third moment of the residual against the centred scores `ℓ_u = ⟨u, S − m_θ⟩`. In particular
affine feature observables `⟨a, S⟩ + c` have zero response curvature
(`secondResponse_dirLoss_add_const`), the second derivative of `t ↦ E_{θ_t}F` along a response line
at `t = 0` is `E_{θ₀}[r_F ℓ_V²]` with `V = A_{θ₀}⁻¹ e` the velocity of the line
(`hasDerivAt_deriv_lineObservable_zero_residual`), and the same holds facewise on every open face
stratum with the conditioned law as base law (`hasDerivAt_deriv_responseObs_face`).
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

section Residual

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The centred model score. -/
local notation "f" => modelScore S ν

/-- **The centred regression residual** `r_F = F − E_θF − ⟨u_F(θ), S − m_θ⟩`. -/
noncomputable def regResidual (F : X → ℝ) (θ : 𝕍) : X → ℝ :=
  fun x ↦ F x - (∫ y, F y ∂Pfam (θ : J → ℝ)) - f θ (regressionDir hS ν F θ) x

theorem bdd_regResidual {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) : Bdd (regResidual hS ν F θ) :=
  (hF.sub (Bdd.const _)).sub (bdd_modelScore hS ν θ _)

/-- The residual has mean zero. -/
theorem integral_regResidual {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) :
    ∫ x, regResidual hS ν F θ x ∂Pfam (θ : J → ℝ) = 0 := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  unfold regResidual
  rw [integral_sub (integrable_of_bdd_prob _ (hF.sub (Bdd.const _)))
    (integrable_of_bdd_prob _ (bdd_modelScore hS ν θ _)),
    integral_sub (integrable_of_bdd_prob _ hF) (integrable_const _), integral_const,
    probReal_univ, one_smul, sub_self, integral_modelScore hS ν θ, sub_zero]

/-- **The residual is orthogonal to every score.** -/
theorem integral_regResidual_mul_modelScore {F : X → ℝ} (hF : Bdd F) (θ v : 𝕍) :
    ∫ x, regResidual hS ν F θ x * f θ v x ∂Pfam (θ : J → ℝ) = 0 := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hg : Bdd (fun x ↦ F x - dirLoss S (regressionDir hS ν F θ : J → ℝ) x) :=
    hF.sub (bdd_dirLoss hS _)
  have e : (fun x ↦ regResidual hS ν F θ x * f θ v x) = fun x ↦
      ((fun x ↦ F x - dirLoss S (regressionDir hS ν F θ : J → ℝ) x) x -
        ∫ y, (F y - dirLoss S (regressionDir hS ν F θ : J → ℝ) y) ∂Pfam (θ : J → ℝ)) *
      (dirLoss S (v : J → ℝ) x - ∫ y, dirLoss S (v : J → ℝ) y ∂Pfam (θ : J → ℝ)) := by
    funext x
    simp only [regResidual, modelScore]
    rw [integral_sub (integrable_of_bdd_prob _ hF) (integrable_of_bdd_prob _ (bdd_dirLoss hS _))]
    ring
  rw [e, ← lawCov_eq_integral_centred _ hg (bdd_dirLoss hS _)]
  exact lawCov_regressionResidual_dirLoss hS ν hF θ v

/-- **THE RESPONSE HESSIAN IS A RESIDUAL THIRD MOMENT**:
`secondResponse F θ u v = E_θ[r_F · ℓ_u ℓ_v]`. -/
theorem secondResponse_eq_integral_regResidual {F : X → ℝ} (hF : Bdd F) (θ u v : 𝕍) :
    secondResponse hS ν F θ u v =
      ∫ x, regResidual hS ν F θ x * (f θ u x * f θ v x) ∂Pfam (θ : J → ℝ) := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hr := bdd_regResidual hS ν hF θ
  have e : ∀ x, (F x - ∫ y, F y ∂Pfam (θ : J → ℝ)) * scoreResidual hS ν θ u v x =
      regResidual hS ν F θ x * (f θ u x * f θ v x) - G θ u v * regResidual hS ν F θ x +
        regResidual hS ν F θ x * f θ (mChristoffel hS ν θ u v) x +
        scoreResidual hS ν θ u v x * f θ (regressionDir hS ν F θ) x := by
    intro x
    simp only [regResidual, scoreResidual]
    ring
  have I1 : Integrable (fun x ↦ regResidual hS ν F θ x * (f θ u x * f θ v x))
      (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hr.mul ((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)))
  have I2 : Integrable (fun x ↦ G θ u v * regResidual hS ν F θ x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (Bdd.const_mul _ hr)
  have I3 : Integrable (fun x ↦ regResidual hS ν F θ x * f θ (mChristoffel hS ν θ u v) x)
      (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hr.mul (bdd_modelScore hS ν θ _))
  have I4 : Integrable (fun x ↦ scoreResidual hS ν θ u v x * f θ (regressionDir hS ν F θ) x)
      (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ ((bdd_scoreResidual hS ν θ u v).mul (bdd_modelScore hS ν θ _))
  have I12 : Integrable (fun x ↦ regResidual hS ν F θ x * (f θ u x * f θ v x) -
      G θ u v * regResidual hS ν F θ x) (Pfam (θ : J → ℝ)) := I1.sub I2
  have I123 : Integrable (fun x ↦ regResidual hS ν F θ x * (f θ u x * f θ v x) -
      G θ u v * regResidual hS ν F θ x + regResidual hS ν F θ x * f θ (mChristoffel hS ν θ u v) x)
      (Pfam (θ : J → ℝ)) := I12.add I3
  unfold secondResponse
  simp only [e]
  rw [integral_add I123 I4, integral_add I12 I3, integral_sub I1 I2, integral_const_mul,
    integral_regResidual hS ν hF θ, mul_zero, sub_zero,
    integral_regResidual_mul_modelScore hS ν hF θ, add_zero,
    integral_scoreResidual_mul_modelScore hS ν θ u v, add_zero]

/-- **Affine feature observables have zero response curvature.** -/
theorem secondResponse_dirLoss_add_const (a : 𝕍) (c : ℝ) (θ u v : 𝕍) :
    secondResponse hS ν (fun x ↦ dirLoss S (a : J → ℝ) x + c) θ u v = 0 := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  unfold secondResponse
  rw [integral_add (integrable_of_bdd_prob _ (bdd_dirLoss hS _)) (integrable_const _),
    integral_const, probReal_univ, one_smul]
  have e : ∀ x, (dirLoss S (a : J → ℝ) x + c -
      ((∫ y, dirLoss S (a : J → ℝ) y ∂Pfam (θ : J → ℝ)) + c)) * scoreResidual hS ν θ u v x =
      scoreResidual hS ν θ u v x * f θ a x := by
    intro x
    simp only [modelScore]
    ring
  simp only [e]
  exact integral_scoreResidual_mul_modelScore hS ν θ u v a

/-- The first response along a response line, as the derivative function near `t = 0`. -/
theorem deriv_lineObservable_eventuallyEq {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    deriv (lineObservable hS ν F θ₀ e) =ᶠ[𝓝 0] fun s ↦
      -lawCov (Pfam (responseLine hS ν θ₀ e s : J → ℝ)) F
        (dirLoss S (responseLineVel hS ν θ₀ e s : J → ℝ)) := by
  filter_upwards [(isOpen_responseLineDomain hS ν θ₀ e).mem_nhds
    (zero_mem_responseLineDomain hS ν θ₀ e)] with s hs
  exact (hasDerivAt_lineObservable hS ν hF θ₀ e hs).deriv

/-- **The second response along a response line is the residual third moment**:
`d²/dt² E_{θ_t}F |_{t=0} = E_{θ₀}[r_F · ℓ_V²]`, `V = A_{θ₀}⁻¹ e` the velocity of the line. -/
theorem hasDerivAt_deriv_lineObservable_zero_residual {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    HasDerivAt (deriv (lineObservable hS ν F θ₀ e))
      (∫ x, regResidual hS ν F θ₀ x *
        (f θ₀ ((CDE θ₀).symm e) x * f θ₀ ((CDE θ₀).symm e) x) ∂Pfam (θ₀ : J → ℝ)) 0 := by
  have h := hasDerivAt_deriv_lineObservable hS ν hF θ₀ e (zero_mem_responseLineDomain hS ν θ₀ e)
  rw [responseLine_zero hS ν θ₀ e, responseLineVel_zero hS ν θ₀ e] at h
  rw [← secondResponse_eq_integral_regResidual hS ν hF]
  exact h.congr_of_eventuallyEq (deriv_lineObservable_eventuallyEq hS ν hF θ₀ e)

end Residual

section Face

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (Set.range (statPoint S))

/-- **THE FACEWISE SECOND DERIVATIVE OF THE RESPONSE MAP**: on the relative interior of the face
of `M`, `A = supp q*(M)`, along a face direction `e ∈ W_A`, the second derivative of
`t ↦ E_{R_{M' + te}} F` at `t = 0` is the third moment `E_{R_{M'}}[r_F^{A} · (ℓ_V^{A})²]` of the
regression residual of `F` relative to the conditioned law `ν_A` against the score of the velocity
`V = (A^{A}_{θ})⁻¹ e`. -/
theorem hasDerivAt_deriv_responseObs_face {A : Set X} [IsProbabilityMeasure (faceMeasure ν A)]
    {M M' : J → ℝ} (hM : M ∈ hull) (hA : A = supportSet hS ν M)
    (hM' : M' ∈ intrinsicInterior ℝ (carriedResponses S A)) {F : X → ℝ} (hF : Bdd F)
    (e : dirSpan (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) S) :
    HasDerivAt (deriv (fun t : ℝ ↦ ∫ x, F x ∂responseProjection hS ν (M' + t • (e : J → ℝ))))
      (∫ x, regResidual hS (faceMeasure ν A) F
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos (faceMeasure ν A)) hS M') x *
        (modelScore S (faceMeasure ν A)
          (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS M')
          ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS
            (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
              (one_integral_pos (faceMeasure ν A)) hS M')).symm e) x *
         modelScore S (faceMeasure ν A)
          (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS M')
          ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS
            (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
              (one_integral_pos (faceMeasure ν A)) hS M')).symm e) x)
        ∂familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          ((responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos (faceMeasure ν A)) hS M' : J → ℝ))) 0 :=
  (hasDerivAt_deriv_lineObservable_zero_residual hS (faceMeasure ν A) hF _ e).congr_of_eventuallyEq
    (eventuallyEq_responseObs_face hS ν hν hM hA hM' F e).deriv

end Face

end Laplace.Multi
