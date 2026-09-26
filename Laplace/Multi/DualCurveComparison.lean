/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DensityPeano
import Laplace.Multi.BoundaryTaylor
import Laplace.Multi.DualFlat

/-!
# The matched-velocity comparison of the mixture and exponential curves

Through an interior response `M` with `Q = Π(M)`, `θ = θ(M)`, `R = R_M` and a direction `u`, two
curves leave `Q` with the same velocity `Q ℓ_{M,u}`: the mixture-affine curve `Q^m_t = Π(M + tu)`
and the exponential curve `Q^e_t = P_{θ + tRu}`. Their second-order coefficients differ:

* mixture: `q_{M+tu} = q_M (1 + t ℓ + ½ t² N_M(ℓ²)) + o(t²)` relative-uniformly
  (`famDens_response_peano_line`);
* exponential: `p_{θ+tRu} = q_M (1 + t ℓ + ½ t² (ℓ² − E_Q ℓ²)) + O(t³)` relative-uniformly
  (`abs_famDens_exponential_line_le`);
* the difference of the coefficients is minus the regression part of the squared score,
  `N_M(ℓ²) − (ℓ² − E_Qℓ²) = −B_M(ℓ²)` (`normalProj_sub_centred_sq`), a third-cumulant vector rather
  than a scalar, and its pairing with the velocity score is minus the skewness,
  `E_Q[ℓ (N_M(ℓ²) − (ℓ² − E_Qℓ²))] = −E_Q ℓ³` (`integral_responseScore_mul_normalProj_sub`).

`dual_curve_comparison` packages the four statements.
-/

open MeasureTheory Filter Topology Set Asymptotics

namespace Laplace.Multi

section Trunc

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X)

omit hS in
/-- The truncation along a line: `T_θ(tη) = 1 + t a + ½ t² (a² − Var)`. -/
theorem densTrunc_smul (θ η : J → ℝ) (t : ℝ) (x : X) :
    densTrunc S ν θ (t • η) x = 1 + t * affScoreAt S (famMean S ν θ) η x +
      (1 / 2) * (t ^ 2 * (affScoreAt S (famMean S ν θ) η x ^ 2 - covQ S ν θ η η)) := by
  unfold densTrunc affScoreAt covQ
  rw [dotJ_smul_left, dirLoss_smul]
  have e : ∫ y, (t * dirLoss S η y) ^ 2 * famDens S ν θ y ∂ν =
      t ^ 2 * ∫ y, dirLoss S η y * dirLoss S η y * famDens S ν θ y ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    beta_reduce
    ring
  rw [e]
  ring

end Trunc

section Curves

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
include hS

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

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The response score is the affine score of `R u` at the response. -/
theorem responseScore_eq_affScoreAt (u : 𝕍) (x : X) :
    responseScore hS ν M u x =
      affScoreAt S (famMean S ν (θr M)) (ContinuousLinearEquiv.symm (CDE (θr M)) u) x := by
  rw [famMean_eq_meanMap hS ν, meanMap_responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS hrel]
  rfl

/-- The second moment of the response score is the covariance of `⟨Ru, S⟩`. -/
theorem covQ_responseScore (u : 𝕍) :
    covQ S ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) u)
      (ContinuousLinearEquiv.symm (CDE (θr M)) u) =
      ∫ y, responseScore hS ν M u y * responseScore hS ν M u y ∂(Pfam (θr M)) := by
  rw [covQ_self_eq hS ν, integral_famDens_mul hS ν]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  rw [responseScore_eq_affScoreAt hS ν hrel]
  ring

/-- **The exponential curve to second order**:
`p_{θ + tRu} = q_M (1 + tℓ + ½t²(ℓ² − E_Qℓ²)) + O(t³)`, relative-uniformly in the sample point. -/
theorem abs_famDens_exponential_line_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B) (u : 𝕍)
    {t : ℝ} (ht : (Fintype.card J : ℝ) * B *
      ‖t • (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ)‖ ≤ 1 / 4) (x : X) :
    |famDens S ν ((θr M : J → ℝ) + t • (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ)) x -
      famDens S ν (θr M) x * (1 + t * responseScore hS ν M u x + (1 / 2) * (t ^ 2 *
        (responseScore hS ν M u x ^ 2 -
          ∫ y, responseScore hS ν M u y * responseScore hS ν M u y ∂(Pfam (θr M)))))| ≤
      13 * ((Fintype.card J : ℝ) * B *
        ‖t • (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ)‖) ^ 3 * famDens S ν (θr M) x := by
  have h := abs_famDens_second_remainder_le hS ν hB0 hB (θr M : J → ℝ)
    (t • (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ)) ht x
  rw [densTrunc_smul, ← responseScore_eq_affScoreAt hS ν hrel, covQ_responseScore hS ν hrel] at h
  exact h

/-- **The mixture curve to second order**: `q_{M+tu} = q_M (1 + tℓ + ½t² N_M(ℓ²)) + o(t²)`,
relative-uniformly in the sample point. -/
theorem famDens_response_peano_line (u : 𝕍) :
    ∃ φ : ℝ → ℝ, (φ =o[𝓝 0] fun t ↦ t ^ 2) ∧ ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
      |famDens S ν (θr (M + (t • u : 𝕍))) x - famDens S ν (θr M) x *
        (1 + t * responseScore hS ν M u x + (1 / 2) * (t ^ 2 * normalProj hS ν M
          ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x))| ≤
      φ t * famDens S ν (θr M) x := by
  obtain ⟨φ, hφ, hev⟩ := famDens_response_peano hS ν hrel
  have hline : Tendsto (fun t : ℝ ↦ t • u) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ ↦ t • u := by fun_prop
    have := hc.tendsto 0
    simpa using this
  refine ⟨fun t ↦ φ (t • u), ?_, ?_⟩
  · have h1 := hφ.comp_tendsto hline
    refine h1.trans_isBigO ?_
    refine IsBigO.of_bound (‖u‖ ^ 2) (Eventually.of_forall fun t ↦ ?_)
    simp only [Function.comp_def, Real.norm_eq_abs, norm_smul]
    rw [abs_of_nonneg (sq_nonneg (|t| * ‖u‖)), abs_of_nonneg (sq_nonneg t), mul_pow, sq_abs]
    exact le_of_eq (by ring)
  · filter_upwards [hline.eventually hev] with t ht x
    have h := ht x
    rw [responseScore_smul hS ν M t u x, normalProj_congr_smul hS ν M
      ((bdd_responseScore hS ν M (t • u)).mul (bdd_responseScore hS ν M (t • u)))
      ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) (c := t ^ 2)
      (fun y ↦ by rw [responseScore_smul hS ν M t u y]; ring)] at h
    exact h

omit hrel in
/-- **The second-order coefficients differ by the regression part of the squared score**:
`N_M(ℓ²) − (ℓ² − E_Qℓ²) = −B_M(ℓ²)`. -/
theorem normalProj_sub_centred_sq (u : 𝕍) (x : X) :
    normalProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x -
      (responseScore hS ν M u x ^ 2 -
        ∫ y, responseScore hS ν M u y * responseScore hS ν M u y ∂(Pfam (θr M))) =
      -regProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x := by
  unfold normalProj
  ring

/-- **The pairing with the velocity is minus the skewness**:
`E_Q[ℓ (N_M(ℓ²) − (ℓ² − E_Qℓ²))] = −E_Q ℓ³`. -/
theorem integral_responseScore_mul_normalProj_sub (u : 𝕍) :
    ∫ x, responseScore hS ν M u x *
      (normalProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x -
        (responseScore hS ν M u x ^ 2 -
          ∫ y, responseScore hS ν M u y * responseScore hS ν M u y ∂(Pfam (θr M))))
      ∂(Pfam (θr M)) = -cubicScore hS ν M u u u := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have e : (fun x ↦ responseScore hS ν M u x *
      (normalProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x -
        (responseScore hS ν M u x ^ 2 -
          ∫ y, responseScore hS ν M u y * responseScore hS ν M u y ∂(Pfam (θr M))))) =
      fun x ↦ -(regProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x *
        responseScore hS ν M u x) := by
    funext x
    rw [normalProj_sub_centred_sq hS ν]
    ring
  rw [e, integral_neg, integral_regProj_mul_responseScore hS ν hrel]
  unfold cubicScore
  congr 1

/-- **The matched-velocity comparison of the mixture and exponential curves** (see the module
docstring): the four statements together. -/
theorem dual_curve_comparison {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B) (u : 𝕍) :
    (∃ φ : ℝ → ℝ, (φ =o[𝓝 0] fun t ↦ t ^ 2) ∧ ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
      |famDens S ν (θr (M + (t • u : 𝕍))) x - famDens S ν (θr M) x *
        (1 + t * responseScore hS ν M u x + (1 / 2) * (t ^ 2 * normalProj hS ν M
          ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x))| ≤
      φ t * famDens S ν (θr M) x) ∧
    (∀ t : ℝ, (Fintype.card J : ℝ) * B *
      ‖t • (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ)‖ ≤ 1 / 4 → ∀ x,
      |famDens S ν ((θr M : J → ℝ) + t • (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ)) x -
        famDens S ν (θr M) x * (1 + t * responseScore hS ν M u x + (1 / 2) * (t ^ 2 *
          (responseScore hS ν M u x ^ 2 -
            ∫ y, responseScore hS ν M u y * responseScore hS ν M u y ∂(Pfam (θr M)))))| ≤
        13 * ((Fintype.card J : ℝ) * B *
          ‖t • (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ)‖) ^ 3 *
          famDens S ν (θr M) x) ∧
    (∀ x, normalProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x -
      (responseScore hS ν M u x ^ 2 -
        ∫ y, responseScore hS ν M u y * responseScore hS ν M u y ∂(Pfam (θr M))) =
      -regProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x) ∧
    ∫ x, responseScore hS ν M u x *
      (normalProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M u)) x -
        (responseScore hS ν M u x ^ 2 -
          ∫ y, responseScore hS ν M u y * responseScore hS ν M u y ∂(Pfam (θr M))))
      ∂(Pfam (θr M)) = -cubicScore hS ν M u u u :=
  ⟨famDens_response_peano_line hS ν hrel u,
    fun _ ht x ↦ abs_famDens_exponential_line_le hS ν hrel hB0 hB u ht x,
    fun x ↦ normalProj_sub_centred_sq hS ν u x,
    integral_responseScore_mul_normalProj_sub hS ν hrel u⟩

end Curves

end Laplace.Multi
