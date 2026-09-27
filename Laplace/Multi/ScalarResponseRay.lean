/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSpeedDistortion
import Laplace.Multi.DataDissipation
import Laplace.Multi.RayFisherLengthClassification

/-!
# The one-dimensional response path is a reparametrised ray

With a single statistic (`[Unique J]`) the natural coordinate of the response along the data path
is a scalar `θ_t`, the response speed is `|q'_t|_F = |θ'_t| √Var_{P_{θ_t}} S`, and the mean map is
strictly decreasing. If the data means converge to a value below the whole range of the mean map
then `θ_t → +∞`, and by the primitive-composition inequality a finite total response length forces
finite Fisher length of the fixed ray `θ ↦ P_θ` on `(0, ∞)`
(`lintegral_sqrt_raySpeedSq_lt_top_of_length_le`). Combined with the shell classification this says:
in one dimension the response path from the featureless law to a boundary response is at least as
long as the normal ray, so a divergent shell series makes the response path infinitely long.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Scalar

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Unique J]
  {S : J → X → ℝ} (ν : Measure X) [IsProbabilityMeasure ν]

/-- The family of tilts by `θ ∈ ℝ`. -/
local notation "Pf" θ => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (fun _ : J ↦ θ)

variable (S) in
/-- The scalar mean map `θ ↦ E_{P_θ} S`. -/
noncomputable def scalarMean (θ : ℝ) : ℝ := ∫ x, S default x ∂(Pf θ)

variable (S) in
/-- The Fisher weight `√Var_{P_θ} S` along the natural coordinate. -/
noncomputable def scalarFisherWeight (θ : ℝ) : ℝ := √(lawCov (Pf θ) (S default) (S default))

omit [Nonempty X] in
theorem bdd_neg {f : X → ℝ} (hf : Bdd f) : Bdd fun x ↦ -f x := by
  obtain ⟨hm, M, hM⟩ := hf
  exact ⟨hm.neg, M, fun x ↦ by rw [abs_neg]; exact hM x⟩

variable (hS : ∀ j, Bdd (S j)) {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The scalar natural coordinate of the response along the data path. -/
noncomputable def scalarTheta (t : ℝ) : ℝ := (dataTheta hS ν hh t : J → ℝ) default

/-- Its velocity. -/
noncomputable def scalarThetaVel (t : ℝ) : ℝ := (dataThetaVel hS ν hh t : J → ℝ) default

theorem coe_dataTheta_eq (t : ℝ) :
    (dataTheta hS ν hh t : J → ℝ) = fun _ ↦ scalarTheta ν hS hh t :=
  funext fun j ↦ by rw [Unique.eq_default j]; rfl

theorem coe_dataThetaVel_eq (t : ℝ) :
    (dataThetaVel hS ν hh t : J → ℝ) = fun _ ↦ scalarThetaVel ν hS hh t :=
  funext fun j ↦ by rw [Unique.eq_default j]; rfl

theorem hasDerivAt_scalarTheta (t : ℝ) :
    HasDerivAt (scalarTheta ν hS hh) (scalarThetaVel ν hS hh t) t := by
  have hθ : HasDerivAt (fun s ↦ (dataTheta hS ν hh s : J → ℝ))
      (dataThetaVel hS ν hh t : J → ℝ) t :=
    (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_dataTheta_vel hS ν hh t)
  exact hasDerivAt_pi.1 hθ default

omit [MeasurableSpace X] [Nonempty X] hS hh in
theorem dirLoss_unique (u : J → ℝ) (x : X) : dirLoss S u x = u default * S default x := by
  simp [dirLoss]

omit hh in
/-- The scalar family as a tilt. -/
theorem family_scalar_eq_tilted (θ : ℝ) :
    (Pf θ) = ν.tilted (fun x ↦ θ * (-S default x)) := by
  rw [familyMeasure_one_zero_eq_tilted hS ν]
  congr 1
  funext x
  rw [dirLoss_unique]
  ring

omit hh in
theorem isProbabilityMeasure_family_scalar (θ : ℝ) : IsProbabilityMeasure (Pf θ) := by
  rw [family_scalar_eq_tilted ν hS θ]
  exact isProbabilityMeasure_tilted (integrable_exp_of_bdd ν ((bdd_neg (hS default)).const_mul θ))

omit hh in
/-- The scalar mean map has derivative `−Var_{P_θ} S`. -/
theorem hasDerivAt_scalarMean (θ : ℝ) :
    HasDerivAt (scalarMean S ν) (-lawCov (Pf θ) (S default) (S default)) θ := by
  have hneg : Bdd fun x ↦ -S default x := bdd_neg (hS default)
  have h := hasDerivAt_integral_tilted ν hneg (hS default) θ
  have e : scalarMean S ν = fun s ↦ ∫ x, S default x ∂ν.tilted (fun x ↦ s * (-S default x)) := by
    funext s
    rw [scalarMean, family_scalar_eq_tilted ν hS s]
  rw [e]
  refine h.congr_deriv ?_
  rw [← family_scalar_eq_tilted ν hS θ, lawCov]
  have e2 : ∀ x, S default x * -S default x = -(S default x * S default x) := fun x ↦ by ring
  simp_rw [e2]
  rw [integral_neg, integral_neg]
  ring

omit hh in
theorem hasDerivAt_scalarSecondMoment (θ : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, S default x * S default x ∂(Pf s))
      ((∫ x, S default x * S default x * -S default x ∂(Pf θ)) -
        (∫ x, S default x * S default x ∂(Pf θ)) * ∫ x, -S default x ∂(Pf θ)) θ := by
  have h := hasDerivAt_integral_tilted ν (bdd_neg (hS default)) ((hS default).mul (hS default)) θ
  simp_rw [← family_scalar_eq_tilted ν hS] at h
  exact h

omit hh in
theorem continuous_scalarVar :
    Continuous fun θ ↦ lawCov (Pf θ) (S default) (S default) := by
  have h1 : Continuous fun θ ↦ ∫ x, S default x * S default x ∂(Pf θ) :=
    continuous_iff_continuousAt.2 fun θ ↦ (hasDerivAt_scalarSecondMoment ν hS θ).continuousAt
  have h2 : Continuous (scalarMean S ν) :=
    continuous_iff_continuousAt.2 fun θ ↦ (hasDerivAt_scalarMean ν hS θ).continuousAt
  exact h1.sub (h2.mul h2)

omit hh in
theorem continuous_scalarFisherWeight : Continuous (scalarFisherWeight S ν) :=
  (continuous_scalarVar ν hS).sqrt

omit [Nonempty X] [IsProbabilityMeasure ν] hS hh in
theorem scalarFisherWeight_nonneg (θ : ℝ) : 0 ≤ scalarFisherWeight S ν θ := Real.sqrt_nonneg _

omit hh in
/-- The scalar mean map is strictly decreasing when the family has positive variance. -/
theorem strictAnti_scalarMean (hvar : ∀ θ, 0 < lawCov (Pf θ) (S default) (S default)) :
    StrictAnti (scalarMean S ν) :=
  strictAnti_of_deriv_neg fun θ ↦ by
    rw [(hasDerivAt_scalarMean ν hS θ).deriv]
    exact neg_neg_of_pos (hvar θ)

/-- The scalar mean at the response coordinate is the data mean. -/
theorem scalarMean_scalarTheta (t : ℝ) :
    scalarMean S ν (scalarTheta ν hS hh t) = ∫ x, S default x ∂ν.tilted (fun x ↦ t * h x) := by
  have h1 := congrArg Subtype.val (chartV_dataTheta hS ν hh t)
  rw [chartV_apply, pathV_apply, sub_left_inj, ← mean_familyMeasure_one_zero hS ν] at h1
  have h2 := congrFun h1 default
  rw [scalarMean, ← coe_dataTheta_eq ν hS hh t]
  exact h2

/-- **The response coordinate escapes** when the data means converge below the range of the mean
map. -/
theorem tendsto_scalarTheta_atTop (hvar : ∀ θ, 0 < lawCov (Pf θ) (S default) (S default))
    {mInf : ℝ}
    (hlim : Tendsto (fun t ↦ ∫ x, S default x ∂ν.tilted (fun x ↦ t * h x)) atTop (𝓝 mInf))
    (hbelow : ∀ θ, mInf < scalarMean S ν θ) :
    Tendsto (scalarTheta ν hS hh) atTop atTop := by
  refine tendsto_atTop.2 fun B ↦ ?_
  filter_upwards [hlim.eventually (gt_mem_nhds (hbelow B))] with t ht
  rw [← scalarMean_scalarTheta ν hS hh t] at ht
  have hanti : StrictAnti (scalarMean S ν) := strictAnti_scalarMean ν hS hvar
  exact (hanti.lt_iff_gt.1 ht).le

/-- The scalar velocity solves `θ'_t Var_{P_{θ_t}} S = −Cov_{ρ_t}(S, h)`. -/
theorem scalarThetaVel_mul_var (t : ℝ) :
    scalarThetaVel ν hS hh t * lawCov (Pf (scalarTheta ν hS hh t)) (S default) (S default) =
      -dataCov S ν h t default := by
  have h1 := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (dataTheta hS ν hh t) (fun _ ↦ (1 : ℝ)) (dataThetaVel hS ν hh t)
  rw [chartDeriv_dataThetaVel hS ν hh t, priorCov_eq_lawCov_familyMeasure hS ν,
    coe_dataTheta_eq ν hS hh t, coe_dataThetaVel_eq ν hS hh t] at h1
  have e1 : dotJ (fun _ : J ↦ (1 : ℝ)) (dataCov S ν h t) = dataCov S ν h t default := by
    simp [dotJ]
  have e2 : lawCov (Pf (scalarTheta ν hS hh t)) (dirLoss S fun _ ↦ (1 : ℝ))
      (dirLoss S fun _ ↦ scalarThetaVel ν hS hh t) =
      1 * scalarThetaVel ν hS hh t *
        lawCov (Pf (scalarTheta ν hS hh t)) (S default) (S default) := by
    have := isProbabilityMeasure_family_scalar ν hS (scalarTheta ν hS hh t)
    rw [← lawCov_const_mul_const_mul]
    congr 1 <;> funext x <;> rw [dirLoss_unique]
  rw [e1, e2] at h1
  linarith

theorem scalarThetaVel_eq (hvar : ∀ θ, 0 < lawCov (Pf θ) (S default) (S default)) (t : ℝ) :
    scalarThetaVel ν hS hh t =
      -dataCov S ν h t default / lawCov (Pf (scalarTheta ν hS hh t)) (S default) (S default) := by
  rw [eq_div_iff (hvar _).ne', scalarThetaVel_mul_var]

theorem continuous_scalarTheta : Continuous (scalarTheta ν hS hh) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_scalarTheta ν hS hh t).continuousAt

theorem continuous_scalarThetaVel (hvar : ∀ θ, 0 < lawCov (Pf θ) (S default) (S default)) :
    Continuous (scalarThetaVel ν hS hh) := by
  have e : scalarThetaVel ν hS hh = fun t ↦
      -dataCov S ν h t default / lawCov (Pf (scalarTheta ν hS hh t)) (S default) (S default) :=
    funext (scalarThetaVel_eq ν hS hh hvar)
  rw [e]
  exact (continuous_dataCov ν hS hh default).neg.div
    ((continuous_scalarVar ν hS).comp (continuous_scalarTheta ν hS hh)) fun t ↦ (hvar _).ne'

/-- **The scalar response speed**: `|q'_t|_F = |θ'_t| √Var_{P_{θ_t}} S`. -/
theorem sqrt_responseSpeedSq_eq (t : ℝ) :
    √(responseSpeedSq hS ν hh t) =
      |scalarThetaVel ν hS hh t| * scalarFisherWeight S ν (scalarTheta ν hS hh t) := by
  have := isProbabilityMeasure_family_scalar ν hS (scalarTheta ν hS hh t)
  have e : responseSpeedSq hS ν hh t = scalarThetaVel ν hS hh t * scalarThetaVel ν hS hh t *
      lawCov (Pf (scalarTheta ν hS hh t)) (S default) (S default) := by
    rw [responseSpeedSq, coe_dataTheta_eq ν hS hh t, coe_dataThetaVel_eq ν hS hh t,
      ← lawCov_const_mul_const_mul]
    congr 1 <;> funext x <;> rw [dirLoss_unique]
  rw [e, scalarFisherWeight, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs]

omit hh in
/-- The fixed ray `θ ↦ P_θ` has Fisher speed `√Var_{P_θ} S`. -/
theorem sqrt_raySpeedSq_eq (t : ℝ) :
    √(raySpeedSq S ν (0 : J → ℝ) (fun _ ↦ (-1 : ℝ)) t) = scalarFisherWeight S ν t := by
  have e0 : ((0 : J → ℝ) - t • fun _ : J ↦ (-1 : ℝ)) = fun _ ↦ t := by
    funext j; simp
  have := isProbabilityMeasure_family_scalar ν hS t
  rw [raySpeedSq, e0, scalarFisherWeight]
  congr 1
  have e : lawCov (Pf t) (dirLoss S fun _ ↦ (-1 : ℝ)) (dirLoss S fun _ ↦ (-1 : ℝ)) =
      (-1) * (-1) * lawCov (Pf t) (S default) (S default) := by
    rw [← lawCov_const_mul_const_mul]
    congr 1 <;> funext x <;> rw [dirLoss_unique]
  rw [e]
  ring

theorem scalarTheta_zero : scalarTheta ν hS hh 0 = 0 := by
  rw [scalarTheta, dataTheta_zero hS ν hh]
  rfl

/-- **Finite response length forces an integrable Fisher weight on the ray.** -/
theorem integrableOn_scalarFisherWeight_of_length_le
    (hvar : ∀ θ, 0 < lawCov (Pf θ) (S default) (S default))
    (hθ : Tendsto (scalarTheta ν hS hh) atTop atTop) {I : ℝ}
    (hI : ∀ b, 0 ≤ b → ∫ t in (0 : ℝ)..b, √(responseSpeedSq hS ν hh t) ≤ I) :
    IntegrableOn (scalarFisherWeight S ν) (Ioi (0 : ℝ)) := by
  rw [← scalarTheta_zero ν hS hh]
  refine integrableOn_Ioi_of_tendsto_atTop_of_integral_abs_deriv_mul_le (I := I)
    (continuous_scalarFisherWeight ν hS) (scalarFisherWeight_nonneg ν)
    (fun s _ ↦ hasDerivAt_scalarTheta ν hS hh s)
    (continuous_scalarThetaVel ν hS hh hvar).continuousOn hθ fun b hb ↦ ?_
  refine le_trans (le_of_eq ?_) (hI b hb)
  exact intervalIntegral.integral_congr fun t _ ↦ (sqrt_responseSpeedSq_eq ν hS hh t).symm

/-- **In one dimension the response path is at least as long as the ray**: a finite total
response length gives finite Fisher length of the fixed ray `θ ↦ P_θ`, `θ ∈ (0, ∞)`. -/
theorem lintegral_sqrt_raySpeedSq_lt_top_of_length_le
    (hvar : ∀ θ, 0 < lawCov (Pf θ) (S default) (S default))
    (hθ : Tendsto (scalarTheta ν hS hh) atTop atTop) {I : ℝ}
    (hI : ∀ b, 0 ≤ b → ∫ t in (0 : ℝ)..b, √(responseSpeedSq hS ν hh t) ≤ I) :
    (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) (fun _ ↦ (-1 : ℝ)) t))) < ⊤ := by
  have hint := integrableOn_scalarFisherWeight_of_length_le ν hS hh hvar hθ hI
  have e : (fun t ↦ ENNReal.ofReal (√(raySpeedSq S ν (0 : J → ℝ) (fun _ ↦ (-1 : ℝ)) t))) =
      fun t ↦ ENNReal.ofReal (scalarFisherWeight S ν t) :=
    funext fun t ↦ by rw [sqrt_raySpeedSq_eq ν hS t]
  rw [e]
  exact hint.lintegral_lt_top

end Scalar

end Laplace.Multi
