/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherAccessibility

/-!
# The variance sandwich along a natural ray

Along the natural ray `p_t ∝ e^{−t g} e^{−⟨θ,S⟩} ν` towards an exposed face (`g = β − ⟨u,S⟩ ≥ 0`
the slack), write `A` for the face mass, `B_t` for the off-face mass and
`C_j(t) = ∫_{Fᶜ} g^j e^{−⟨θ,S⟩} e^{−tg} dν` for the off-face slack moments.  The Fisher speed
squared of the ray, the variance of the slack, is exactly

  `Var_{p_t}(g) = C₂(t)/(A + B_t) − (C₁(t)/(A + B_t))²`

(`raySpeedSq_eq`), and Cauchy–Schwarz `C₁² ≤ B C₂` (`slackMoment_one_sq_le`) sandwiches it:

  `A C₂(t)/(A + B_t)² ≤ Var_{p_t}(g) ≤ C₂(t)/(A + B_t)`

(`raySpeedSq_sandwich`).  Since `A ≤ A + B_t ≤ A + B_0`, the Fisher speed is comparable to
`√C₂(t)` with constants independent of `t` (`sqrt_raySpeedSq_comparable`): the ray has finite
Fisher length iff `∫^∞ √C₂(t) dt < ∞`.  This is the exact input for the shell-mass classification
of Fisher accessibility.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Covariance

variable {X : Type*} [MeasurableSpace X]

/-- The variance is invariant under `f ↦ c − f`. -/
theorem lawCov_const_sub_self (ρ : Measure X) [IsProbabilityMeasure ρ] {f : X → ℝ} (hf : Bdd f)
    (c : ℝ) : lawCov ρ (fun x ↦ c - f x) (fun x ↦ c - f x) = lawCov ρ f f := by
  rw [lawCov_eq_integral_centred ρ ((Bdd.const c).sub hf) ((Bdd.const c).sub hf),
    lawCov_eq_integral_centred ρ hf hf]
  have hm : ∫ y, c - f y ∂ρ = c - ∫ y, f y ∂ρ := by
    rw [integral_sub (integrable_const _) (integrable_of_bdd_prob ρ hf), integral_const]
    simp
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [hm]
  ring

end Covariance

section Ray

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (θ u : J → ℝ) (β : ℝ)
include hS

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- The off-face slack moments `C_j(t) = ∫_{Fᶜ} g^j e^{−⟨θ,S⟩} e^{−tg} dν`. -/
noncomputable def slackMoment (j : ℕ) (t : ℝ) : ℝ :=
  ∫ x in {x | dirLoss S u x = β}ᶜ,
    (β - dirLoss S u x) ^ j * (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ∂ν

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem slackMoment_zero (t : ℝ) : slackMoment S ν θ u β 0 t = offFaceMass S ν θ u β t := by
  simp [slackMoment, offFaceMass]

omit [Nonempty X] [Nonempty J] in
theorem integrable_slack_pow_mul (j : ℕ) (t : ℝ) :
    Integrable (fun x ↦ (β - dirLoss S u x) ^ j *
      (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))))) ν := by
  obtain ⟨hm, K, hK⟩ := bdd_dirLoss hS u
  refine (integrable_offFace hS ν θ u β t).bdd_mul (c := (|β| + K) ^ j)
    ((hm.const_sub β).pow_const j).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add le_rfl (hK x))) j

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem slackMoment_nonneg (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (j : ℕ) (t : ℝ) :
    0 ≤ slackMoment S ν θ u β j t := by
  refine setIntegral_nonneg_of_ae_restrict ?_
  filter_upwards [ae_restrict_of_ae hβ] with x hx
  exact mul_nonneg (pow_nonneg (sub_nonneg.2 hx) j)
    (mul_nonneg (famWeight_pos θ x).le (Real.exp_pos _).le)

omit [Nonempty X] [Nonempty J] in
/-- The slack moments of the ray law are the off-face moments over the normaliser. -/
theorem integral_slack_pow_famDens_ray {j : ℕ} (hj : 0 < j) (t : ℝ) :
    ∫ x, (β - dirLoss S u x) ^ j * famDens S ν (θ - t • u) x ∂ν =
      slackMoment S ν θ u β j t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) := by
  have hF := measurableSet_faceFibre hS u β
  have e : ∀ x, (β - dirLoss S u x) ^ j * famDens S ν (θ - t • u) x =
      (β - dirLoss S u x) ^ j * (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) /
        (faceMass S ν θ u β + offFaceMass S ν θ u β t) := fun x ↦ by
    rw [famDens_ray hS ν θ u β]
    ring
  simp_rw [e]
  rw [integral_div,
    ← integral_add_compl₀ hF.nullMeasurableSet (integrable_slack_pow_mul hS ν θ u β j t),
    setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ by
      have hx' : dirLoss S u x = β := hx
      rw [hx', sub_self, zero_pow hj.ne', zero_mul], zero_add]
  rfl

omit [Nonempty X] [Nonempty J] in
/-- **The exact Fisher speed of the ray**: `Var_{p_t}(g) = C₂/(A + B_t) − (C₁/(A + B_t))²`. -/
theorem raySpeedSq_eq (t : ℝ) :
    raySpeedSq S ν θ u t =
      slackMoment S ν θ u β 2 t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) -
        (slackMoment S ν θ u β 1 t / (faceMass S ν θ u β + offFaceMass S ν θ u β t)) ^ 2 := by
  have hP : IsProbabilityMeasure
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u)) := by
    rw [familyMeasure_eq_withDensity_famDens]
    exact isProbabilityMeasure_withDensity_ofReal ν (famDens_nonneg hS ν _)
      (integrable_famDens hS ν _) (integral_famDens hS ν _)
  unfold raySpeedSq
  rw [← lawCov_const_sub_self _ (bdd_dirLoss hS u) β, lawCov]
  have e1 : ∫ x, (β - dirLoss S u x)
      ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u) =
      slackMoment S ν θ u β 1 t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) := by
    rw [familyMeasure_eq_withDensity_famDens,
      integral_withDensity_ofReal ν (measurable_famDens hS ν _) (famDens_nonneg hS ν _),
      ← integral_slack_pow_famDens_ray hS ν θ u β one_pos t]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [pow_one, mul_comm])
  have e2 : ∫ x, (β - dirLoss S u x) * (β - dirLoss S u x)
      ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u) =
      slackMoment S ν θ u β 2 t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) := by
    rw [familyMeasure_eq_withDensity_famDens,
      integral_withDensity_ofReal ν (measurable_famDens hS ν _) (famDens_nonneg hS ν _),
      ← integral_slack_pow_famDens_ray hS ν θ u β two_pos t]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [sq, mul_comm])
  rw [e1, e2]
  ring

omit [Nonempty X] [Nonempty J] in
/-- **Cauchy–Schwarz for the slack moments**: `C₁(t)² ≤ B_t C₂(t)`. -/
theorem slackMoment_one_sq_le (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (t : ℝ) :
    slackMoment S ν θ u β 1 t ^ 2 ≤ offFaceMass S ν θ u β t * slackMoment S ν θ u β 2 t := by
  have hF := measurableSet_faceFibre hS u β
  have hmg : Measurable fun x ↦ β - dirLoss S u x := (bdd_dirLoss hS u).1.const_sub β
  have hmw : Measurable fun x ↦ famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))) :=
    (Real.measurable_exp.comp (bdd_dirLoss hS θ).1.neg).mul
      (Real.measurable_exp.comp (hmg.const_mul t).neg)
  have hw0 : ∀ x, 0 ≤ famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))) := fun x ↦
    mul_nonneg (famWeight_pos θ x).le (Real.exp_pos _).le
  obtain ⟨w, hwdef⟩ : ∃ w : X → ℝ, w = fun x ↦
    famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))) := ⟨_, rfl⟩
  have hmw' : Measurable w := by rw [hwdef]; exact hmw
  have hw0' : ∀ x, 0 ≤ w x := by rw [hwdef]; exact hw0
  have hwi : IntegrableOn w {x | dirLoss S u x = β}ᶜ ν := by
    rw [hwdef]; exact (integrable_offFace hS ν θ u β t).integrableOn
  have hswi : IntegrableOn (fun x ↦ (β - dirLoss S u x) ^ 2 * w x) {x | dirLoss S u x = β}ᶜ ν := by
    rw [hwdef]; exact (integrable_slack_pow_mul hS ν θ u β 2 t).integrableOn
  have hs1 : slackMoment S ν θ u β 1 t =
      ∫ x in {x | dirLoss S u x = β}ᶜ, (β - dirLoss S u x) * w x ∂ν := by
    rw [slackMoment, hwdef]
    simp only [pow_one]
  have hs2 : slackMoment S ν θ u β 2 t =
      ∫ x in {x | dirLoss S u x = β}ᶜ, (β - dirLoss S u x) ^ 2 * w x ∂ν := by
    rw [slackMoment, hwdef]
  have hB : offFaceMass S ν θ u β t = ∫ x in {x | dirLoss S u x = β}ᶜ, w x ∂ν := by
    rw [offFaceMass, hwdef]
  -- Cauchy–Schwarz with `f = √w`, `g = g √w` on the off-face set
  have hf_meas : Measurable fun x ↦ √(w x) := Real.continuous_sqrt.measurable.comp hmw'
  have hg_meas : Measurable fun x ↦ (β - dirLoss S u x) * √(w x) := hmg.mul hf_meas
  have hf : MemLp (fun x ↦ √(w x)) (ENNReal.ofReal 2) (ν.restrict {x | dirLoss S u x = β}ᶜ) := by
    rw [ENNReal.ofReal_ofNat]
    refine (memLp_two_iff_integrable_sq hf_meas.aestronglyMeasurable).2 ?_
    refine hwi.congr_fun (fun x _ ↦ ?_) hF.compl
    rw [Real.sq_sqrt (hw0' x)]
  have hg : MemLp (fun x ↦ (β - dirLoss S u x) * √(w x)) (ENNReal.ofReal 2)
      (ν.restrict {x | dirLoss S u x = β}ᶜ) := by
    rw [ENNReal.ofReal_ofNat]
    refine (memLp_two_iff_integrable_sq hg_meas.aestronglyMeasurable).2 ?_
    refine hswi.congr_fun (fun x _ ↦ ?_) hF.compl
    rw [mul_pow, Real.sq_sqrt (hw0' x)]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x ↦ Real.sqrt_nonneg _)
    ((ae_restrict_of_ae hβ).mono fun x hx ↦ mul_nonneg (sub_nonneg.2 hx) (Real.sqrt_nonneg _)) hf hg
  have hL : ∫ x in {x | dirLoss S u x = β}ᶜ, √(w x) * ((β - dirLoss S u x) * √(w x)) ∂ν =
      slackMoment S ν θ u β 1 t := by
    rw [hs1]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [mul_comm (√(w x)), mul_assoc, Real.mul_self_sqrt (hw0' x)])
  have hR1 : ∫ x in {x | dirLoss S u x = β}ᶜ, √(w x) ^ (2 : ℝ) ∂ν = offFaceMass S ν θ u β t := by
    rw [hB]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [Real.rpow_two, Real.sq_sqrt (hw0' x)])
  have hR2 : ∫ x in {x | dirLoss S u x = β}ᶜ, ((β - dirLoss S u x) * √(w x)) ^ (2 : ℝ) ∂ν =
      slackMoment S ν θ u β 2 t := by
    rw [hs2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw0' x)])
  rw [hL, hR1, hR2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  have h1 : 0 ≤ slackMoment S ν θ u β 1 t := slackMoment_nonneg ν θ u β hβ 1 t
  calc slackMoment S ν θ u β 1 t ^ 2
      ≤ (√(offFaceMass S ν θ u β t) * √(slackMoment S ν θ u β 2 t)) ^ 2 :=
        pow_le_pow_left₀ h1 hCS 2
    _ = offFaceMass S ν θ u β t * slackMoment S ν θ u β 2 t := by
        rw [mul_pow, Real.sq_sqrt (offFaceMass_nonneg hS ν θ u β t),
          Real.sq_sqrt (slackMoment_nonneg ν θ u β hβ 2 t)]

omit [Nonempty X] [Nonempty J] in
/-- **The variance sandwich**: `A C₂/(A + B_t)² ≤ Var_{p_t}(g) ≤ C₂/(A + B_t)`. -/
theorem raySpeedSq_sandwich (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) (t : ℝ) :
    faceMass S ν θ u β * slackMoment S ν θ u β 2 t /
        (faceMass S ν θ u β + offFaceMass S ν θ u β t) ^ 2 ≤ raySpeedSq S ν θ u t ∧
      raySpeedSq S ν θ u t ≤
        slackMoment S ν θ u β 2 t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hB := offFaceMass_nonneg hS ν θ u β t
  have hAB : 0 < faceMass S ν θ u β + offFaceMass S ν θ u β t := by linarith
  have hCS := slackMoment_one_sq_le hS ν θ u β hβ t
  rw [raySpeedSq_eq hS ν θ u β t]
  constructor
  · rw [div_pow]
    have h : slackMoment S ν θ u β 1 t ^ 2 / (faceMass S ν θ u β + offFaceMass S ν θ u β t) ^ 2 ≤
        offFaceMass S ν θ u β t * slackMoment S ν θ u β 2 t /
          (faceMass S ν θ u β + offFaceMass S ν θ u β t) ^ 2 :=
      div_le_div_of_nonneg_right hCS (by positivity)
    have e : faceMass S ν θ u β * slackMoment S ν θ u β 2 t /
        (faceMass S ν θ u β + offFaceMass S ν θ u β t) ^ 2 =
        slackMoment S ν θ u β 2 t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) -
          offFaceMass S ν θ u β t * slackMoment S ν θ u β 2 t /
            (faceMass S ν θ u β + offFaceMass S ν θ u β t) ^ 2 := by
      field_simp
      ring
    rw [e]
    linarith
  · exact sub_le_self _ (sq_nonneg _)

omit [Nonempty X] [Nonempty J] in
/-- The off-face mass is at most its value at `t = 0`. -/
theorem offFaceMass_le_zero (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) {t : ℝ} (ht : 0 ≤ t) :
    offFaceMass S ν θ u β t ≤ offFaceMass S ν θ u β 0 := by
  unfold offFaceMass
  refine integral_mono_ae (integrable_offFace hS ν θ u β t).integrableOn
    (integrable_offFace hS ν θ u β 0).integrableOn ?_
  filter_upwards [ae_restrict_of_ae hβ] with x hx
  refine mul_le_mul_of_nonneg_left ?_ (famWeight_pos θ x).le
  refine Real.exp_le_exp.2 ?_
  have := mul_nonneg ht (sub_nonneg.2 hx)
  simp only [zero_mul, neg_zero]
  linarith

omit [Nonempty X] [Nonempty J] in
/-- **The Fisher speed is comparable to `√C₂(t)`, uniformly in `t ≥ 0`**:
`√A/(A + B_0) · √C₂ ≤ √Var_{p_t}(g) ≤ √C₂/√A`. -/
theorem sqrt_raySpeedSq_comparable (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {t : ℝ} (ht : 0 ≤ t) :
    √(faceMass S ν θ u β) / (faceMass S ν θ u β + offFaceMass S ν θ u β 0) *
        √(slackMoment S ν θ u β 2 t) ≤ √(raySpeedSq S ν θ u t) ∧
      √(raySpeedSq S ν θ u t) ≤ √(slackMoment S ν θ u β 2 t) / √(faceMass S ν θ u β) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hB := offFaceMass_nonneg hS ν θ u β t
  have hB0 := offFaceMass_le_zero hS ν θ u β hβ ht
  have hAB : 0 < faceMass S ν θ u β + offFaceMass S ν θ u β t := by linarith
  have hC := slackMoment_nonneg ν θ u β hβ 2 t
  obtain ⟨hlow, hup⟩ := raySpeedSq_sandwich hS ν θ u β hβ hp t
  constructor
  · calc √(faceMass S ν θ u β) / (faceMass S ν θ u β + offFaceMass S ν θ u β 0) *
          √(slackMoment S ν θ u β 2 t)
        ≤ √(faceMass S ν θ u β) / (faceMass S ν θ u β + offFaceMass S ν θ u β t) *
          √(slackMoment S ν θ u β 2 t) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hAB (by linarith)
      _ = √(faceMass S ν θ u β * slackMoment S ν θ u β 2 t /
          (faceMass S ν θ u β + offFaceMass S ν θ u β t) ^ 2) := by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul hA.le, Real.sqrt_sq hAB.le]
          ring
      _ ≤ √(raySpeedSq S ν θ u t) := Real.sqrt_le_sqrt hlow
  · calc √(raySpeedSq S ν θ u t)
        ≤ √(slackMoment S ν θ u β 2 t / (faceMass S ν θ u β + offFaceMass S ν θ u β t)) :=
          Real.sqrt_le_sqrt hup
      _ ≤ √(slackMoment S ν θ u β 2 t / faceMass S ν θ u β) := by
          refine Real.sqrt_le_sqrt ?_
          exact div_le_div_of_nonneg_left hC hA (by linarith)
      _ = √(slackMoment S ν θ u β 2 t) / √(faceMass S ν θ u β) := Real.sqrt_div' _ hA.le

end Ray

end Laplace.Multi
