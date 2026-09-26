/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DensitySecondOrder

/-!
# Algebra of the second-order truncation

The second-order truncation `T_θ(η)` of the density ratio splits under `η = v + ζ` as

`T_θ(v+ζ) = 1 + A v + ½(A v² − Var v) + (A ζ + A v · A ζ + ½ A ζ² − Cov(v,ζ) − ½ Var ζ)`

(`densTrunc_add`), with `A v = ⟨v, m(θ) − S⟩` the affine score (`affScoreAt`) and `Cov` the
covariance of the features under `P_θ` (`covQ`). Both are bounded by the norm of their arguments
(`abs_affScoreAt_le`, `abs_covQ_le`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Algebra

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]

/-- The affine score `A_m(v)(x) = ⟨v, m − S(x)⟩`. -/
noncomputable def affScoreAt (S : J → X → ℝ) (m v : J → ℝ) (x : X) : ℝ :=
  dotJ v m - dirLoss S v x

/-- The covariance of two feature directions under `P_θ`. -/
noncomputable def covQ (S : J → X → ℝ) (ν : Measure X) (θ v w : J → ℝ) : ℝ :=
  (∫ y, dirLoss S v y * dirLoss S w y * famDens S ν θ y ∂ν) -
    dotJ v (famMean S ν θ) * dotJ w (famMean S ν θ)

omit [MeasurableSpace X] [Nonempty X] in
theorem affScoreAt_add (S : J → X → ℝ) (m v w : J → ℝ) (x : X) :
    affScoreAt S m (v + w) x = affScoreAt S m v x + affScoreAt S m w x := by
  unfold affScoreAt
  rw [dotJ_add_left, dirLoss_add]
  ring

omit [MeasurableSpace X] [Nonempty X] in
theorem affScoreAt_smul (S : J → X → ℝ) (m : J → ℝ) (c : ℝ) (v : J → ℝ) (x : X) :
    affScoreAt S m (c • v) x = c * affScoreAt S m v x := by
  unfold affScoreAt
  rw [dotJ_smul_left, dirLoss_smul]
  ring

omit [MeasurableSpace X] [Nonempty X] in
theorem affScoreAt_neg (S : J → X → ℝ) (m v : J → ℝ) (x : X) :
    affScoreAt S m (-v) x = -affScoreAt S m v x := by
  unfold affScoreAt
  rw [dotJ_neg_left, dirLoss_neg]
  ring

variable {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] in
theorem integrable_dirLoss_mul_famDens (θ v : J → ℝ) :
    Integrable (fun y ↦ dirLoss S v y * famDens S ν θ y) ν := by
  obtain ⟨-, C₁, hC₁⟩ := bdd_dirLoss hS v
  refine (integrable_famDens hS ν θ).bdd_mul (c := C₁) (bdd_dirLoss hS v).1.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs]
  exact hC₁ y

theorem integrable_dirLoss_mul_dirLoss_mul_famDens (θ v w : J → ℝ) :
    Integrable (fun y ↦ dirLoss S v y * dirLoss S w y * famDens S ν θ y) ν := by
  obtain ⟨-, C₁, hC₁⟩ := bdd_dirLoss hS v
  obtain ⟨-, C₂, hC₂⟩ := bdd_dirLoss hS w
  refine (integrable_famDens hS ν θ).bdd_mul (c := C₁ * C₂)
    ((bdd_dirLoss hS v).1.mul (bdd_dirLoss hS w).1).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hC₁ y) (hC₂ y) (abs_nonneg _)
    ((abs_nonneg _).trans (hC₁ (Classical.arbitrary X)))

/-- The covariance is bilinear (additivity in the first argument). -/
theorem covQ_add_left (θ v₁ v₂ w : J → ℝ) :
    covQ S ν θ (v₁ + v₂) w = covQ S ν θ v₁ w + covQ S ν θ v₂ w := by
  unfold covQ
  rw [dotJ_add_left, dirLoss_add]
  have h1 := integrable_dirLoss_mul_dirLoss_mul_famDens hS ν θ v₁ w
  have h2 := integrable_dirLoss_mul_dirLoss_mul_famDens hS ν θ v₂ w
  rw [show (fun y ↦ (dirLoss S v₁ y + dirLoss S v₂ y) * dirLoss S w y * famDens S ν θ y) =
    fun y ↦ dirLoss S v₁ y * dirLoss S w y * famDens S ν θ y +
      dirLoss S v₂ y * dirLoss S w y * famDens S ν θ y from funext fun y ↦ by ring,
    integral_add h1 h2]
  ring

omit [Nonempty X] hS [IsProbabilityMeasure ν] in
theorem covQ_comm (θ v w : J → ℝ) : covQ S ν θ v w = covQ S ν θ w v := by
  unfold covQ
  rw [mul_comm (dotJ v _)]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun y ↦ by beta_reduce; ring)

/-- `Var_θ⟨v,S⟩ = E_θ[A_v²]`: the variance of a feature direction is the second moment of its
affine score. -/
theorem covQ_self_eq (θ v : J → ℝ) :
    covQ S ν θ v v = ∫ y, affScoreAt S (famMean S ν θ) v y ^ 2 * famDens S ν θ y ∂ν := by
  unfold covQ affScoreAt
  have h2 := integrable_dirLoss_mul_dirLoss_mul_famDens hS ν θ v v
  have h1 : Integrable (fun y ↦ dotJ v (famMean S ν θ) * (dirLoss S v y * famDens S ν θ y)) ν :=
    (integrable_dirLoss_mul_famDens hS ν θ v |>.const_mul _)
  have h0 : Integrable (fun y ↦ dotJ v (famMean S ν θ) ^ 2 * famDens S ν θ y) ν :=
    (integrable_famDens hS ν θ).const_mul _
  have h1' : Integrable (fun y ↦ 2 * (dotJ v (famMean S ν θ) * (dirLoss S v y * famDens S ν θ y)))
      ν := h1.const_mul 2
  have h01 : Integrable (fun y ↦ dotJ v (famMean S ν θ) ^ 2 * famDens S ν θ y -
      2 * (dotJ v (famMean S ν θ) * (dirLoss S v y * famDens S ν θ y))) ν := h0.sub h1'
  have e : (fun y ↦ (dotJ v (famMean S ν θ) - dirLoss S v y) ^ 2 * famDens S ν θ y) =
      fun y ↦ (dotJ v (famMean S ν θ) ^ 2 * famDens S ν θ y -
        2 * (dotJ v (famMean S ν θ) * (dirLoss S v y * famDens S ν θ y))) +
        dirLoss S v y * dirLoss S v y * famDens S ν θ y := funext fun y ↦ by ring
  rw [e, integral_add h01 h2, integral_sub h0 h1', integral_const_mul, integral_const_mul,
    integral_const_mul, integral_famDens hS ν, integral_dirLoss_mul_famDens hS ν θ v]
  ring

/-- **The second-order truncation splits under `η = v + ζ`.** -/
theorem densTrunc_add (θ v ζ : J → ℝ) (x : X) :
    densTrunc S ν θ (v + ζ) x =
      1 + affScoreAt S (famMean S ν θ) v x +
        (1 / 2) * (affScoreAt S (famMean S ν θ) v x ^ 2 - covQ S ν θ v v) +
        (affScoreAt S (famMean S ν θ) ζ x + affScoreAt S (famMean S ν θ) v x *
          affScoreAt S (famMean S ν θ) ζ x + (1 / 2) * affScoreAt S (famMean S ν θ) ζ x ^ 2 -
          covQ S ν θ v ζ - (1 / 2) * covQ S ν θ ζ ζ) := by
  have hvv := integrable_dirLoss_mul_dirLoss_mul_famDens hS ν θ v v
  have hvζ := integrable_dirLoss_mul_dirLoss_mul_famDens hS ν θ v ζ
  have hζζ := integrable_dirLoss_mul_dirLoss_mul_famDens hS ν θ ζ ζ
  have e : (fun y ↦ (dirLoss S (v + ζ) y) ^ 2 * famDens S ν θ y) = fun y ↦
      (dirLoss S v y * dirLoss S v y * famDens S ν θ y +
        2 * (dirLoss S v y * dirLoss S ζ y * famDens S ν θ y)) +
        dirLoss S ζ y * dirLoss S ζ y * famDens S ν θ y := funext fun y ↦ by
    rw [dirLoss_add]
    ring
  have hvζ' : Integrable (fun y ↦ 2 * (dirLoss S v y * dirLoss S ζ y * famDens S ν θ y)) ν :=
    hvζ.const_mul 2
  have h12 : Integrable (fun y ↦ dirLoss S v y * dirLoss S v y * famDens S ν θ y +
      2 * (dirLoss S v y * dirLoss S ζ y * famDens S ν θ y)) ν := hvv.add hvζ'
  unfold densTrunc affScoreAt covQ
  rw [e, integral_add h12 hζζ, integral_add hvv hvζ', integral_const_mul, dotJ_add_left,
    dirLoss_add]
  beta_reduce
  ring

end Algebra

section Bounds

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ j x, |S j x| ≤ B)
include hS hB0 hB

omit [MeasurableSpace X] [Nonempty X] hS in
/-- `|A_m(v)(x)| ≤ |J| (‖m‖ + B) ‖v‖`. -/
theorem abs_affScoreAt_le (m v : J → ℝ) (x : X) :
    |affScoreAt S m v x| ≤ (Fintype.card J : ℝ) * (‖m‖ + B) * ‖v‖ := by
  unfold affScoreAt
  calc |dotJ v m - dirLoss S v x| ≤ |dotJ v m| + |dirLoss S v x| := abs_sub _ _
    _ ≤ (Fintype.card J : ℝ) * ‖v‖ * ‖m‖ + (Fintype.card J : ℝ) * B * ‖v‖ :=
        add_le_add (abs_dotJ_le_card_mul v m) (abs_dirLoss_le_card_mul hB0 hB v x)
    _ = (Fintype.card J : ℝ) * (‖m‖ + B) * ‖v‖ := by ring

omit [Nonempty X] in
/-- `|Cov_θ(v,w)| ≤ 2 (|J| B)² ‖v‖ ‖w‖`. -/
theorem abs_covQ_le (θ v w : J → ℝ) :
    |covQ S ν θ v w| ≤ 2 * ((Fintype.card J : ℝ) * B) ^ 2 * ‖v‖ * ‖w‖ := by
  have hv : ∀ y, |dirLoss S v y| ≤ (Fintype.card J : ℝ) * B * ‖v‖ := fun y ↦
    abs_dirLoss_le_card_mul hB0 hB v y
  have hw : ∀ y, |dirLoss S w y| ≤ (Fintype.card J : ℝ) * B * ‖w‖ := fun y ↦
    abs_dirLoss_le_card_mul hB0 hB w y
  have hK : 0 ≤ (Fintype.card J : ℝ) * B := by positivity
  have h1 : |∫ y, dirLoss S v y * dirLoss S w y * famDens S ν θ y ∂ν| ≤
      ((Fintype.card J : ℝ) * B * ‖v‖) * ((Fintype.card J : ℝ) * B * ‖w‖) := by
    have := norm_integral_le_of_norm_le ((integrable_famDens hS ν θ).const_mul
      (((Fintype.card J : ℝ) * B * ‖v‖) * ((Fintype.card J : ℝ) * B * ‖w‖))) (μ := ν)
      (f := fun y ↦ dirLoss S v y * dirLoss S w y * famDens S ν θ y)
      (Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (famDens_nonneg hS ν θ y)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hv y) (hw y) (abs_nonneg _)
          (by positivity)) (famDens_nonneg hS ν θ y))
    rwa [integral_const_mul, integral_famDens hS ν, mul_one, Real.norm_eq_abs] at this
  have h2 : |dotJ v (famMean S ν θ) * dotJ w (famMean S ν θ)| ≤
      ((Fintype.card J : ℝ) * B * ‖v‖) * ((Fintype.card J : ℝ) * B * ‖w‖) := by
    rw [abs_mul]
    exact mul_le_mul (abs_dotJ_famMean_le hS ν hB0 hB θ v) (abs_dotJ_famMean_le hS ν hB0 hB θ w)
      (abs_nonneg _) (by positivity)
  unfold covQ
  calc |(∫ y, dirLoss S v y * dirLoss S w y * famDens S ν θ y ∂ν) -
        dotJ v (famMean S ν θ) * dotJ w (famMean S ν θ)|
      ≤ |∫ y, dirLoss S v y * dirLoss S w y * famDens S ν θ y ∂ν| +
        |dotJ v (famMean S ν θ) * dotJ w (famMean S ν θ)| := abs_sub _ _
    _ ≤ ((Fintype.card J : ℝ) * B * ‖v‖) * ((Fintype.card J : ℝ) * B * ‖w‖) +
        ((Fintype.card J : ℝ) * B * ‖v‖) * ((Fintype.card J : ℝ) * B * ‖w‖) := add_le_add h1 h2
    _ = 2 * ((Fintype.card J : ℝ) * B) ^ 2 * ‖v‖ * ‖w‖ := by ring

end Bounds

end Laplace.Multi
