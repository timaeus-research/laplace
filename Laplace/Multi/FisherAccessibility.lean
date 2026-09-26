/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BoundaryLayerBounds

/-!
# Fisher accessibility of boundary responses

Along the natural ray `θ − t u` towards a charged exposed face, the Fisher speed squared is the
variance `Var_{p_t}⟨u,S⟩ = Var_{p_t}(g)` of the slack `g = β − ⟨u,S⟩`. The elementary bound
`s² e^{−ts} ≤ (16/t²) e^{−ts/2}` gives `Var_{p_t}(g) ≤ 16 B_{t/2} / (A t²)`
(`raySpeedSq_le_offFaceMass`), so a polynomial tilt decay `B_{t/2} ≤ C t^{−α}` makes the Fisher
length of the tail of the ray finite and explicit:

`∫_T^∞ √(Var_{p_t}(g)) dt ≤ (8/α) √(C/A) T^{−α/2}`   (`integral_sqrt_raySpeedSq_le`).

Boundary responses with a polynomial boundary layer lie at finite Fisher distance; Astra's
one-dimensional example shows that without such a layer the distance can be infinite.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Elementary

/-- `s² e^{−ts} ≤ (16/t²) e^{−ts/2}` for `s ≥ 0`, `t > 0`. -/
theorem sq_mul_exp_neg_le {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    s ^ 2 * Real.exp (-(t * s)) ≤ 16 / t ^ 2 * Real.exp (-(t / 2 * s)) := by
  have h1 : t * s / 4 + 1 ≤ Real.exp (t * s / 4) := Real.add_one_le_exp _
  have h2 : (t * s / 4) ^ 2 ≤ Real.exp (t / 2 * s) := by
    have h3 : (t * s / 4) ^ 2 ≤ (t * s / 4 + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h4 : (t * s / 4 + 1) ^ 2 ≤ Real.exp (t * s / 4) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h5 : Real.exp (t * s / 4) ^ 2 = Real.exp (t / 2 * s) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    linarith
  have hsq : s ^ 2 ≤ 16 / t ^ 2 * Real.exp (t / 2 * s) := by
    have e : s ^ 2 = 16 / t ^ 2 * (t * s / 4) ^ 2 := by
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hE : Real.exp (-(t * s)) = Real.exp (-(t / 2 * s)) * Real.exp (-(t / 2 * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hE, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  calc s ^ 2 * Real.exp (-(t / 2 * s)) ≤
        16 / t ^ 2 * Real.exp (t / 2 * s) * Real.exp (-(t / 2 * s)) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = 16 / t ^ 2 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end Elementary

section Ray

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (θ u : J → ℝ) (β : ℝ)
include hS

omit [Nonempty X] [Nonempty J] hS in
variable (S) in
/-- The Fisher speed squared of the natural ray `θ − t u`: the variance of the sufficient
statistic `⟨u, S⟩` under the family law. -/
noncomputable def raySpeedSq (t : ℝ) : ℝ :=
  lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u)) (dirLoss S u)
    (dirLoss S u)

omit [Nonempty X] [Nonempty J] in
/-- **The Fisher speed is bounded by the second moment of the slack**, computed against `ν`. -/
theorem raySpeedSq_le_integral_sq (t : ℝ) :
    raySpeedSq S ν θ u t ≤
      ∫ x, (β - dirLoss S u x) ^ 2 * famDens S ν (θ - t • u) x ∂ν := by
  have hP : IsProbabilityMeasure
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u)) := by
    rw [familyMeasure_eq_withDensity_famDens]
    exact isProbabilityMeasure_withDensity_ofReal ν (famDens_nonneg hS ν _)
      (integrable_famDens hS ν _) (integral_famDens hS ν _)
  have h := lawCov_self_le_integral_sq
    (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u)) (bdd_dirLoss hS u) β
  refine h.trans (le_of_eq ?_)
  rw [familyMeasure_eq_withDensity_famDens,
    integral_withDensity_ofReal ν (measurable_famDens hS ν _) (famDens_nonneg hS ν _)]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

omit [Nonempty X] [Nonempty J] in
/-- **The second moment of the slack decays like `B_{t/2}/t²`**: `∫ g² p_t ≤ 16 B_{t/2}/(A t²)`. -/
theorem integral_sq_slack_le (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {t : ℝ} (ht : 0 < t) :
    ∫ x, (β - dirLoss S u x) ^ 2 * famDens S ν (θ - t • u) x ∂ν ≤
      16 / (faceMass S ν θ u β * t ^ 2) * offFaceMass S ν θ u β (t / 2) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hB := offFaceMass_nonneg hS ν θ u β t
  have hAB : 0 < faceMass S ν θ u β + offFaceMass S ν θ u β t := by linarith
  have hF := measurableSet_faceFibre hS u β
  have hmg : Measurable fun x ↦ β - dirLoss S u x := (bdd_dirLoss hS u).1.const_sub β
  have hmw : Measurable (famWeight S θ) := Real.measurable_exp.comp (bdd_dirLoss hS θ).1.neg
  -- pointwise: the integrand is `g² w e^{−tg}/(A + B_t)`
  have e : ∀ x, (β - dirLoss S u x) ^ 2 * famDens S ν (θ - t • u) x =
      (β - dirLoss S u x) ^ 2 * (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) /
        (faceMass S ν θ u β + offFaceMass S ν θ u β t) := fun x ↦ by
    rw [famDens_ray hS ν θ u β]
    ring
  simp_rw [e]
  rw [integral_div]
  -- integrability: bounded factor times the integrable off-face weight
  obtain ⟨_, K, hK⟩ := bdd_dirLoss hS u
  have hint : Integrable (fun x ↦ (β - dirLoss S u x) ^ 2 *
      (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))))) ν :=
    (integrable_offFace hS ν θ u β t).bdd_mul (hmg.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add le_rfl (hK x))) 2)
  -- the integrand vanishes on the face
  have hsplit : ∫ x, (β - dirLoss S u x) ^ 2 *
      (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ∂ν =
      ∫ x in {x | dirLoss S u x = β}ᶜ, (β - dirLoss S u x) ^ 2 *
        (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ∂ν := by
    rw [← integral_add_compl₀ hF.nullMeasurableSet hint,
      setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ by
        have hx' : dirLoss S u x = β := hx
        rw [hx', sub_self, sq, zero_mul, zero_mul], zero_add]
  -- a.e. off the face the slack is positive and the elementary bound applies
  have hmaj : ∫ x in {x | dirLoss S u x = β}ᶜ, (β - dirLoss S u x) ^ 2 *
      (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ∂ν ≤
      ∫ x in {x | dirLoss S u x = β}ᶜ, 16 / t ^ 2 *
        (famWeight S θ x * Real.exp (-(t / 2 * (β - dirLoss S u x)))) ∂ν := by
    refine integral_mono_ae hint.integrableOn
      ((integrable_offFace hS ν θ u β (t / 2)).const_mul _).integrableOn ?_
    filter_upwards [ae_restrict_of_ae hβ] with x hx
    have h := sq_mul_exp_neg_le ht (sub_nonneg.2 hx)
    calc (β - dirLoss S u x) ^ 2 * (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) =
          famWeight S θ x * ((β - dirLoss S u x) ^ 2 * Real.exp (-(t * (β - dirLoss S u x)))) := by
          ring
      _ ≤ famWeight S θ x * (16 / t ^ 2 * Real.exp (-(t / 2 * (β - dirLoss S u x)))) :=
          mul_le_mul_of_nonneg_left h (famWeight_pos θ x).le
      _ = 16 / t ^ 2 * (famWeight S θ x * Real.exp (-(t / 2 * (β - dirLoss S u x)))) := by ring
  rw [integral_const_mul] at hmaj
  have hnum : 0 ≤ ∫ x, (β - dirLoss S u x) ^ 2 *
      (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ∂ν :=
    integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _)
      (mul_nonneg (famWeight_pos θ x).le (Real.exp_pos _).le)
  calc (∫ x, (β - dirLoss S u x) ^ 2 *
        (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ∂ν) /
          (faceMass S ν θ u β + offFaceMass S ν θ u β t) ≤
      (16 / t ^ 2 * offFaceMass S ν θ u β (t / 2)) / faceMass S ν θ u β :=
        div_le_div₀ (mul_nonneg (by positivity) (offFaceMass_nonneg hS ν θ u β _))
          (by rw [hsplit]; exact hmaj) hA (by linarith)
    _ = 16 / (faceMass S ν θ u β * t ^ 2) * offFaceMass S ν θ u β (t / 2) := by
        field_simp

omit [Nonempty X] [Nonempty J] in
/-- **The Fisher speed along the ray decays with the off-face mass**:
`Var_{p_t}⟨u,S⟩ ≤ 16 B_{t/2} / (A t²)`. -/
theorem raySpeedSq_le_offFaceMass (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {t : ℝ} (ht : 0 < t) :
    raySpeedSq S ν θ u t ≤
      16 / (faceMass S ν θ u β * t ^ 2) * offFaceMass S ν θ u β (t / 2) :=
  (raySpeedSq_le_integral_sq hS ν θ u β t).trans (integral_sq_slack_le hS ν θ u β hβ hp ht)

omit [Nonempty X] [Nonempty J] in
/-- **Fisher accessibility**: a polynomial tilt decay `B_{t/2} ≤ C t^{−α}` makes the tail of the
natural ray of finite Fisher length, `∫_T^∞ √(Var_{p_t}⟨u,S⟩) dt ≤ (8/α) √(C/A) T^{−α/2}`. -/
theorem integral_sqrt_raySpeedSq_le (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {α C T : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hT : 0 < T)
    (hB : ∀ t, T ≤ t → offFaceMass S ν θ u β (t / 2) ≤ C * t ^ (-α)) :
    ∫ t in Ioi T, √(raySpeedSq S ν θ u t) ≤
      8 / α * √(C / faceMass S ν θ u β) * T ^ (-α / 2) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hpt : ∀ t, T ≤ t → √(raySpeedSq S ν θ u t) ≤
      4 * √(C / faceMass S ν θ u β) * t ^ (-1 - α / 2) := fun t htT ↦ by
    have ht : 0 < t := hT.trans_le htT
    have h1 : raySpeedSq S ν θ u t ≤ 16 / (faceMass S ν θ u β * t ^ 2) * (C * t ^ (-α)) :=
      (raySpeedSq_le_offFaceMass hS ν θ u β hβ hp ht).trans
        (mul_le_mul_of_nonneg_left (hB t htT) (by positivity))
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    have e : 16 / (faceMass S ν θ u β * t ^ 2) * (C * t ^ (-α)) =
        (4 * √(C / faceMass S ν θ u β) * t ^ (-1 - α / 2)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hC hA.le),
        ← Real.rpow_natCast (t ^ (-1 - α / 2)) 2, ← Real.rpow_mul ht.le,
        show (-1 - α / 2) * ((2 : ℕ) : ℝ) = -α + -2 by push_cast; ring, Real.rpow_add ht,
        Real.rpow_neg ht.le 2, Real.rpow_two]
      field_simp
      ring
    rw [e, Real.sqrt_sq (by positivity)]
  have hmaj : IntegrableOn (fun t ↦ 4 * √(C / faceMass S ν θ u β) * t ^ (-1 - α / 2)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hT).const_mul _
  calc ∫ t in Ioi T, √(raySpeedSq S ν θ u t) ≤
        ∫ t in Ioi T, 4 * √(C / faceMass S ν θ u β) * t ^ (-1 - α / 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun t ↦ Real.sqrt_nonneg _) hmaj
          ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun t ht ↦ hpt t (le_of_lt ht)))
    _ = 4 * √(C / faceMass S ν θ u β) * (-T ^ (-1 - α / 2 + 1) / (-1 - α / 2 + 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hT]
    _ = 8 / α * √(C / faceMass S ν θ u β) * T ^ (-α / 2) := by
        rw [show -1 - α / 2 + 1 = -α / 2 by ring]
        field_simp
        ring

end Ray

end Laplace.Multi
