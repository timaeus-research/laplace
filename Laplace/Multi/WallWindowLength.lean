/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ProfileResponse
import Laplace.Multi.ThermoLength

/-!
# A shrinking window of the data coordinate carries a fixed response geometry

For the two-monomial family `L_a(w) = w^p + a w^q` on `(0,∞)` (`0 < q < p`, Lebesgue reference
measure), the wall `a = 0` is crossed in the window `a = c t^{-σ*}`, `σ* = 1 − q/p`, and the
finite-temperature posterior of the scaled coordinate `y = t^{1/p} w` in that window is exactly the
profile law `ρ_c` (`wall_posterior_eq_profile`). Consequently the Fisher speed of the data path
`a ↦ L_a` at `a = c t^{-σ*}` is

  `g_t(a) = t² Var_{t,a}(w^q) = t^{2σ*} Var_c(y^q)`   (`fisherSpeed_twoMonoPath`),

and the thermodynamic length of the window `[c₀ t^{-σ*}, c₁ t^{-σ*}]` is **independent of `t`**:

  `∫_{c₀ t^{-σ*}}^{c₁ t^{-σ*}} √g_t(a) da = ∫_{c₀}^{c₁} √Var_c(y^q) dc`   (`wall_window_length`).

A window of the data coordinate that shrinks like `t^{-σ*}` carries a fixed, nontrivial response
geometry: the profile family's own Fisher length. This is the exact bridge between the response
geometry of the exact layer and the blow-up geometry of the singular layer (Astra, round 22).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Posterior expectations are linear in the observable: `⟨c φ⟩ = c ⟨φ⟩`. -/
theorem priorExp_const_mul (π L φ : X → ℝ) (c t : ℝ) :
    priorExp μ π L (fun x ↦ c * φ x) t = c * priorExp μ π L φ t := by
  unfold priorExp
  simp only [mul_assoc]
  rw [MeasureTheory.integral_const_mul, mul_div_assoc]

/-- Posterior expectations only depend on the observable almost everywhere. -/
theorem priorExp_congr_ae (π L : X → ℝ) {φ ψ : X → ℝ} (h : ∀ᵐ x ∂μ, φ x = ψ x) (t : ℝ) :
    priorExp μ π L φ t = priorExp μ π L ψ t := by
  unfold priorExp
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The two-monomial data path `a ↦ w^p + a w^q`. -/
noncomputable def twoMonoPath (p q : ℝ) : ℝ → ℝ → ℝ := fun a w ↦ w ^ p + a * w ^ q

/-- Its velocity `L̇_a = w^q`. -/
noncomputable def twoMonoVel (q : ℝ) : ℝ → ℝ → ℝ := fun _ w ↦ w ^ q

/-- The scaled coordinate: `(t^{1/p} w)^q = t^{q/p} w^q` for `w > 0`. -/
theorem scaled_rpow {p q t : ℝ} (ht : 0 < t) {w : ℝ} (hw : 0 < w) :
    (t ^ (1 / p) * w) ^ q = t ^ (q / p) * w ^ q := by
  rw [Real.mul_rpow (Real.rpow_pos_of_pos ht _).le hw.le, ← Real.rpow_mul ht.le,
    show 1 / p * q = q / p by ring]

/-- The mean of the wall score in the window: `⟨w^q⟩_{t, c t^{-σ*}} = t^{-q/p} ⟨y^q⟩_c`. -/
theorem priorExp_twoMonoPath_score {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q (c * t ^ (-(1 - q / p))))
        (fun w ↦ w ^ q) t = (t ^ (q / p))⁻¹ * profilePosterior p q (fun y ↦ y ^ q) c := by
  have h := wall_posterior_eq_profile (q := q) hp ht (fun y ↦ y ^ q) c
  have e : priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (fun w ↦ w ^ p + c * t ^ (-(1 - q / p)) * w ^ q) (fun w ↦ (t ^ (1 / p) * w) ^ q) t =
      t ^ (q / p) * priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
        (fun w ↦ w ^ p + c * t ^ (-(1 - q / p)) * w ^ q) (fun w ↦ w ^ q) t := by
    rw [← priorExp_const_mul]
    refine priorExp_congr_ae _ _ ?_ t
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw ↦ ?_)
    exact scaled_rpow ht hw
  rw [e] at h
  have hT : t ^ (q / p) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  unfold twoMonoPath
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hT, one_mul]

/-- The second moment of the wall score in the window. -/
theorem priorExp_twoMonoPath_score_sq {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q (c * t ^ (-(1 - q / p))))
        (fun w ↦ w ^ q * w ^ q) t =
      (t ^ (q / p))⁻¹ * (t ^ (q / p))⁻¹ * profilePosterior p q (fun y ↦ y ^ q * y ^ q) c := by
  have h := wall_posterior_eq_profile (q := q) hp ht (fun y ↦ y ^ q * y ^ q) c
  have e : priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (fun w ↦ w ^ p + c * t ^ (-(1 - q / p)) * w ^ q)
        (fun w ↦ (t ^ (1 / p) * w) ^ q * (t ^ (1 / p) * w) ^ q) t =
      (t ^ (q / p) * t ^ (q / p)) * priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
        (fun w ↦ w ^ p + c * t ^ (-(1 - q / p)) * w ^ q) (fun w ↦ w ^ q * w ^ q) t := by
    rw [← priorExp_const_mul]
    refine priorExp_congr_ae _ _ ?_ t
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw ↦ ?_)
    rw [scaled_rpow ht hw]
    ring
  rw [e] at h
  have hT : t ^ (q / p) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  unfold twoMonoPath
  rw [← h]
  field_simp

/-- **The Fisher speed in the wall window**: `g_t(c t^{-σ*}) = t^{2σ*} Var_c(y^q)`. -/
theorem fisherSpeed_twoMonoPath {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q) (twoMonoVel q) t
        (c * t ^ (-(1 - q / p))) =
      (t ^ (1 - q / p)) ^ 2 * (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
        profilePosterior p q (fun y ↦ y ^ q) c ^ 2) := by
  simp only [fisherSpeed, priorCov]
  rw [show twoMonoVel q (c * t ^ (-(1 - q / p))) = fun w ↦ w ^ q from rfl,
    priorExp_twoMonoPath_score hp ht c, priorExp_twoMonoPath_score_sq hp ht c,
    Real.rpow_sub ht, Real.rpow_one]
  have hT : t ^ (q / p) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  field_simp

/-- **The length of the wall window is the profile length, for every `t`**:
`∫_{c₀ t^{-σ*}}^{c₁ t^{-σ*}} √g_t = ∫_{c₀}^{c₁} √Var_c(y^q) dc`. -/
theorem wall_window_length {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (c₀ c₁ : ℝ) :
    ∫ a in (c₀ * t ^ (-(1 - q / p)))..(c₁ * t ^ (-(1 - q / p))),
        Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q)
          (twoMonoVel q) t a)
      = ∫ c in c₀..c₁, Real.sqrt (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
          profilePosterior p q (fun y ↦ y ^ q) c ^ 2) := by
  set σ : ℝ := 1 - q / p with hσ
  have hpos : 0 < t ^ σ := Real.rpow_pos_of_pos ht _
  have hinv : t ^ (-σ) = (t ^ σ)⁻¹ := Real.rpow_neg ht.le σ
  -- every `a` is `c t^{-σ}` with `c = a t^{σ}`
  have e : ∀ a, Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q)
      (twoMonoVel q) t a) =
      t ^ σ * Real.sqrt (profilePosterior p q (fun y ↦ y ^ q * y ^ q) (a * t ^ σ)
        - profilePosterior p q (fun y ↦ y ^ q) (a * t ^ σ) ^ 2) := fun a ↦ by
    have ha : a = (a * t ^ σ) * t ^ (-σ) := by
      rw [hinv, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
    conv_lhs => rw [ha]
    rw [fisherSpeed_twoMonoPath hp ht, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_right
    (f := fun c ↦ Real.sqrt (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2)) hpos.ne', smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hpos.ne', one_mul, hinv, mul_assoc, mul_assoc, inv_mul_cancel₀ hpos.ne',
    mul_one, mul_one]

end Laplace.Multi
