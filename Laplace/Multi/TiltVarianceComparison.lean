/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.QuadraticInformationBound
import Laplace.Multi.BoundaryBlowup
import Laplace.Multi.EntropyProjection

/-!
# Variances under bounded tilts

If `|g| ≤ c` then the tilt `Q.tilted g` has density in `[e^{−2c}, e^{2c}]` with respect to `Q`, and
since a variance is the infimum of second moments about a centre,

  `e^{−2c} Var_Q f ≤ Var_{Q.tilted g} f ≤ e^{2c} Var_Q f`
  (`lawCov_tilted_le`, `le_lawCov_tilted`).

This is the "bounded tangential tilt" step of the facet accessibility theorem: along a path
approaching a facet with convergent tangential part, the normal variance is uniformly comparable
to the normal variance of the fixed reference ray.
-/

open MeasureTheory Real

namespace Laplace.Multi

section Tilt

variable {X : Type*} [MeasurableSpace X] (Q : Measure X) [IsProbabilityMeasure Q]

/-- The normaliser of a tilt by `g` with `|g| ≤ c` lies in `[e^{−c}, e^{c}]`. -/
theorem exp_neg_le_integral_exp {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) : exp (-c) ≤ ∫ x, exp (g x) ∂Q := by
  have hint : Integrable (fun x ↦ exp (g x)) Q := integrable_exp_of_bdd Q ⟨hg, c, hc⟩
  calc exp (-c) = ∫ _, exp (-c) ∂Q := by simp
    _ ≤ ∫ x, exp (g x) ∂Q := by
      refine integral_mono (integrable_const _) hint fun x ↦ exp_le_exp.2 ?_
      have := (abs_le.1 (hc x)).1
      linarith

theorem integral_exp_le_exp {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) : ∫ x, exp (g x) ∂Q ≤ exp c := by
  have hint : Integrable (fun x ↦ exp (g x)) Q := integrable_exp_of_bdd Q ⟨hg, c, hc⟩
  calc ∫ x, exp (g x) ∂Q ≤ ∫ _, exp c ∂Q :=
        integral_mono hint (integrable_const _) fun x ↦ exp_le_exp.2 (abs_le.1 (hc x)).2
    _ = exp c := by simp

/-- The tilt density is bounded above by `e^{2c}`. -/
theorem tilt_density_le {g : X → ℝ} (hg : Measurable g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) (x : X) :
    exp (g x) / ∫ y, exp (g y) ∂Q ≤ exp (2 * c) := by
  have hZ := exp_neg_le_integral_exp Q hg hc
  rw [div_le_iff₀ (lt_of_lt_of_le (exp_pos _) hZ)]
  calc exp (g x) ≤ exp c := exp_le_exp.2 (abs_le.1 (hc x)).2
    _ = exp (2 * c) * exp (-c) := by rw [← exp_add]; ring_nf
    _ ≤ exp (2 * c) * ∫ y, exp (g y) ∂Q := by gcongr

/-- The tilt density is bounded below by `e^{−2c}`. -/
theorem le_tilt_density {g : X → ℝ} (hg : Measurable g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) (x : X) :
    exp (-(2 * c)) ≤ exp (g x) / ∫ y, exp (g y) ∂Q := by
  have hZ := integral_exp_le_exp Q hg hc
  have hZpos : 0 < ∫ y, exp (g y) ∂Q :=
    lt_of_lt_of_le (exp_pos _) (exp_neg_le_integral_exp Q hg hc)
  rw [le_div_iff₀ hZpos]
  calc exp (-(2 * c)) * ∫ y, exp (g y) ∂Q ≤ exp (-(2 * c)) * exp c := by gcongr
    _ = exp (-c) := by rw [← exp_add]; ring_nf
    _ ≤ exp (g x) := exp_le_exp.2 (abs_le.1 (hc x)).1

/-- Nonnegative integrals grow by at most `e^{2c}` under a tilt by `|g| ≤ c`. -/
theorem integral_tilted_le_of_nonneg {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) {φ : X → ℝ} (hφ : Bdd φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫ x, φ x ∂(Q.tilted g) ≤ exp (2 * c) * ∫ x, φ x ∂Q := by
  rw [integral_tilted, ← integral_const_mul]
  refine integral_mono ?_ ((integrable_of_bdd_prob Q hφ).const_mul _) fun x ↦ ?_
  · refine (integrable_of_bdd_prob Q hφ).bdd_mul (c := exp (2 * c)) ?_ (ae_of_all _ fun x ↦ ?_)
    · exact (hg.exp.div_const _).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (exp_pos _).le
        (lt_of_lt_of_le (exp_pos _) (exp_neg_le_integral_exp Q hg hc)).le)]
      exact tilt_density_le Q hg hc x
  · simp only [smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (tilt_density_le Q hg hc x) (hφ0 x)

/-- Nonnegative integrals shrink by at most `e^{−2c}` under a tilt by `|g| ≤ c`. -/
theorem le_integral_tilted_of_nonneg {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) {φ : X → ℝ} (hφ : Bdd φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    exp (-(2 * c)) * ∫ x, φ x ∂Q ≤ ∫ x, φ x ∂(Q.tilted g) := by
  rw [integral_tilted, ← integral_const_mul]
  refine integral_mono ((integrable_of_bdd_prob Q hφ).const_mul _) ?_ fun x ↦ ?_
  · refine (integrable_of_bdd_prob Q hφ).bdd_mul (c := exp (2 * c)) ?_ (ae_of_all _ fun x ↦ ?_)
    · exact (hg.exp.div_const _).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (exp_pos _).le
        (lt_of_lt_of_le (exp_pos _) (exp_neg_le_integral_exp Q hg hc)).le)]
      exact tilt_density_le Q hg hc x
  · simp only [smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (le_tilt_density Q hg hc x) (hφ0 x)

/-- **Variance comparison under a bounded tilt (upper)**: `Var_{Q.tilted g} f ≤ e^{2c} Var_Q f`. -/
theorem lawCov_tilted_le {g : X → ℝ} (hg : Bdd g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) {f : X → ℝ}
    (hf : Bdd f) :
    lawCov (Q.tilted g) f f ≤ exp (2 * c) * lawCov Q f f := by
  have hP : IsProbabilityMeasure (Q.tilted g) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd Q hg)
  have hsq : Bdd fun x ↦ (f x - ∫ y, f y ∂Q) * (f x - ∫ y, f y ∂Q) :=
    (hf.sub (Bdd.const _)).mul (hf.sub (Bdd.const _))
  calc lawCov (Q.tilted g) f f
      ≤ ∫ x, (f x - ∫ y, f y ∂Q) * (f x - ∫ y, f y ∂Q) ∂(Q.tilted g) :=
        lawCov_self_le_integral_sq _ hf _
    _ ≤ exp (2 * c) * ∫ x, (f x - ∫ y, f y ∂Q) * (f x - ∫ y, f y ∂Q) ∂Q :=
        integral_tilted_le_of_nonneg Q hg.1 hc hsq fun x ↦ mul_self_nonneg _
    _ = exp (2 * c) * lawCov Q f f := by rw [lawCov_eq_integral_centred Q hf hf]

/-- **Variance comparison under a bounded tilt (lower)**: `e^{−2c} Var_Q f ≤ Var_{Q.tilted g} f`. -/
theorem le_lawCov_tilted {g : X → ℝ} (hg : Bdd g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) {f : X → ℝ}
    (hf : Bdd f) :
    exp (-(2 * c)) * lawCov Q f f ≤ lawCov (Q.tilted g) f f := by
  have hP : IsProbabilityMeasure (Q.tilted g) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd Q hg)
  have hsq : Bdd fun x ↦ (f x - ∫ y, f y ∂(Q.tilted g)) * (f x - ∫ y, f y ∂(Q.tilted g)) :=
    (hf.sub (Bdd.const _)).mul (hf.sub (Bdd.const _))
  calc exp (-(2 * c)) * lawCov Q f f
      ≤ exp (-(2 * c)) *
          ∫ x, (f x - ∫ y, f y ∂(Q.tilted g)) * (f x - ∫ y, f y ∂(Q.tilted g)) ∂Q :=
        mul_le_mul_of_nonneg_left (lawCov_self_le_integral_sq _ hf _) (exp_pos _).le
    _ ≤ ∫ x, (f x - ∫ y, f y ∂(Q.tilted g)) * (f x - ∫ y, f y ∂(Q.tilted g)) ∂(Q.tilted g) :=
        le_integral_tilted_of_nonneg Q hg.1 hc hsq fun x ↦ mul_self_nonneg _
    _ = lawCov (Q.tilted g) f f := by rw [lawCov_eq_integral_centred _ hf hf]

end Tilt

end Laplace.Multi
