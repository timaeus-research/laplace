/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib

/-!
# Renormalised limits of radial lengths with a `log log` correction

If a speed `f` satisfies `f(u) = A − B/log u + O(1/log² u)` on `[u₀, ∞)`, then the length
`∫_{u₀}^t f(u)/u du` has the expansion `A log t − B log log t + K + o(1)`
(`tendsto_renormalised_length`). This is the analytic engine behind "thermodynamic length detects
multiplicity": for a state density with exponents `(λ, m)` the radial speed is
`u√Var_u = √λ − (m−1)/(2√λ log u) + O(1/log² u)`, so the featureless-line length is
`√λ log t − ((m−1)/(2√λ)) log log t + K + o(1)`.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-- The antiderivative of `(A − B/log u)/u`. -/
theorem hasDerivAt_log_sub_loglog (A B : ℝ) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun u ↦ A * Real.log u - B * Real.log (Real.log u))
      ((A - B / Real.log u) / u) u := by
  have hu0 : u ≠ 0 := by positivity
  have hlog : 0 < Real.log u := Real.log_pos hu
  have h1 := (Real.hasDerivAt_log hu0).const_mul A
  have h2 := ((Real.hasDerivAt_log hu0).log hlog.ne').const_mul B
  refine (h1.sub h2).congr_deriv ?_
  field_simp

/-- `u ↦ C/(u log² u)` is integrable on `(u₀, ∞)` for `u₀ > 1`. -/
theorem integrableOn_inv_mul_log_sq {u₀ C : ℝ} (hu₀ : 1 < u₀) (hC : 0 ≤ C) :
    IntegrableOn (fun u ↦ C / (u * Real.log u ^ 2)) (Ioi u₀) := by
  have hderiv : ∀ x ∈ Ici u₀,
      HasDerivAt (fun u ↦ -C / Real.log u) (C / (x * Real.log x ^ 2)) x := by
    intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le hu₀ hx
    have hx0 : x ≠ 0 := by positivity
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have h := ((Real.hasDerivAt_log hx0).inv hlog.ne').const_mul (-C)
    refine h.congr_deriv ?_
    field_simp
  have hlim : Tendsto (fun u ↦ -C / Real.log u) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (-C)
    simpa [div_eq_mul_inv, Function.comp_def] using this
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx ↦ by
    have hx1 : 1 < x := lt_trans hu₀ hx
    have := Real.log_pos hx1
    positivity) hlim

/-- **Renormalised radial length**: `f = A − B/log u + O(1/log² u)` gives
`∫_{u₀}^t f/u = A log t − B log log t + K + o(1)`. -/
theorem tendsto_renormalised_length {f : ℝ → ℝ} {u₀ A B C : ℝ} (hu₀ : 1 < u₀)
    (hf : ContinuousOn f (Ici u₀))
    (hb : ∀ u, u₀ ≤ u → |f u - (A - B / Real.log u)| ≤ C / Real.log u ^ 2) :
    ∃ K, Tendsto (fun t ↦ (∫ u in u₀..t, f u / u) -
      (A * Real.log t - B * Real.log (Real.log t))) atTop (𝓝 K) := by
  have hC : 0 ≤ C := by
    have := hb u₀ le_rfl
    have hl : 0 < Real.log u₀ ^ 2 := by have := Real.log_pos hu₀; positivity
    by_contra hneg
    push Not at hneg
    have : C / Real.log u₀ ^ 2 < 0 := div_neg_of_neg_of_pos hneg hl
    linarith [abs_nonneg (f u₀ - (A - B / Real.log u₀))]
  -- the remainder
  set r : ℝ → ℝ := fun u ↦ (f u - (A - B / Real.log u)) / u with hr
  have hrc : ContinuousOn r (Ici u₀) := by
    refine ContinuousOn.div (hf.sub (continuousOn_const.sub (continuousOn_const.div
      (Real.continuousOn_log.mono fun x hx ↦ ?_) fun x hx ↦ ?_))) continuousOn_id fun x hx ↦ ?_
    · exact (lt_trans zero_lt_one (lt_of_lt_of_le hu₀ hx)).ne'
    · exact (Real.log_pos (lt_of_lt_of_le hu₀ hx)).ne'
    · exact (lt_trans zero_lt_one (lt_of_lt_of_le hu₀ hx)).ne'
  have hrb : ∀ u, u₀ ≤ u → |r u| ≤ C / (u * Real.log u ^ 2) := fun u hu ↦ by
    have hu0 : 0 < u := lt_trans zero_lt_one (lt_of_lt_of_le hu₀ hu)
    rw [hr]
    simp only
    have hl : 0 < Real.log u ^ 2 := by have := Real.log_pos (lt_of_lt_of_le hu₀ hu); positivity
    rw [abs_div, abs_of_pos hu0, div_le_div_iff₀ hu0 (by positivity)]
    have := hb u hu
    calc |f u - (A - B / Real.log u)| * (u * Real.log u ^ 2)
        = (|f u - (A - B / Real.log u)| * Real.log u ^ 2) * u := by ring
      _ ≤ (C / Real.log u ^ 2 * Real.log u ^ 2) * u := by gcongr
      _ = C * u := by
        have hl0 : Real.log u ≠ 0 := (Real.log_pos (lt_of_lt_of_le hu₀ hu)).ne'
        field_simp
  have hri : IntegrableOn r (Ioi u₀) := by
    refine (integrableOn_inv_mul_log_sq hu₀ hC).mono'
      ((hrc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu ↦ ?_)
    rw [Real.norm_eq_abs]
    exact hrb u (le_of_lt hu)
  have hconv := intervalIntegral_tendsto_integral_Ioi u₀ hri (tendsto_id (x := atTop))
  refine ⟨(∫ u in Ioi u₀, r u) - (A * Real.log u₀ - B * Real.log (Real.log u₀)),
    (hconv.sub_const _).congr' ?_⟩
  filter_upwards [eventually_ge_atTop u₀] with t ht
  simp only [id_eq]
  -- split the integral
  have hIcc : uIcc u₀ t = Icc u₀ t := uIcc_of_le ht
  have hg : ∀ x ∈ uIcc u₀ t, HasDerivAt (fun u ↦ A * Real.log u - B * Real.log (Real.log u))
      ((A - B / Real.log x) / x) x := fun x hx ↦ by
    rw [hIcc] at hx
    exact hasDerivAt_log_sub_loglog A B (lt_of_lt_of_le hu₀ hx.1)
  have hgc : ContinuousOn (fun u ↦ (A - B / Real.log u) / u) (uIcc u₀ t) := by
    rw [hIcc]
    refine ContinuousOn.div (continuousOn_const.sub (continuousOn_const.div
      (Real.continuousOn_log.mono fun x hx ↦ ?_) fun x hx ↦ ?_)) continuousOn_id fun x hx ↦ ?_
    · exact (lt_trans zero_lt_one (lt_of_lt_of_le hu₀ hx.1)).ne'
    · exact (Real.log_pos (lt_of_lt_of_le hu₀ hx.1)).ne'
    · exact (lt_trans zero_lt_one (lt_of_lt_of_le hu₀ hx.1)).ne'
  have hgi : IntervalIntegrable (fun u ↦ (A - B / Real.log u) / u) volume u₀ t :=
    hgc.intervalIntegrable
  have hri' : IntervalIntegrable r volume u₀ t := by
    refine (hrc.mono ?_).intervalIntegrable
    rw [hIcc]
    exact fun x hx ↦ hx.1
  have hsplit : (∫ u in u₀..t, f u / u) = (∫ u in u₀..t, r u) +
      ∫ u in u₀..t, (A - B / Real.log u) / u := by
    rw [← integral_add hri' hgi]
    refine integral_congr fun u hu ↦ ?_
    rw [hIcc] at hu
    have hu0 : u ≠ 0 := (lt_trans zero_lt_one (lt_of_lt_of_le hu₀ hu.1)).ne'
    simp only [hr]
    field_simp
    ring
  rw [hsplit, integral_eq_sub_of_hasDerivAt hg hgi]
  ring

end Laplace.Multi
