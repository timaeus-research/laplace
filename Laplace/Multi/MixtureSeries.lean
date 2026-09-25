/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.HigherResponse

/-!
# The mixture path is an entire function of the mixture weight

For bounded losses the tilted numerator is given by its Taylor series at the base point, for every
value of the tilt:

  `∫ f e^{-tuR} ν = ∑_n (−tu)^n/n! ∫ f R^n ν`   (`TiltData.hasSum_tiltNum`),

so along a mixture path `L_s = L₀ + sΔ` the partition function and every numerator are entire in
the mixture weight, with coefficients the moments of the loss contrast under the base posterior
(`TiltData.hasSum_priorZ_pathLoss`, `TiltData.hasSum_mixNum`). This is the all-orders form of the
statement that the response map along a mixture path is determined by the joint law of `(φ, Δ)`
under the base posterior; the derivative formulas of `HigherResponse` are its termwise
derivatives. The proof is dominated convergence for series
(`hasSum_integral_of_dominated_convergence`) with the exponential series as the majorant.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The exponential series in `ℝ`. -/
theorem hasSum_exp_series (x : ℝ) :
    HasSum (fun n : ℕ ↦ x ^ n / n.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- **The tilted numerator is entire in the tilt**: `∫ f e^{-tuR} ν = ∑ (−tu)^n/n! ∫ f R^n ν`. -/
theorem TiltData.hasSum_tiltNum [Nonempty X] {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t u : ℝ) :
    HasSum (fun n : ℕ ↦ (-t * u) ^ n / n.factorial * ∫ x, f x * R x ^ n * ν x ∂μ)
      (tiltNum μ ν f R t u) := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hM := h.M_nonneg
  set y : ℝ := |t * u| * M with hy
  have hy0 : 0 ≤ y := mul_nonneg (abs_nonneg _) hM
  have key := hasSum_integral_of_dominated_convergence
    (F := fun n : ℕ ↦ fun x ↦ (-t * u) ^ n / n.factorial * (f x * R x ^ n * ν x))
    (f := fun x ↦ f x * Real.exp (-(t * R x * u)) * ν x)
    (bound := fun n x ↦ y ^ n / n.factorial * (Mf * ν x)) (μ := μ) ?_ ?_ ?_ ?_ ?_
  · unfold tiltNum
    simpa only [integral_const_mul] using key
  · intro n
    exact (((hfm.mul (h.R_meas.pow_const n)).mul h.ν_meas).const_mul _).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_div, abs_pow, abs_pow, Nat.abs_cast,
      abs_of_nonneg (h.ν_nonneg x), hy, mul_pow]
    have h1 : |f x| * |R x| ^ n ≤ Mf * M ^ n :=
      mul_le_mul (hf x) (pow_le_pow_left₀ (abs_nonneg _) (h.R_bound x) n) (by positivity) hMf
    have h2 : 0 ≤ |-t * u| ^ n / (n.factorial : ℝ) := by positivity
    calc |-t * u| ^ n / (n.factorial : ℝ) * (|f x| * |R x| ^ n * ν x)
        ≤ |-t * u| ^ n / (n.factorial : ℝ) * (Mf * M ^ n * ν x) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (h.ν_nonneg x)) h2
      _ = |t * u| ^ n * M ^ n / (n.factorial : ℝ) * (Mf * ν x) := by
          rw [neg_mul, abs_neg]
          ring
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    exact (Real.summable_pow_div_factorial y).mul_right _
  · have e : (fun x ↦ ∑' n : ℕ, y ^ n / n.factorial * (Mf * ν x)) =
        fun x ↦ Real.exp y * Mf * ν x := by
      funext x
      rw [tsum_mul_right, (hasSum_exp_series y).tsum_eq]
      ring
    rw [e]
    exact h.ν_int.const_mul _
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have hs := (hasSum_exp_series (-(t * R x * u))).mul_right (f x * ν x)
    have e : (fun n : ℕ ↦ (-(t * R x * u)) ^ n / n.factorial * (f x * ν x)) =
        fun n : ℕ ↦ (-t * u) ^ n / n.factorial * (f x * R x ^ n * ν x) := by
      funext n
      rw [show -(t * R x * u) = (-t * u) * R x by ring, mul_pow]
      ring
    rw [e, show Real.exp (-(t * R x * u)) * (f x * ν x) =
      f x * Real.exp (-(t * R x * u)) * ν x by ring] at hs
    exact hs

/-- **The mixture numerators are entire in the mixture weight**:
`∫ φ e^{-tL_s} π = ∑ (−ts)^n/n! ∫ φ Δ^n e^{-tL₀} π`. -/
theorem TiltData.hasSum_mixNum [Nonempty X] {π L₀ Δ : X → ℝ} {t M : ℝ}
    (h : TiltData μ (baseWeight π L₀ t) Δ M) {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ}
    (hφ : ∀ x, |φ x| ≤ Mφ) (s : ℝ) :
    HasSum (fun n : ℕ ↦ (-t * s) ^ n / n.factorial *
        ∫ x, φ x * Δ x ^ n * Real.exp (-(t * L₀ x)) * π x ∂μ)
      (∫ x, φ x * Real.exp (-(t * pathLoss L₀ Δ s x)) * π x ∂μ) := by
  rw [mixNum_eq_tiltNum]
  have := h.hasSum_tiltNum hφm hφ t s
  simpa only [baseWeight, mul_assoc] using this

/-- **The partition function is entire along the mixture path**:
`Z_t(L_s) = ∑ (−ts)^n/n! ∫ Δ^n e^{-tL₀} π` — the exponential generating function of the moments
of the loss contrast under the base posterior. -/
theorem TiltData.hasSum_priorZ_pathLoss [Nonempty X] {π L₀ Δ : X → ℝ} {t M : ℝ}
    (h : TiltData μ (baseWeight π L₀ t) Δ M) (s : ℝ) :
    HasSum (fun n : ℕ ↦ (-t * s) ^ n / n.factorial *
        ∫ x, Δ x ^ n * Real.exp (-(t * L₀ x)) * π x ∂μ)
      (priorZ μ π (pathLoss L₀ Δ s) t) := by
  have := h.hasSum_mixNum (φ := fun _ ↦ (1 : ℝ)) measurable_const (Mφ := 1) (fun _ ↦ by simp) s
  simpa only [one_mul, priorZ] using this

end Laplace.Multi
