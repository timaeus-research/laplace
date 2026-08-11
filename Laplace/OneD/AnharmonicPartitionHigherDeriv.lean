/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicGibbsObservableMonomials

/-!
# Higher `h`-derivatives of the anharmonic perturbed partition function

For the 1D anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`
(discriminant `α² < 3λγ`) under the linear perturbation `A(x) = x`,
the perturbed partition function is
`Z(h) = ∫ exp(-t·(L(x) + h·x)) dx`. The `GibbsRegularity` instance
proved its first `h`-derivative at `h = 0`. This file proves the
general iterated-derivative *step*: for every `n : ℕ`,
\[
  \frac{d}{dh}\Big|_{h=0} \int (-(t x))^n\, e^{-t(L(x)+hx)}\,dx
    = \int (-(t x))^{n+1}\, e^{-t L(x)}\,dx .
\]
The `n`-th member is the integrand of the `n`-th `h`-derivative of
`Z`; the `n = 1` and `n = 2` instances are the second and third
`h`-derivatives of `Z` at `h = 0` (named below), which feed the
flow-equation / fourth-cumulant identity.

The proof mirrors the `partition_hasDerivAt` field of
`Threepoint.anharmonic_id_gibbsRegularity`, with the constant-in-`h`
factor `(-(t x))^n` multiplied into the integrand. The dominator on
`|h| < 1` is `t^(n+1)·exp(t/(2c))·|x|^(n+1)·exp(-(t/2)·L)`, integrable
via the general `integrable_abs_pow_mul_exp_neg_t_anharmonic`.
-/

open MeasureTheory Topology

namespace Laplace.OneD

/-- **General iterated-derivative step for the anharmonic perturbed
partition.** For every `n : ℕ`, the `h`-derivative at `h = 0` of
`∫ (-(t x))^n · exp(-t(L + h x))` is `∫ (-(t x))^(n+1) · exp(-t L)`. -/
theorem anharmonic_partition_deriv_step
    {lam alpha gamma t : ℝ} (n : ℕ)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    HasDerivAt
      (fun h : ℝ => ∫ x : ℝ, (-(t * x)) ^ n *
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
      (∫ x : ℝ, (-(t * x)) ^ (n + 1) *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
      0 := by
  obtain ⟨c, hc_pos, h_coerc⟩ :=
    anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds 0 zero_lt_one
  -- AE strong measurability of `F h` in `x`, for all `h`.
  have hF_meas : ∀ᶠ h in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun x : ℝ => (-(t * x)) ^ n *
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
      (volume : Measure ℝ) := by
    refine Filter.Eventually.of_forall (fun h => ?_)
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul (by fun_prop)
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    unfold anharmonicPotential
    fun_prop
  -- Integrability of `F 0`.
  have hF_int : Integrable
      (fun x : ℝ => (-(t * x)) ^ n *
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x))))
      (volume : Measure ℝ) := by
    have h_abs :=
      (integrable_abs_pow_mul_exp_neg_t_anharmonic n hlam hgamma hdisc ht).const_mul
        (t ^ n)
    refine h_abs.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul (by fun_prop)
      apply Real.continuous_exp.comp
      apply Continuous.neg
      apply Continuous.mul continuous_const
      unfold anharmonicPotential
      fun_prop
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
        abs_of_pos (Real.exp_pos _)]
      have hexp :
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x)))
            = Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
        congr 1; ring
      rw [hexp, abs_mul, abs_of_pos ht, mul_pow]
      exact le_of_eq (by ring)
  -- AE strong measurability of `F' 0`.
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => (-(t * x)) ^ (n + 1) *
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x))))
      (volume : Measure ℝ) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul (by fun_prop)
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    unfold anharmonicPotential
    fun_prop
  -- Dominator: `t^(n+1)·exp(t/(2c))·|x|^(n+1)·exp(-(t/2)·L)`.
  set bound : ℝ → ℝ :=
    fun x => t ^ (n + 1) * Real.exp (t / (2 * c)) *
      (|x| ^ (n + 1) * Real.exp (-((t / 2) *
        anharmonicPotential lam alpha gamma x))) with hbound_def
  have h_bound_int : Integrable bound := by
    have ht_half : 0 < t / 2 := by linarith
    have h_abs :=
      integrable_abs_pow_mul_exp_neg_t_anharmonic (n + 1) hlam hgamma hdisc ht_half
    have h_total :=
      h_abs.const_mul (t ^ (n + 1) * Real.exp (t / (2 * c)))
    refine h_total.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hbound_def]
  -- Pointwise bound `‖F'(h, x)‖ ≤ bound x` for `|h| < 1`.
  have h_F'_bound : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Metric.ball (0 : ℝ) 1,
      ‖(-(t * x)) ^ (n + 1) *
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x)))‖
        ≤ bound x := by
    refine Filter.Eventually.of_forall fun x h hx => ?_
    have hh_lt : |h| < 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
      exact hx
    -- Reuse the n=0 pointwise bound on the single `(-t·x)·exp` factor.
    have hv := anharmonic_perturbed_pointwise_bound ht hc_pos h_coerc h x hh_lt
    -- Rewrite `(-(t·x))^(n+1)·exp = (-(t·x))^n · ((-t·x)·exp)`.
    have h_rewrite :
        (-(t * x)) ^ (n + 1) *
            Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x)))
          = (-(t * x)) ^ n *
            ((-t * x) *
              Real.exp (-(t *
                (anharmonicPotential lam alpha gamma x + h * x)))) := by
      rw [pow_succ]; ring
    rw [h_rewrite, norm_mul, Real.norm_eq_abs, abs_pow, abs_neg, abs_mul,
      abs_of_pos ht]
    have hxn_nn : 0 ≤ (t * |x|) ^ n := pow_nonneg (by positivity) n
    calc (t * |x|) ^ n *
            ‖(-t * x) *
              Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x)))‖
          ≤ (t * |x|) ^ n *
            (t * Real.exp (t / (2 * c)) *
              (|x| * Real.exp (-((t / 2) *
                anharmonicPotential lam alpha gamma x)))) :=
            mul_le_mul_of_nonneg_left hv hxn_nn
      _ = bound x := by rw [hbound_def, mul_pow]; ring
  -- Pointwise differentiability of `F` at every `h` in the ball.
  have h_diff : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt
        (fun h : ℝ => (-(t * x)) ^ n *
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
        ((-(t * x)) ^ (n + 1) *
          Real.exp (-(t *
            (anharmonicPotential lam alpha gamma x + h * x)))) h := by
    refine Filter.Eventually.of_forall fun x h _ => ?_
    have hpw :=
      (anharmonic_perturbed_pointwise_hasDerivAt lam alpha gamma t h x).const_mul
        ((-(t * x)) ^ n)
    convert hpw using 1
    rw [pow_succ]; ring
  -- Apply the dominated-differentiation theorem.
  have key :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ)) hs hF_meas hF_int hF'_meas h_F'_bound
      h_bound_int h_diff
  -- Rewrite the derivative integrand to drop the `+ 0 · x` term.
  have h_rhs_eq :
      (∫ x : ℝ, (-(t * x)) ^ (n + 1) *
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x))))
        = ∫ x : ℝ, (-(t * x)) ^ (n + 1) *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    congr 2; ring
  rw [← h_rhs_eq]
  exact key.2

/-- **Second `h`-derivative of `Z` at `h = 0`.** The `h`-derivative at
`h = 0` of the first-derivative integral
`∫ (-(t x)) · exp(-t(L + h x))` is `∫ (t x)² · exp(-t L)`. (Instance of
`anharmonic_partition_deriv_step` at `n = 1`, with `(-(t x))² = (t x)²`.) -/
theorem anharmonic_partition_secondDeriv
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    HasDerivAt
      (fun h : ℝ => ∫ x : ℝ, (-(t * x)) ^ 1 *
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
      (∫ x : ℝ, (t * x) ^ 2 *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
      0 := by
  have h := anharmonic_partition_deriv_step 1 hlam hgamma hdisc ht
  have heq : (∫ x : ℝ, (-(t * x)) ^ (1 + 1) *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
      = ∫ x : ℝ, (t * x) ^ 2 *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
    congr 1; funext x; congr 1; ring
  rwa [heq] at h

/-- **Third `h`-derivative of `Z` at `h = 0`.** The `h`-derivative at
`h = 0` of the second-derivative integral
`∫ (-(t x))² · exp(-t(L + h x))` is `∫ -(t x)³ · exp(-t L)` (the
negative third moment). (Instance at `n = 2`.) -/
theorem anharmonic_partition_thirdDeriv
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    HasDerivAt
      (fun h : ℝ => ∫ x : ℝ, (-(t * x)) ^ 2 *
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
      (∫ x : ℝ, -(t * x) ^ 3 *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
      0 := by
  have h := anharmonic_partition_deriv_step 2 hlam hgamma hdisc ht
  have heq : (∫ x : ℝ, (-(t * x)) ^ (2 + 1) *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
      = ∫ x : ℝ, -(t * x) ^ 3 *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
    congr 1; funext x; congr 1; ring
  rwa [heq] at h

end Laplace.OneD
