/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicPartitionHigherDeriv

/-!
# General-`h` iterated derivatives of the anharmonic perturbed partition

The companion file `AnharmonicPartitionHigherDeriv.lean` proved the
iterated-derivative *step* at the single point `h = 0`. As GPT-5.5 Pro
observed, the `h = 0` form gives the derivative of each member of the
weighted-partition family `G n h = ∫ (-(t x))^n e^{-t(L+hx)}`, but is not
by itself enough to *chain* into the genuine higher derivatives of
`Z = G 0`. This file proves the **local-in-`h`** step — for every `n` and
every `h` with `|h| < 1`,
\[
  \frac{d}{dh}\, G_n(h) = G_{n+1}(h),
\]
and then chains it through `iteratedDeriv` to identify
\[
  Z''(0) = \int (t x)^2 e^{-tL},\qquad Z'''(0) = \int -(t x)^3 e^{-tL}.
\]

The analytic core is the same dominated-differentiation argument as the
`h = 0` case; the only new ingredients are (i) `Metric.ball 0 1` is a
neighbourhood of any interior `h₀`, and (ii) integrability of the family
at a *nonzero* centre `h₀`, which needs the bare-exponential domination
bound `anharmonic_perturbed_exp_le` proved below.
-/

open MeasureTheory Topology

namespace Laplace.OneD

/-- The `n`-weighted perturbed partition integrand integral
`G n h = ∫ (-(t x))^n e^{-t(L(x)+hx)}`. `G 0` is the perturbed partition
function `Z`. -/
noncomputable def weightedPartition (lam alpha gamma t : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  ∫ x : ℝ, (-(t * x)) ^ n *
    Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x)))

/-- Bare-exponential domination bound: for `|h| < 1`,
`exp(-t(L + h x)) ≤ exp(t/(2c)) · exp(-(t/2) L)`. The exponent half of
`anharmonic_perturbed_pointwise_bound`, without the `(-t x)` weight. -/
theorem anharmonic_perturbed_exp_le
    {lam alpha gamma t c : ℝ} (ht : 0 < t) (hc_pos : 0 < c)
    (h_coerc : ∀ x : ℝ, c * x ^ 2 ≤ anharmonicPotential lam alpha gamma x)
    (h x : ℝ) (hh : |h| < 1) :
    Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x)))
      ≤ Real.exp (t / (2 * c)) *
          Real.exp (-((t / 2) * anharmonicPotential lam alpha gamma x)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : -(t * (h * x)) ≤ t * |x| := by
    have h_abs_hx_le : |h * x| ≤ |x| := by
      rw [abs_mul]
      have hhx_le : |h| * |x| ≤ 1 * |x| :=
        mul_le_mul_of_nonneg_right hh.le (abs_nonneg x)
      simpa using hhx_le
    have h_neg_le_abs : -(t * (h * x)) ≤ |t * (h * x)| := neg_le_abs _
    rw [abs_mul, abs_of_pos ht] at h_neg_le_abs
    have : t * |h * x| ≤ t * |x| := mul_le_mul_of_nonneg_left h_abs_hx_le ht.le
    linarith
  have h2 : t * |x| ≤ t * c / 2 * x ^ 2 + t / (2 * c) :=
    ResolutionCommon.amgm_t_abs_x t c ht hc_pos x
  have h3 : t * c / 2 * x ^ 2 ≤ t / 2 * anharmonicPotential lam alpha gamma x := by
    have hcoerc := h_coerc x
    have ht2_nn : 0 ≤ t / 2 := by linarith
    nlinarith [hcoerc, ht2_nn]
  linarith

/-- Integrability of the weighted perturbed integrand at any centre `h₀`
with `|h₀| < 1`. -/
theorem integrable_weightedPartition_integrand
    {lam alpha gamma t : ℝ} (n : ℕ)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    {h₀ : ℝ} (hh₀ : |h₀| < 1) :
    Integrable (fun x : ℝ => (-(t * x)) ^ n *
      Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h₀ * x)))) := by
  obtain ⟨c, hc_pos, h_coerc⟩ :=
    anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  have ht_half : 0 < t / 2 := by linarith
  have hdom :=
    ((integrable_abs_pow_mul_exp_neg_t_anharmonic n hlam hgamma hdisc ht_half).const_mul
      (t ^ n * Real.exp (t / (2 * c))))
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul (by fun_prop)
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    unfold anharmonicPotential
    fun_prop
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_mul, abs_of_pos ht,
      abs_of_pos (Real.exp_pos _)]
    have hexple := anharmonic_perturbed_exp_le ht hc_pos h_coerc h₀ x hh₀
    calc (t * |x|) ^ n *
            Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h₀ * x)))
          ≤ (t * |x|) ^ n *
            (Real.exp (t / (2 * c)) *
              Real.exp (-((t / 2) * anharmonicPotential lam alpha gamma x))) :=
            mul_le_mul_of_nonneg_left hexple (pow_nonneg (by positivity) n)
      _ = t ^ n * Real.exp (t / (2 * c)) *
            (|x| ^ n *
              Real.exp (-((t / 2) * anharmonicPotential lam alpha gamma x))) := by
            rw [mul_pow]; ring

/-- **General-`h` iterated-derivative step.** For every `n : ℕ` and every
`h₀` with `|h₀| < 1`,
`HasDerivAt (G n) (G (n+1) h₀) h₀`, i.e. the `h`-derivative of
`∫ (-(t x))^n e^{-t(L+hx)}` at `h₀` is `∫ (-(t x))^(n+1) e^{-t(L+h₀ x)}`. -/
theorem weightedPartition_hasDerivAt
    {lam alpha gamma t : ℝ} (n : ℕ)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    {h₀ : ℝ} (hh₀ : |h₀| < 1) :
    HasDerivAt (weightedPartition lam alpha gamma t n)
      (weightedPartition lam alpha gamma t (n + 1) h₀) h₀ := by
  obtain ⟨c, hc_pos, h_coerc⟩ :=
    anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  -- `ball 0 1` is a neighbourhood of the interior point `h₀`.
  have hh₀_mem : h₀ ∈ Metric.ball (0 : ℝ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hh₀
  have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 h₀ := Metric.isOpen_ball.mem_nhds hh₀_mem
  -- AE strong measurability of `F h` for all `h`.
  have hF_meas : ∀ᶠ h in 𝓝 h₀, AEStronglyMeasurable
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
  -- Integrability of `F` at the centre `h₀`.
  have hF_int := integrable_weightedPartition_integrand n hlam hgamma hdisc ht hh₀
  -- AE strong measurability of `F'` at `h₀`.
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => (-(t * x)) ^ (n + 1) *
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h₀ * x))))
      (volume : Measure ℝ) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul (by fun_prop)
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    unfold anharmonicPotential
    fun_prop
  -- Dominator.
  set bound : ℝ → ℝ :=
    fun x => t ^ (n + 1) * Real.exp (t / (2 * c)) *
      (|x| ^ (n + 1) * Real.exp (-((t / 2) *
        anharmonicPotential lam alpha gamma x))) with hbound_def
  have h_bound_int : Integrable bound := by
    have ht_half : 0 < t / 2 := by linarith
    have h_abs :=
      integrable_abs_pow_mul_exp_neg_t_anharmonic (n + 1) hlam hgamma hdisc ht_half
    have h_total := h_abs.const_mul (t ^ (n + 1) * Real.exp (t / (2 * c)))
    refine h_total.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hbound_def]
  -- Pointwise bound `‖F'(h, x)‖ ≤ bound x` for `h ∈ ball 0 1`.
  have h_F'_bound : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Metric.ball (0 : ℝ) 1,
      ‖(-(t * x)) ^ (n + 1) *
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x)))‖
        ≤ bound x := by
    refine Filter.Eventually.of_forall fun x h hx => ?_
    have hh_lt : |h| < 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
      exact hx
    have hv := anharmonic_perturbed_pointwise_bound ht hc_pos h_coerc h x hh_lt
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
  -- Pointwise differentiability.
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
  have key :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ)) hs hF_meas hF_int hF'_meas h_F'_bound
      h_bound_int h_diff
  exact key.2

/-- The derivative-equation form: for `|h| < 1`,
`deriv (G n) h = G (n+1) h`. -/
theorem weightedPartition_deriv
    {lam alpha gamma t : ℝ} (n : ℕ)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t)
    {h : ℝ} (hh : |h| < 1) :
    deriv (weightedPartition lam alpha gamma t n) h
      = weightedPartition lam alpha gamma t (n + 1) h :=
  (weightedPartition_hasDerivAt n hlam hgamma hdisc ht hh).deriv

/-- The iterated derivative of `Z = G 0` agrees with `G k` on `ball 0 1`:
for every `k : ℕ` and `|h| < 1`,
`iteratedDeriv k (G 0) h = G k h`. -/
theorem iteratedDeriv_weightedPartition_zero
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    ∀ (k : ℕ) {h : ℝ}, |h| < 1 →
      iteratedDeriv k (weightedPartition lam alpha gamma t 0) h
        = weightedPartition lam alpha gamma t k h := by
  intro k
  induction k with
  | zero => intro h _; rw [iteratedDeriv_zero]
  | succ k ih =>
    intro h hh
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 h := by
      apply Metric.isOpen_ball.mem_nhds
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hh
    -- On `ball 0 1`, `iteratedDeriv k (G 0)` agrees with `G k`.
    have h_eq : iteratedDeriv k (weightedPartition lam alpha gamma t 0)
        =ᶠ[𝓝 h] weightedPartition lam alpha gamma t k := by
      refine Filter.eventuallyEq_of_mem hball (fun y hy => ?_)
      have hy' : |y| < 1 := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy; exact hy
      exact ih hy'
    rw [iteratedDeriv_succ, h_eq.deriv_eq,
      weightedPartition_deriv k hlam hgamma hdisc ht hh]

/-- **Second `h`-derivative of the partition `Z = G 0` at `h = 0`**, as a
genuine `iteratedDeriv`: `Z''(0) = ∫ (t x)² e^{-tL}`. -/
theorem iteratedDeriv_two_partition_zero
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 2 (weightedPartition lam alpha gamma t 0) 0
      = ∫ x : ℝ, (t * x) ^ 2 *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
  rw [iteratedDeriv_weightedPartition_zero hlam hgamma hdisc ht 2 (by norm_num)]
  unfold weightedPartition
  congr 1; funext x
  have hexp : Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x)))
      = Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by congr 1; ring
  rw [hexp]; ring

/-- **Third `h`-derivative of the partition `Z = G 0` at `h = 0`**, as a
genuine `iteratedDeriv`: `Z'''(0) = ∫ -(t x)³ e^{-tL}`. -/
theorem iteratedDeriv_three_partition_zero
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 3 (weightedPartition lam alpha gamma t 0) 0
      = ∫ x : ℝ, -(t * x) ^ 3 *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
  rw [iteratedDeriv_weightedPartition_zero hlam hgamma hdisc ht 3 (by norm_num)]
  unfold weightedPartition
  congr 1; funext x
  have hexp : Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x)))
      = Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by congr 1; ring
  rw [hexp]; ring

end Laplace.OneD
