/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicGibbsRegularity
import Threepoint.CrossSusceptibility

/-!
# `Threepoint.GibbsObservable` instances for anharmonic monomials

Concrete `Threepoint.GibbsObservable` instances for the 1D anharmonic
potential `L(x) = (λ/2) x² + (α/6) x³ + (γ/24) x⁴` (discriminant
`α² < 3λγ`) with linear perturbation `A(x) = x` and monomial
observables `(fun x => x^k)` for `k : ℕ`. Anharmonic mirror of
`Laplace.OneD.HarmonicGibbsObservableMonomials`.

These witnesses make the FDT and cross-susceptibility identities in
`Laplace/OneD/AnharmonicFDT.lean` *unconditional*: the canonical
observables `x, x², x³` are the `k = 1, 2, 3` instances.

## Strategy

Dominated differentiation under the integral sign, exactly as in the
harmonic case and in the `partition_hasDerivAt` field of
`Threepoint.anharmonic_id_gibbsRegularity`. The pointwise derivative
`anharmonic_perturbed_pointwise_hasDerivAt` (now public) supplies the
`HasDerivAt` content; multiplying by the constant-in-`h` factor `x^k`
via `HasDerivAt.const_mul` handles the monomial. The dominator is the
`k = 0` derivative bound `anharmonic_perturbed_pointwise_bound` (now
public) scaled by `|x|^k`, i.e.
`t · exp(t/(2c)) · |x|^(k+1) · exp(-(t/2) · L_anh)`, integrable via the
general `integrable_abs_pow_mul_exp_neg_t_anharmonic` proved below at
half temperature.
-/

open MeasureTheory

namespace Laplace.OneD

/-- General integrability of `|x|^m · exp(-t · L_anh(x))` for any
`m : ℕ`. Generalises `integrable_exp_neg_t_anharmonic` (`m = 0`) and
`integrable_x_mul_exp_neg_t_anharmonic` (`m = 1`); same
Gaussian-domination argument with the `m`-indexed polynomial dominator
`integrable_abs_pow_mul_exp_neg_mul_sq`. -/
theorem integrable_abs_pow_mul_exp_neg_t_anharmonic
    {lam alpha gamma t : ℝ} (m : ℕ)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Integrable (fun x : ℝ => |x| ^ m *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  obtain ⟨c, hc_pos, hbound⟩ :=
    anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  have htc_pos : 0 < t * c := mul_pos ht hc_pos
  -- Dominator: `|x|^m · exp(-tc · x²)`, integrable Gaussian-times-poly.
  have h_dom : Integrable (fun x : ℝ => |x| ^ m *
      Real.exp (-(t * c * x ^ 2))) :=
    integrable_abs_pow_mul_exp_neg_mul_sq htc_pos m
  -- Continuity → AE strong measurability.
  have h_meas : AEStronglyMeasurable
      (fun x : ℝ => |x| ^ m *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) volume := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul (continuous_abs.pow m)
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    unfold anharmonicPotential
    fun_prop
  refine h_dom.mono h_meas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, abs_of_pos (Real.exp_pos _)]
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg x) m)
  apply Real.exp_le_exp.mpr
  have h := hbound x
  have ht_le : t * (c * x ^ 2) ≤ t * anharmonicPotential lam alpha gamma x :=
    mul_le_mul_of_nonneg_left h ht.le
  linarith

/-! ## The `GibbsObservable` instance for monomial observables -/

/-- **Concrete `Threepoint.GibbsObservable` for the anharmonic + linear
perturbation case at monomial observables.** For `λ, γ > 0`,
`α² < 3λγ`, `t > 0`, `k : ℕ`,
`Threepoint.GibbsObservable volume (anharmonicPotential λ α γ) id t (·^k)`
holds.

The first conjunct is the `h = 0` numerator reduction (`ring_nf`); the
second is `HasDerivAt` of the perturbed numerator at `h = 0`, proved by
dominated differentiation under the integral via
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
theorem _root_.Threepoint.anharmonic_id_gibbsObservable_pow
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) (k : ℕ) :
    Threepoint.GibbsObservable (volume : Measure ℝ)
      (anharmonicPotential lam alpha gamma)
      (fun x : ℝ => x) t (fun x : ℝ => x ^ k) := by
  obtain ⟨c, hc_pos, h_coerc⟩ :=
    anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  refine ⟨?_, ?_⟩
  · -- First conjunct: h = 0 numerator identity.
    congr 1
    funext x
    ring_nf
  · -- Second conjunct: HasDerivAt of the perturbed numerator at h = 0.
    have hball : Metric.ball (0 : ℝ) 1 ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds _ one_pos
    -- Integrability of `F` at `h = 0`.
    have hF_int : Integrable
        (fun x : ℝ => x ^ k *
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x))))
        (volume : Measure ℝ) := by
      have h_abs := integrable_abs_pow_mul_exp_neg_t_anharmonic k hlam hgamma hdisc ht
      refine h_abs.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · apply Continuous.aestronglyMeasurable
        apply Continuous.mul (continuous_id.pow k)
        apply Real.continuous_exp.comp
        apply Continuous.neg
        apply Continuous.mul continuous_const
        unfold anharmonicPotential
        fun_prop
      · rw [Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_pos (Real.exp_pos _)]
        have hexp : Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x)))
            = Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
          congr 1; ring
        rw [hexp]
    -- AE strong measurability of `F` for `h` near 0.
    have hF_meas : ∀ᶠ h in nhds (0 : ℝ),
        AEStronglyMeasurable
          (fun x : ℝ => x ^ k *
            Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
          (volume : Measure ℝ) := by
      refine Filter.Eventually.of_forall fun h => ?_
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul (continuous_id.pow k)
      apply Real.continuous_exp.comp
      apply Continuous.neg
      apply Continuous.mul continuous_const
      unfold anharmonicPotential
      fun_prop
    -- AE strong measurability of `F'` at `h = 0`.
    have hF'_meas : AEStronglyMeasurable
        (fun x : ℝ => x ^ k *
          ((-t * x) *
            Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x)))))
        (volume : Measure ℝ) := by
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul (continuous_id.pow k)
      apply Continuous.mul (by fun_prop)
      apply Real.continuous_exp.comp
      apply Continuous.neg
      apply Continuous.mul continuous_const
      unfold anharmonicPotential
      fun_prop
    -- Dominator: `t · exp(t/(2c)) · |x|^(k+1) · exp(-(t/2) · L_anh)`.
    set bound : ℝ → ℝ :=
      fun x => t * Real.exp (t / (2 * c)) *
        (|x| ^ (k + 1) * Real.exp (-((t / 2) *
          anharmonicPotential lam alpha gamma x))) with hbound_def
    have h_bound_int : Integrable bound := by
      have ht_half : 0 < t / 2 := by linarith
      have h_abs :=
        integrable_abs_pow_mul_exp_neg_t_anharmonic (k + 1) hlam hgamma hdisc ht_half
      have h_total := h_abs.const_mul (t * Real.exp (t / (2 * c)))
      refine h_total.congr (Filter.Eventually.of_forall fun x => ?_)
      rw [hbound_def]
    -- Pointwise bound `‖F' h x‖ ≤ bound x` for `|h| < 1`.
    have h_F'_bound : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Metric.ball (0 : ℝ) 1,
        ‖x ^ k *
            ((-t * x) *
              Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))‖
          ≤ bound x := by
      refine Filter.Eventually.of_forall fun x h hx => ?_
      have hh_lt : |h| < 1 := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
        exact hx
      have hv :=
        anharmonic_perturbed_pointwise_bound ht hc_pos h_coerc h x hh_lt
      rw [norm_mul, Real.norm_eq_abs, abs_pow]
      have hxk_nn : 0 ≤ |x| ^ k := pow_nonneg (abs_nonneg x) k
      calc |x| ^ k *
              ‖(-t * x) *
                Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x)))‖
            ≤ |x| ^ k *
              (t * Real.exp (t / (2 * c)) *
                (|x| * Real.exp (-((t / 2) *
                  anharmonicPotential lam alpha gamma x)))) :=
              mul_le_mul_of_nonneg_left hv hxk_nn
        _ = bound x := by rw [hbound_def]; ring
    -- Pointwise differentiability for each `x` and each `h ∈ ball 0 1`.
    have h_diff : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Metric.ball (0 : ℝ) 1,
        HasDerivAt
          (fun h : ℝ => x ^ k *
            Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
          (x ^ k *
            ((-t * x) *
              Real.exp (-(t *
                (anharmonicPotential lam alpha gamma x + h * x))))) h := by
      refine Filter.Eventually.of_forall fun x h _ => ?_
      exact (anharmonic_perturbed_pointwise_hasDerivAt lam alpha gamma t h x).const_mul
        (x ^ k)
    -- Apply the dominated-differentiation theorem.
    have h_total :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := (volume : Measure ℝ)) hball hF_meas hF_int hF'_meas h_F'_bound
        h_bound_int h_diff
    have h_d := h_total.2
    -- Reshape the derivative integrand to the `GibbsObservable` form
    -- (drop the `+ 0 · x` term, match `φ w * ((-t·w)·exp(-tL))`).
    have h_eq_deriv :
        (∫ a : ℝ, a ^ k *
            ((-t * a) *
              Real.exp (-(t * (anharmonicPotential lam alpha gamma a + 0 * a))))
              ∂(volume : Measure ℝ))
          = (∫ w : ℝ, w ^ k *
              ((-t * w) *
                Real.exp (-(t * anharmonicPotential lam alpha gamma w)))
                ∂(volume : Measure ℝ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with a
      ring_nf
    rw [h_eq_deriv] at h_d
    exact h_d

/-! ## Multiplicative-form wrappers

The FDT and cross-susceptibility theorems consume the witnesses in
multiplicative form (`x`, `x*x`, `x*x*x`). Transport the `pow` instance
along function-extensional equality. -/

/-- `GibbsObservable` for `fun x => x`. -/
theorem _root_.Threepoint.anharmonic_id_gibbsObservable_id
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Threepoint.GibbsObservable (volume : Measure ℝ)
      (anharmonicPotential lam alpha gamma)
      (fun x : ℝ => x) t (fun x : ℝ => x) := by
  have h := Threepoint.anharmonic_id_gibbsObservable_pow hlam hgamma hdisc ht 1
  have heq : (fun x : ℝ => x ^ 1) = (fun x : ℝ => x) := by funext x; ring
  rwa [heq] at h

/-- `GibbsObservable` for `fun x => x * x`. -/
theorem _root_.Threepoint.anharmonic_id_gibbsObservable_mul_self
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Threepoint.GibbsObservable (volume : Measure ℝ)
      (anharmonicPotential lam alpha gamma)
      (fun x : ℝ => x) t (fun x : ℝ => x * x) := by
  have h := Threepoint.anharmonic_id_gibbsObservable_pow hlam hgamma hdisc ht 2
  have heq : (fun x : ℝ => x ^ 2) = (fun x : ℝ => x * x) := by funext x; ring
  rwa [heq] at h

/-- `GibbsObservable` for `fun x => x * x * x`. -/
theorem _root_.Threepoint.anharmonic_id_gibbsObservable_mul_mul_self
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Threepoint.GibbsObservable (volume : Measure ℝ)
      (anharmonicPotential lam alpha gamma)
      (fun x : ℝ => x) t (fun x : ℝ => x * x * x) := by
  have h := Threepoint.anharmonic_id_gibbsObservable_pow hlam hgamma hdisc ht 3
  have heq : (fun x : ℝ => x ^ 3) = (fun x : ℝ => x * x * x) := by funext x; ring
  rwa [heq] at h

end Laplace.OneD
