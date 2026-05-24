/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.Anharmonic
import Laplace.OneD.AnharmonicKappa3Affine
import Threepoint.CrossSusceptibility

/-!
# Anharmonic 1D `Threepoint.GibbsRegularity` instance

Concrete `Threepoint.GibbsRegularity` instance for the 1D anharmonic
potential `L(x) = (λ/2) x² + (α/6) x³ + (γ/24) x⁴` (with discriminant
`α² < 3λγ`) at the linear perturbation `A(x) = x` on `ℝ` against
Lebesgue measure. Anharmonic mirror of
`Laplace.OneD.HarmonicGibbsRegularity._root_.Threepoint.harmonic_id_gibbsRegularity`.

The third field (`partition_hasDerivAt`) routes through
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
the local dominator `t · exp(t/(2c)) · |x| · exp(-(t/2) · L_anh(x))`,
integrable via `integrable_x_mul_exp_neg_t_anharmonic` at half
temperature. The first two fields (`partition_pos`,
`partition_h_zero`) were landed in the skeleton tide; this tide
closed the third.

The instance unlocks the general FDT identity
`Threepoint.gibbsCov_deriv_eq_neg_t_kappa3` for the anharmonic
potential. Combined with `Laplace.OneD.AnharmonicKappa3.kappa3_anharmonic_id_id_id_asymptotic`
(Tide 9), this yields the closed-form asymptotic
`∂_h Cov_h(x, x)|_{h=0} → α/(λ³ t)` as `t → ∞`. The empirical
validation of the asymptotic appears in
`projects/primer/experiment-log/2026-05-23-experiment-fdt-identity-1d.md`
(HMC at `(λ, α, γ, t) = (1, 0.5, 1, 100)`, formal asymptote $0.005$
matched within $2.5\sigma$).
-/

open MeasureTheory Topology

namespace Laplace.OneD

/-- The unperturbed anharmonic partition function is integrable.

This is the `n = 0` case of `integrable_pow_mul_exp_neg_anharmonic`
(which is `private` in `AnharmonicKappa3Affine`). Re-derive here as
a public witness used by the `GibbsRegularity` instance below. -/
theorem integrable_exp_neg_t_anharmonic
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Integrable (fun x : ℝ =>
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  -- Same dominating-Gaussian argument as in
  -- `AnharmonicKappa3Affine.integrable_pow_mul_exp_neg_anharmonic 0`,
  -- specialised to `n = 0`.
  obtain ⟨c, hc_pos, hbound⟩ :=
    anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  have htc_pos : 0 < t * c := mul_pos ht hc_pos
  -- Dominator: `exp(-tc·x²)`, integrable Gaussian.
  have h_dom : Integrable (fun x : ℝ => Real.exp (-(t * c * x ^ 2))) := by
    have h := integrable_abs_pow_mul_exp_neg_mul_sq htc_pos 0
    -- `|x|^0 = 1`, so the lemma collapses to bare Gaussian integrability.
    simpa using h
  -- Continuity → AE strong measurability.
  have h_meas : AEStronglyMeasurable
      (fun x : ℝ =>
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) volume := by
    apply Continuous.aestronglyMeasurable
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    unfold anharmonicPotential
    fun_prop
  -- Pointwise domination.
  refine h_dom.mono h_meas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h := hbound x
  have ht_le : t * (c * x ^ 2) ≤ t * anharmonicPotential lam alpha gamma x :=
    mul_le_mul_of_nonneg_left h ht.le
  linarith

/-- The integrand `x · exp(-t · L_anh(x))` is integrable.

Public witness for the `n = 1` case (the RHS of `partition_hasDerivAt`
is `∫ -t · x · exp(-t · L_anh(x)) dx`). Mirrors
`integrable_exp_neg_t_anharmonic` (the `n = 0` case). -/
theorem integrable_x_mul_exp_neg_t_anharmonic
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Integrable (fun x : ℝ => x *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  -- Same Gaussian-domination argument as the `n = 0` case, with one
  -- extra factor of `|x|`.
  obtain ⟨c, hc_pos, hbound⟩ :=
    anharmonic_coercive lam alpha gamma hlam hgamma hdisc
  have htc_pos : 0 < t * c := mul_pos ht hc_pos
  -- Dominator: `|x|¹ · exp(-tc · x²)`, integrable Gaussian-times-poly.
  have h_dom : Integrable (fun x : ℝ => |x| ^ 1 *
      Real.exp (-(t * c * x ^ 2))) :=
    integrable_abs_pow_mul_exp_neg_mul_sq htc_pos 1
  -- Continuity → AE strong measurability.
  have h_meas : AEStronglyMeasurable
      (fun x : ℝ => x *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) volume := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul continuous_id
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    unfold anharmonicPotential
    fun_prop
  refine h_dom.mono h_meas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs,
      abs_of_pos (Real.exp_pos _), pow_one]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg x)
  apply Real.exp_le_exp.mpr
  have h := hbound x
  have ht_le : t * (c * x ^ 2) ≤ t * anharmonicPotential lam alpha gamma x :=
    mul_le_mul_of_nonneg_left h ht.le
  linarith

/-- **Strict positivity of the unperturbed anharmonic partition.**

The integrand `exp(-t · L_anh(x))` is everywhere strictly positive,
and integrable (`integrable_exp_neg_t_anharmonic`). The integral is
therefore strictly positive. -/
theorem anharmonic_partition_pos
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    0 < (∫ x : ℝ,
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
  -- Use `integral_pos_iff_support_of_nonneg_ae`: since `exp > 0` everywhere,
  -- the support is all of `ℝ`, which has infinite Lebesgue measure (in
  -- particular nonzero).
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · -- Support of `exp(...)` is all of `ℝ` (`exp > 0` is never zero).
    have h_support : Function.support
        (fun x : ℝ =>
          Real.exp (-(t * anharmonicPotential lam alpha gamma x))) = Set.univ := by
      ext x
      simp [Function.mem_support, Real.exp_ne_zero]
    rw [h_support, Real.volume_univ]
    exact ENNReal.zero_lt_top
  · -- Nonneg a.e.: `exp ≥ 0` is pointwise.
    exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  · -- Integrable.
    exact integrable_exp_neg_t_anharmonic hlam hgamma hdisc ht

/-! ## Helpers for `partition_hasDerivAt` -/

/-- Pointwise derivative in `h` of the perturbed Boltzmann factor at a
fixed `x`. -/
private theorem anharmonic_perturbed_pointwise_hasDerivAt
    (lam alpha gamma t : ℝ) (h₀ x : ℝ) :
    HasDerivAt
      (fun h : ℝ =>
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
      ((-t * x) *
        Real.exp (-(t *
          (anharmonicPotential lam alpha gamma x + h₀ * x))))
      h₀ := by
  have h_lin : HasDerivAt (fun h : ℝ => h * x) x h₀ := by
    simpa using (hasDerivAt_id h₀).mul_const x
  have h_add :
      HasDerivAt
        (fun h : ℝ =>
          anharmonicPotential lam alpha gamma x + h * x) x h₀ :=
    h_lin.const_add _
  have h_t : HasDerivAt
      (fun h : ℝ =>
        t * (anharmonicPotential lam alpha gamma x + h * x))
      (t * x) h₀ := h_add.const_mul t
  have h_inner : HasDerivAt
      (fun h : ℝ =>
        -(t * (anharmonicPotential lam alpha gamma x + h * x)))
      (-(t * x)) h₀ := h_t.neg
  have h_exp := h_inner.exp
  convert h_exp using 1
  ring

/-- AM-GM-style scalar inequality: for `t, c > 0` and any real `x`,
`t · |x| ≤ (tc/2) · x² + t/(2c)`. -/
private theorem amgm_t_abs_x (t c : ℝ) (ht : 0 < t) (hc : 0 < c) (x : ℝ) :
    t * |x| ≤ t * c / 2 * x ^ 2 + t / (2 * c) := by
  have hc_ne : c ≠ 0 := hc.ne'
  have habs_sq : |x| ^ 2 = x ^ 2 := sq_abs x
  have h_sq_nn : 0 ≤ t * (c * |x| - 1) ^ 2 := mul_nonneg ht.le (sq_nonneg _)
  have h_expand : t * (c * |x| - 1) ^ 2
      = t * c ^ 2 * x ^ 2 - 2 * t * c * |x| + t := by
    have h_inner : (c * |x| - 1) ^ 2 = c ^ 2 * |x| ^ 2 - 2 * c * |x| + 1 := by ring
    rw [h_inner, habs_sq]; ring
  have h_poly_nn : 0 ≤ t * c ^ 2 * x ^ 2 - 2 * t * c * |x| + t := by linarith
  have h2c_pos : 0 < 2 * c := by linarith
  have h_eq_r : 2 * c * (t * c / 2 * x ^ 2 + t / (2 * c))
      = t * c ^ 2 * x ^ 2 + t := by field_simp
  have h_eq_l : 2 * c * (t * |x|) = 2 * t * c * |x| := by ring
  have h_mul_le : 2 * c * (t * |x|)
      ≤ 2 * c * (t * c / 2 * x ^ 2 + t / (2 * c)) := by
    rw [h_eq_l, h_eq_r]; linarith
  exact le_of_mul_le_mul_left h_mul_le h2c_pos

/-- Pointwise bound `|F'(h, x)| ≤ bound(x)` on `|h| < 1`. -/
private theorem anharmonic_perturbed_pointwise_bound
    {lam alpha gamma t c : ℝ} (ht : 0 < t) (hc_pos : 0 < c)
    (h_coerc : ∀ x : ℝ, c * x ^ 2 ≤ anharmonicPotential lam alpha gamma x)
    (h x : ℝ) (hh : |h| < 1) :
    ‖(-t * x) * Real.exp (-(t *
        (anharmonicPotential lam alpha gamma x + h * x)))‖
      ≤ t * Real.exp (t / (2 * c)) *
          (|x| * Real.exp (-((t / 2) *
              anharmonicPotential lam alpha gamma x))) := by
  -- Reduce to a bound on the exponent.
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos ht,
    abs_of_pos (Real.exp_pos _)]
  rw [show t * Real.exp (t / (2 * c)) *
            (|x| * Real.exp (-((t / 2) *
              anharmonicPotential lam alpha gamma x)))
        = t * |x| * (Real.exp (t / (2 * c)) *
            Real.exp (-((t / 2) *
              anharmonicPotential lam alpha gamma x))) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- Goal: -(t·(L + h·x)) ≤ t/(2c) + -((t/2)·L).
  -- Pieces:
  --   (1) -t·h·x ≤ t·|x|         [since |h·x| ≤ |x|]
  --   (2) t·|x|   ≤ (tc/2)·x² + t/(2c)         [AM-GM]
  --   (3) (tc/2)·x² ≤ (t/2)·L                  [coercivity]
  --   chain: -t·h·x ≤ t/(2c) + (t/2)·L
  --          -t·L - t·h·x ≤ t/(2c) - (t/2)·L
  have h1 : -(t * (h * x)) ≤ t * |x| := by
    have h_abs_hx_le : |h * x| ≤ |x| := by
      rw [abs_mul]
      have hhx_le : |h| * |x| ≤ 1 * |x| :=
        mul_le_mul_of_nonneg_right hh.le (abs_nonneg x)
      simpa using hhx_le
    have h_neg_le_abs : -(t * (h * x)) ≤ |t * (h * x)| := neg_le_abs _
    rw [abs_mul, abs_of_pos ht] at h_neg_le_abs
    have : t * |h * x| ≤ t * |x| :=
      mul_le_mul_of_nonneg_left h_abs_hx_le ht.le
    linarith
  have h2 : t * |x| ≤ t * c / 2 * x ^ 2 + t / (2 * c) :=
    amgm_t_abs_x t c ht hc_pos x
  have h3 : t * c / 2 * x ^ 2 ≤ t / 2 * anharmonicPotential lam alpha gamma x := by
    have hcoerc := h_coerc x
    have ht2_nn : 0 ≤ t / 2 := by linarith
    nlinarith [hcoerc, ht2_nn]
  linarith

/-- Integrability of the bound function used in `partition_hasDerivAt`. -/
private theorem anharmonic_bound_integrable
    {lam alpha gamma t c : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) (_hc_pos : 0 < c) :
    Integrable (fun x : ℝ =>
      t * Real.exp (t / (2 * c)) *
        (|x| * Real.exp (-((t / 2) *
          anharmonicPotential lam alpha gamma x)))) volume := by
  have ht_half : 0 < t / 2 := by linarith
  have h_base : Integrable (fun x : ℝ =>
        x * Real.exp (-((t / 2) *
          anharmonicPotential lam alpha gamma x))) volume :=
    integrable_x_mul_exp_neg_t_anharmonic hlam hgamma hdisc ht_half
  have h_norm := h_base.norm
  have h_abs :
      Integrable (fun x : ℝ =>
          |x| * Real.exp (-((t / 2) *
            anharmonicPotential lam alpha gamma x))) volume := by
    refine h_norm.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact h_abs.const_mul (t * Real.exp (t / (2 * c)))

/-! ## The `GibbsRegularity` instance -/

/-- **Concrete `GibbsRegularity` for the anharmonic + linear-perturbation case.**

For the 1D anharmonic potential `L(x) = (λ/2) x² + (α/6) x³ + (γ/24) x⁴`
with discriminant `α² < 3λγ`, at the linear perturbation `A(x) = x` on
`ℝ` against Lebesgue (`λ, γ, t > 0`), all three regularity fields hold.

The third field (`partition_hasDerivAt`) routes through Mathlib's
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The
local dominator on `|h| < 1` is
`t · exp(t/(2c)) · |x| · exp(-(t/2) · L_anh(x))`, integrable via
`integrable_x_mul_exp_neg_t_anharmonic` at half temperature.

The instance unlocks the FDT identity
`Threepoint.gibbsCov_deriv_eq_neg_t_kappa3` for the anharmonic
potential — completing the formal side of the cross-validation
established empirically in
`projects/primer/experiment-log/2026-05-23-experiment-fdt-identity-1d.md`. -/
theorem _root_.Threepoint.anharmonic_id_gibbsRegularity
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    Threepoint.GibbsRegularity (volume : Measure ℝ)
      (anharmonicPotential lam alpha gamma)
      (fun x : ℝ => x) t where
  partition_pos := anharmonic_partition_pos hlam hgamma hdisc ht
  partition_h_zero := by
    -- ∫ exp(-(t · (L_anh(x) + 0 · x))) = ∫ exp(-(t · L_anh(x))).
    -- The integrand is pointwise-equal after `ring_nf`.
    congr 1
    funext x
    ring_nf
  partition_hasDerivAt := by
    -- Extract the coercivity constant.
    obtain ⟨c, hc_pos, h_coerc⟩ :=
      anharmonic_coercive lam alpha gamma hlam hgamma hdisc
    -- Neighborhood of h = 0.
    have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 zero_lt_one
    -- AE strong measurability of `F h` in `x`, for h near 0 (in fact for all h).
    have hF_meas : ∀ᶠ h in 𝓝 (0 : ℝ), AEStronglyMeasurable
        (fun x : ℝ =>
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
        (volume : Measure ℝ) := by
      refine Filter.Eventually.of_forall (fun h => ?_)
      apply Continuous.aestronglyMeasurable
      unfold anharmonicPotential
      fun_prop
    -- Integrability of `F 0`.
    have hF_int : Integrable
        (fun x : ℝ =>
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + 0 * x))))
        (volume : Measure ℝ) := by
      have h0 := integrable_exp_neg_t_anharmonic hlam hgamma hdisc ht
      refine h0.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [zero_mul, add_zero]
    -- AE strong measurability of `F' 0`.
    have hF'_meas : AEStronglyMeasurable
        (fun x : ℝ => (-t * x) *
          Real.exp (-(t *
            (anharmonicPotential lam alpha gamma x + 0 * x))))
        (volume : Measure ℝ) := by
      apply Continuous.aestronglyMeasurable
      unfold anharmonicPotential
      fun_prop
    -- Pointwise bound on `|F'(h, x)|` for `h ∈ ball 0 1`.
    have h_bound : ∀ᵐ x ∂(volume : Measure ℝ), ∀ h ∈ Metric.ball (0 : ℝ) 1,
        ‖(-t * x) * Real.exp (-(t *
            (anharmonicPotential lam alpha gamma x + h * x)))‖
          ≤ t * Real.exp (t / (2 * c)) *
              (|x| * Real.exp (-((t / 2) *
                anharmonicPotential lam alpha gamma x))) := by
      refine Filter.Eventually.of_forall (fun x h hh => ?_)
      have hh_lt : |h| < 1 := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
        exact hh
      exact anharmonic_perturbed_pointwise_bound ht hc_pos h_coerc h x hh_lt
    -- Integrability of the bound function.
    have h_bound_int :=
      anharmonic_bound_integrable (lam := lam) (alpha := alpha) (gamma := gamma)
        hlam hgamma hdisc ht hc_pos
    -- Pointwise differentiability of `F · x` at every `h` in the ball.
    have h_diff : ∀ᵐ x ∂(volume : Measure ℝ), ∀ h ∈ Metric.ball (0 : ℝ) 1,
        HasDerivAt
          (fun h' : ℝ =>
            Real.exp (-(t *
              (anharmonicPotential lam alpha gamma x + h' * x))))
          ((-t * x) * Real.exp (-(t *
              (anharmonicPotential lam alpha gamma x + h * x)))) h := by
      refine Filter.Eventually.of_forall (fun x h _ => ?_)
      exact anharmonic_perturbed_pointwise_hasDerivAt lam alpha gamma t h x
    -- Apply the dominated-convergence-style differentiation lemma.
    have key :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := (volume : Measure ℝ)) hs hF_meas hF_int hF'_meas h_bound
        h_bound_int h_diff
    -- `key.2 : HasDerivAt (fun h => ∫ x, F h x) (∫ x, F' 0 x) 0`.
    -- Rewrite the RHS integrand to drop the `+ 0 * x` term.
    have h_rhs_eq :
        (∫ x : ℝ, (-t * x) *
            Real.exp (-(t *
              (anharmonicPotential lam alpha gamma x + 0 * x))))
          = ∫ x : ℝ, (-t * x) *
              Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
      congr 1; funext x; ring_nf
    rw [← h_rhs_eq]
    exact key.2

end Laplace.OneD
