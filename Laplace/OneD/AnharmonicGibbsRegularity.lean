/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.Anharmonic
import Laplace.OneD.AnharmonicKappa3Affine
import Threepoint.CrossSusceptibility

/-!
# Anharmonic 1D `Threepoint.GibbsRegularity` instance (skeleton)

Concrete `Threepoint.GibbsRegularity` instance for the 1D anharmonic
potential `L(x) = (λ/2) x² + (α/6) x³ + (γ/24) x⁴` (with discriminant
`α² < 3λγ`) at the linear perturbation `A(x) = x` on `ℝ` against
Lebesgue measure. Anharmonic mirror of
`Laplace.OneD.HarmonicGibbsRegularity._root_.Threepoint.harmonic_id_gibbsRegularity`.

**Skeleton status (2026-05-23 tide).** The first two regularity fields
(`partition_pos`, `partition_h_zero`) are proven; the third
(`partition_hasDerivAt`) is left as `sorry` with a detailed proof
sketch. The follow-up analytic-regularity tide picks up the sorry
using the dominated-convergence + Gaussian-decay machinery in
`Laplace.OneD.IntegralRemainder`.

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

open MeasureTheory

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

/-! ## The `GibbsRegularity` instance (skeleton) -/

/-- **Concrete `GibbsRegularity` for the anharmonic + linear-perturbation case (skeleton).**

For the 1D anharmonic potential `L(x) = (λ/2) x² + (α/6) x³ + (γ/24) x⁴`
with discriminant `α² < 3λγ`, at the linear perturbation `A(x) = x` on
`ℝ` against Lebesgue (`λ, γ, t > 0`), all three regularity fields hold.

Two of three fields proven; `partition_hasDerivAt` is `sorry` —
left for the next analytic-regularity tide. See proof sketch below
the instance.

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
    /-
    **Proof sketch (next analytic-regularity tide).**

    Goal:
      HasDerivAt (fun h : ℝ => ∫ x, exp(-(t · (L_anh(x) + h · x))))
        (∫ x, (-t · x) · exp(-(t · L_anh(x)))) 0

    Use `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_lip` or
    `hasDerivAt_integral_of_dominated_of_aeMeasurable`. The dominator
    on a neighborhood of `h = 0` (say `|h| ≤ 1`) is

      D(x) = exp(-t · L_anh(x)) · (|t · x| + 1) · exp(t · |x|)

    where the `exp(t · |x|)` factor bounds `exp(-t · h · x)` for
    `|h| ≤ 1`. By the coercivity `L_anh(x) ≥ c · x²`, the dominator
    decays like `exp(-t·c·x²) · poly(x) · exp(t·|x|)`. The
    `exp(t · |x|)` factor is absorbed by completing the square:
    `-t·c·x² + t·|x| ≤ -t·c·x² + (c·t/2)·x² + 1/(2c) = -(t·c/2)·x² + const`,
    so the dominator is still Gaussian-decaying and integrable.

    Pointwise derivative (under the integral): differentiating
    `exp(-(t · (L_anh(x) + h · x)))` in `h` gives
    `-t · x · exp(-(t · (L_anh(x) + h · x)))`. At `h = 0` this is
    `-t · x · exp(-t · L_anh(x))`, which is the integrand on the RHS.

    The integrability of the RHS integrand `x · exp(-t · L_anh(x))`
    is exactly `integrable_pow_mul_exp_neg_anharmonic 1` (private in
    `AnharmonicKappa3Affine` — would need to be made public, or
    re-proven publicly here).

    Estimated proof size: 100-200 lines.
    -/
    sorry

end Laplace.OneD
