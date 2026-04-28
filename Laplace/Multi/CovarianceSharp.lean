/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Multi.Covariance

/-!
# Sharp-rate multivariate Laplace covariance asymptotic (in progress)

This file aims at the **sharp** $O(t^{-2})$ rate for `lem:laplace_cov` of the
Susceptibility Primer, building on the **weak** $O(t^{-3/2})$ rate already
proved as `gibbsCov_first_order_rate_weak` in `Laplace.Multi.Covariance`.

The sharp rate exploits *parity-resolved Taylor jets*:

* the cubic jet `cV` of the potential `V` is **odd** in `w`, so a leading
  $1/\sqrt{t}$ correction to the rescaled weight integrates to zero against
  the even Gaussian factor (after multiplication by an even bilinear factor
  in the integrand);
* the quadratic jets `qφ`, `qψ` of the observables are **even** in `w`, so
  the cross terms admit similar parity cancellations.

Following the GPT-5.5 Pro consultation `gpt_responses/strategy_sharp_track.md`,
we adopt two architectural decisions:

1. **Centered numerator target.** Instead of bounding $|t\,N_t - Z m|$ (which
   would require the partition asymptote at the sharp rate too), we bound
   the *centered* quantity
   $$|t \cdot N_t(\phi\psi) - m \cdot D_t| \le K/t$$
   where $m = \langle a, H^{-1} b\rangle$ and $D_t$ is the rescaled partition.
   The existing weak lower bound $D_t \ge Z/2$ then suffices to extract the
   sharp expectation rate.
2. **Scaled-jet formulation.** We do *not* assume the cubic jet is
   homogeneous; we work with the scaled jet `s₁(t,u) := t · cV((√t)⁻¹ • u)`
   directly. The parity argument needs only oddness of `cV`, not
   homogeneity. Tensor-valued jets (and the resulting *explicit* coefficient
   for `lem:laplace_cov2`) are deferred to a follow-on file.

## Status

Stage 0 (jet hypothesis structures) below. Stages 1–4 (scalar bound,
rescaled decomposition lemmas, centered numerator bound, sharp covariance
theorem) are tracked as `sorry` stubs.

-/

namespace Laplace.Multi

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section JetHypotheses

/-- **Sharp local approximation package for the potential**.

Extends `PotentialApprox` with an *odd* cubic-scale jet `cV` and a quartic
local remainder. Together with the existing local cubic remainder of
`PotentialApprox`, this controls the rescaled potential to one extra Taylor
order — sufficient for the parity-resolved sharp covariance rate.

The cubic jet is *not* required to be exactly homogeneous; oddness plus
the global cubic-growth bound `|cV w| ≤ Cc · ‖w‖³` is enough for the sharp
rate (see `gpt_responses/strategy_sharp_track.md`, §2). Imposing exact
cubic homogeneity (or the full symmetric trilinear tensor data) is a
strict strengthening, and is the natural route for the *explicit-coefficient*
companion theorem `lem:laplace_cov2`. -/
structure PotentialJetApprox
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    extends PotentialApprox V H where
  /-- Cubic-scale jet. -/
  cV : (ι → ℝ) → ℝ
  /-- Continuity of the cubic jet (needed for measurability). -/
  cV_continuous : Continuous cV
  /-- Oddness of the cubic jet: `cV (-w) = -(cV w)`. -/
  cV_odd : Function.Odd cV
  /-- Global cubic-growth constant. -/
  cV_bound_const : ℝ
  cV_bound_const_nonneg : 0 ≤ cV_bound_const
  /-- Global cubic-growth bound: `|cV w| ≤ C · ‖w‖³`. -/
  cV_bound : ∀ w : ι → ℝ, |cV w| ≤ cV_bound_const * ‖w‖ ^ 3
  /-- Radius for the quartic local remainder (may differ from `local_radius`). -/
  jet_radius : ℝ
  /-- Constant for the quartic local remainder. -/
  jet_const : ℝ
  jet_radius_pos : 0 < jet_radius
  jet_const_nonneg : 0 ≤ jet_const
  /-- Local quartic remainder: on `‖w‖ ≤ jet_radius`,
  `|V w - ((1/2) · quadForm H w + cV w)| ≤ jet_const · ‖w‖^4`. -/
  jet_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |V w - ((1 / 2 : ℝ) * quadForm H w + cV w)| ≤ jet_const * ‖w‖ ^ 4

/-- **Sharp local approximation package for an observable**.

Extends `ObservableApprox` with an *even* quadratic-scale jet `qφ` and a
cubic local remainder. The quadratic jet is not required to be exactly
homogeneous; evenness plus `|qφ w| ≤ Cq · ‖w‖²` suffices for the
parity-resolved sharp rate. -/
structure ObservableJetApprox
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    extends ObservableApprox φ a where
  /-- Quadratic-scale jet. -/
  qφ : (ι → ℝ) → ℝ
  /-- Continuity of the quadratic jet (needed for measurability). -/
  qφ_continuous : Continuous qφ
  /-- Evenness of the quadratic jet: `qφ (-w) = qφ w`. -/
  qφ_even : Function.Even qφ
  /-- Global quadratic-growth constant. -/
  qφ_bound_const : ℝ
  qφ_bound_const_nonneg : 0 ≤ qφ_bound_const
  /-- Global quadratic-growth bound: `|qφ w| ≤ C · ‖w‖²`. -/
  qφ_bound : ∀ w : ι → ℝ, |qφ w| ≤ qφ_bound_const * ‖w‖ ^ 2
  /-- Radius for the cubic local remainder. -/
  jet_radius : ℝ
  /-- Constant for the cubic local remainder. -/
  jet_const : ℝ
  jet_radius_pos : 0 < jet_radius
  jet_const_nonneg : 0 ≤ jet_const
  /-- Local cubic remainder: on `‖w‖ ≤ jet_radius`,
  `|φ w - (dot a w + qφ w)| ≤ jet_const · ‖w‖³`. -/
  jet_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |φ w - (dot a w + qφ w)| ≤ jet_const * ‖w‖ ^ 3

/-- The cubic jet vanishes at the origin. Follows from oddness:
`cV (-0) = -(cV 0)` and `-0 = 0` gives `cV 0 = -(cV 0)`, so `cV 0 = 0`. -/
@[simp] lemma PotentialJetApprox.cV_zero
    {V : (ι → ℝ) → ℝ} {H : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hV : PotentialJetApprox V H) : hV.cV 0 = 0 := by
  have h := hV.cV_odd 0
  simp at h
  linarith

/-- The quadratic jet vanishes at the origin. Follows *not* from evenness alone
but from the local cubic remainder bound at `w = 0` together with `φ 0 = 0`:
`|φ 0 - (dot a 0 + qφ 0)| = |qφ 0| ≤ C · ‖0‖³ = 0`. -/
@[simp] lemma ObservableJetApprox.qφ_zero
    {φ : (ι → ℝ) → ℝ} {a : ι → ℝ}
    (hφ : ObservableJetApprox φ a) : hφ.qφ 0 = 0 := by
  have hb := hφ.jet_bound 0 (by simp [hφ.jet_radius_pos.le])
  have hφ0 : φ 0 = 0 := hφ.phi_zero
  have hdot : dot a (0 : ι → ℝ) = 0 := by
    unfold dot
    simp
  rw [hφ0, hdot, zero_add, zero_sub, abs_neg] at hb
  have hbound : (0 : ℝ) ≤ hφ.jet_const * ‖(0 : ι → ℝ)‖ ^ 3 := by
    simp [hφ.jet_const_nonneg]
  have h_zero_norm : ‖(0 : ι → ℝ)‖ = 0 := norm_zero
  rw [h_zero_norm] at hb
  simp at hb
  exact hb

end JetHypotheses

section ScalarBounds

/-- **Sharp Taylor-1 bound for `Real.exp`**:
`|exp(-r) - (1 - r)| ≤ r^2 · exp |r|`.

The weak counterpart is `abs_exp_neg_sub_one_le` in `RescaledIntegrals`,
which gives `|exp(-r) - 1| ≤ |r| · exp |r|`. Subtracting one more Taylor term
(`-r`) tightens the rate from linear to quadratic in `r`, which is what the
sharp covariance proof needs to extract the `1/√t · ∫ ⟨a,u⟩⟨b,u⟩ · cV · gW = 0`
parity cancellation cleanly.

The constant is `1` (not the optimal `1/2`); per the GPT-5.5 Pro consult, the
half-factor is not needed for the bound-only sharp rate. -/
lemma abs_exp_neg_sub_one_add_le (r : ℝ) :
    |Real.exp (-r) - (1 - r)| ≤ r ^ 2 * Real.exp |r| := by
  -- Bridge via `Complex.norm_exp_sub_sum_le_norm_mul_exp` at `n = 2`.
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-r : ℂ) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
    pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    div_one, zero_add] at h
  have hL :
      ‖Complex.exp (-↑r : ℂ) - (1 + -↑r)‖ = |Real.exp (-r) - (1 - r)| := by
    rw [show (1 + -↑r : ℂ) = ↑(1 - r) from by push_cast; ring]
    rw [show (-↑r : ℂ) = ↑(-r) from by push_cast; ring]
    rw [← Complex.ofReal_exp]
    rw [show (↑(Real.exp (-r)) : ℂ) - ↑(1 - r)
         = ↑(Real.exp (-r) - (1 - r)) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hR : ‖(-↑r : ℂ)‖ = |r| := by
    rw [show (-↑r : ℂ) = ↑(-r) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]
  rw [hL, hR] at h
  rw [show (|r| : ℝ) ^ 2 = r ^ 2 from sq_abs r] at h
  exact h

end ScalarBounds

section RescaledLocalBounds

/-- **Sharp rescaled-perturbation bound** (parametrized).

Given a quartic local remainder `|V w - ((1/2)·quadForm H w + cV w)| ≤ C·‖w‖^4`
on `‖w‖ ≤ R`, the rescaled perturbation differs from the *scaled cubic jet*
`s₁(t,u) := t · cV((√t)⁻¹ • u)` by `O(‖u‖^4/t)` on the local region:

  `|rescaledPerturbation V H t u - t · cV((√t)⁻¹ • u)| ≤ C · ‖u‖^4 / t`,
  for `‖u‖ ≤ R · √t`.

This is the sharp analogue of `abs_rescaledPerturbation_le` (which only
controls `|rescaledPerturbation| ≤ C·‖u‖³/√t`); it isolates the *odd*
1/√t-scale leading correction `t · cV((√t)⁻¹ • u)`. -/
lemma abs_rescaledPerturbation_sub_scaledCubicJet_le
    (V cV : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {R C : ℝ}
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - ((1 / 2 : ℝ) * quadForm H w + cV w)| ≤ C * ‖w‖ ^ 4)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ R * Real.sqrt t) :
    |rescaledPerturbation V H t u - t * cV ((Real.sqrt t)⁻¹ • u)|
      ≤ C * ‖u‖ ^ 4 / t := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have h_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  -- ‖(√t)⁻¹ • u‖ ≤ R.
  have h_norm : ‖(Real.sqrt t)⁻¹ • u‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos]
    rw [show (Real.sqrt t)⁻¹ * ‖u‖ = ‖u‖ / Real.sqrt t from by field_simp]
    rwa [div_le_iff₀ hsqrt_pos]
  have h_loc := h_local ((Real.sqrt t)⁻¹ • u) h_norm
  -- ‖(√t)⁻¹ • u‖^4 = ‖u‖^4 / t^2.
  have h_norm_pow : ‖(Real.sqrt t)⁻¹ • u‖ ^ 4 = ‖u‖ ^ 4 / t ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos, mul_pow, inv_pow]
    rw [show (Real.sqrt t) ^ 4 = (Real.sqrt t * Real.sqrt t) ^ 2 from by ring,
        h_sq]
    field_simp
  rw [h_norm_pow] at h_loc
  -- quadForm H ((√t)⁻¹ • u) = quadForm H u / t.
  have h_qf : quadForm H ((Real.sqrt t)⁻¹ • u) = quadForm H u / t := by
    rw [quadForm_smul]
    rw [show ((Real.sqrt t)⁻¹) ^ 2 = ((Real.sqrt t) ^ 2)⁻¹ from by
      rw [inv_pow]]
    rw [show (Real.sqrt t) ^ 2 = t from by rw [sq, h_sq]]
    field_simp
  -- Restate the goal in terms of the local bound expression.
  unfold rescaledPerturbation
  have h_eq : t * V ((Real.sqrt t)⁻¹ • u) - (1 / 2) * quadForm H u
      - t * cV ((Real.sqrt t)⁻¹ • u)
      = t * (V ((Real.sqrt t)⁻¹ • u) -
              ((1 / 2 : ℝ) * quadForm H ((Real.sqrt t)⁻¹ • u)
                + cV ((Real.sqrt t)⁻¹ • u))) := by
    rw [h_qf]
    field_simp
    ring
  rw [h_eq, abs_mul, abs_of_pos ht]
  calc t * |V ((Real.sqrt t)⁻¹ • u) - ((1 / 2 : ℝ) * quadForm H ((Real.sqrt t)⁻¹ • u)
            + cV ((Real.sqrt t)⁻¹ • u))|
      ≤ t * (C * (‖u‖ ^ 4 / t ^ 2)) :=
        mul_le_mul_of_nonneg_left h_loc ht.le
    _ = C * ‖u‖ ^ 4 / t := by
        rw [show (t : ℝ) ^ 2 = t * t from sq t]
        field_simp

/-- **Sharp rescaled-observable bound** (parametrized).

Given a cubic local remainder `|φ w - (dot a w + qφ w)| ≤ C·‖w‖^3` on
`‖w‖ ≤ R`, the rescaled observable error differs from the *scaled
quadratic jet* `qφ_t(u) := qφ((√t)⁻¹ • u)` by `O(‖u‖^3/t^(3/2))`:

  `|φ((√t)⁻¹ • u) - (√t)⁻¹ · dot a u - qφ((√t)⁻¹ • u)| ≤ C · ‖u‖^3 / t^(3/2)`,
  for `‖u‖ ≤ R · √t`.

Sharp analogue of `abs_rescaledObservable_linear_error_le`. -/
lemma abs_rescaledObservable_quadratic_error_le
    (φ qφ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    {R C : ℝ}
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |φ w - (dot a w + qφ w)| ≤ C * ‖w‖ ^ 3)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ R * Real.sqrt t) :
    |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u - qφ ((Real.sqrt t)⁻¹ • u)|
      ≤ C * ‖u‖ ^ 3 / (t * Real.sqrt t) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have h_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have h_norm : ‖(Real.sqrt t)⁻¹ • u‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos]
    rw [show (Real.sqrt t)⁻¹ * ‖u‖ = ‖u‖ / Real.sqrt t from by field_simp]
    rwa [div_le_iff₀ hsqrt_pos]
  have h_loc := h_local ((Real.sqrt t)⁻¹ • u) h_norm
  -- ‖(√t)⁻¹ • u‖^3 = ‖u‖^3 / (t · √t).
  have h_norm_pow : ‖(Real.sqrt t)⁻¹ • u‖ ^ 3 = ‖u‖ ^ 3 / (t * Real.sqrt t) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos, mul_pow, inv_pow]
    rw [show (Real.sqrt t) ^ 3 = Real.sqrt t * (Real.sqrt t * Real.sqrt t) from by
      ring]
    rw [h_sq, mul_comm (Real.sqrt t) t]
    field_simp
  rw [h_norm_pow] at h_loc
  -- dot a ((√t)⁻¹ • u) = (√t)⁻¹ · dot a u.
  have h_dot : dot a ((Real.sqrt t)⁻¹ • u) = (Real.sqrt t)⁻¹ * dot a u :=
    dot_smul a (Real.sqrt t)⁻¹ u
  rw [h_dot] at h_loc
  -- h_loc : |φ((√t)⁻¹•u) - ((√t)⁻¹·dot a u + qφ((√t)⁻¹•u))| ≤ C · ‖u‖^3/(t·√t)
  -- Goal: |φ((√t)⁻¹•u) - (√t)⁻¹·dot a u - qφ((√t)⁻¹•u)| ≤ C · ‖u‖^3 / (t · √t)
  -- Just associativity of subtraction inside the abs.
  have h_eq : φ ((Real.sqrt t)⁻¹ • u) - ((Real.sqrt t)⁻¹ * dot a u + qφ ((Real.sqrt t)⁻¹ • u))
      = φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u - qφ ((Real.sqrt t)⁻¹ • u) := by
    ring
  rw [h_eq] at h_loc
  -- Also fix the RHS form: C * (‖u‖^3 / (t·√t)) = C * ‖u‖^3 / (t·√t).
  have h_eq2 : C * (‖u‖ ^ 3 / (t * Real.sqrt t)) = C * ‖u‖ ^ 3 / (t * Real.sqrt t) := by
    ring
  rw [h_eq2] at h_loc
  exact h_loc

end RescaledLocalBounds

section IntegrabilityHelpers

/-- **Integrability of `dot a · dot b · gW · exp(-s_t)`** under
`PotentialApprox` + `LaplaceCovHypotheses`. Needed by the centered
numerator decomposition.

The bound is `|dot a u · dot b u · gW · exp(-s_t)| ≤ A·B·‖u‖² · gW · exp(-s_t)`,
and `‖u‖² · gW · exp(-s_t)` is integrable via `integrable_pow_norm_mul_rescaled_weight` (k = 2). -/
private lemma integrable_dot_mul_dot_mul_rescaled_weight
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV_cont : Continuous V)
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable (fun u : ι → ℝ =>
      dot a u * dot b u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
  set A : ℝ := ∑ i, |a i| with hA_def
  set B : ℝ := ∑ i, |b i| with hB_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_dot_a_cont : Continuous (fun u : ι → ℝ => dot a u) := by
    unfold dot
    exact continuous_finset_sum _
      (fun i _ => continuous_const.mul (continuous_apply i))
  have h_dot_b_cont : Continuous (fun u : ι → ℝ => dot b u) := by
    unfold dot
    exact continuous_finset_sum _
      (fun i _ => continuous_const.mul (continuous_apply i))
  have h_dom : MeasureTheory.Integrable (fun u : ι → ℝ =>
      A * B * (‖u‖ ^ 2 *
        (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))))) :=
    (integrable_pow_norm_mul_rescaled_weight V hV_cont H
      hc_pos h_coer 2 ht).const_mul (A * B)
  refine h_dom.mono' ?_ ?_
  · exact (((h_dot_a_cont.mul h_dot_b_cont).mul
      (continuous_gaussianWeight H)).mul (Real.continuous_exp.comp
        (continuous_rescaledPerturbation hV_cont H t).neg)).aestronglyMeasurable
  · filter_upwards with u
    have h_dot_a_le : |dot a u| ≤ A * ‖u‖ := by
      rw [hA_def]; exact abs_dot_le_l1_mul_norm a u
    have h_dot_b_le : |dot b u| ≤ B * ‖u‖ := by
      rw [hB_def]; exact abs_dot_le_l1_mul_norm b u
    have h_rw_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
    rw [Real.norm_eq_abs]
    rw [show dot a u * dot b u * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
        = (dot a u * dot b u) *
          (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) from by ring]
    rw [abs_mul, abs_of_nonneg h_rw_nn, abs_mul]
    calc |dot a u| * |dot b u| *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        ≤ (A * ‖u‖) * (B * ‖u‖) *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h_dot_a_le h_dot_b_le (abs_nonneg _)
              (mul_nonneg hA_nn (norm_nonneg _))) h_rw_nn
      _ = A * B * (‖u‖ ^ 2 *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))) := by
          rw [show ‖u‖ ^ 2 = ‖u‖ * ‖u‖ from sq _]; ring

end IntegrabilityHelpers

section ParityLemmas

/-- **Parity vanishing for the centered bilinear correction**: the integral
of `(dot a u · dot b u - m) · gW · cV((√t)⁻¹•u)` against the Gaussian
weight is zero, since the integrand is odd in u (even · even · odd).

This is the parity argument that drives the sharp `O(1/t)` rate for the
centered bilinear correction (sharp helper 1): it kills the leading
`1/√t` contribution that the weak track was forced to triangle-bound. -/
lemma integral_centered_bilinear_cubicJet_eq_zero
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (cV : (ι → ℝ) → ℝ) (cV_odd : Function.Odd cV)
    (a b : ι → ℝ) (m : ℝ) (t : ℝ) :
    ∫ u : ι → ℝ, (dot a u * dot b u - m) *
      cV ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u = 0 := by
  apply integral_odd_mul_gaussian_eq_zero H
    (fun u => (dot a u * dot b u - m) * cV ((Real.sqrt t)⁻¹ • u))
  intro u
  -- Show odd: (dot a (-u) · dot b (-u) - m) · cV((√t)⁻¹ • (-u))
  --         = (dot a u · dot b u - m) · (-cV((√t)⁻¹ • u))
  --         = -((dot a u · dot b u - m) · cV((√t)⁻¹ • u)).
  have h_dot_a : dot a (-u) = -(dot a u) := dot_neg a u
  have h_dot_b : dot b (-u) = -(dot b u) := dot_neg b u
  have h_smul : (Real.sqrt t)⁻¹ • (-u) = -((Real.sqrt t)⁻¹ • u) := by
    simp [smul_neg]
  rw [h_dot_a, h_dot_b, h_smul, cV_odd ((Real.sqrt t)⁻¹ • u)]
  ring

/-- **Parity vanishing for the cross-term jet correction**: the integral of
`dot c u · qφ((√t)⁻¹•u) · gW` is zero, since the integrand is odd in u
(odd · even · even). Used by sharp helpers 2/3. -/
lemma integral_dot_mul_quadJet_eq_zero
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (qφ : (ι → ℝ) → ℝ) (qφ_even : Function.Even qφ)
    (c : ι → ℝ) (t : ℝ) :
    ∫ u : ι → ℝ, dot c u * qφ ((Real.sqrt t)⁻¹ • u) *
      gaussianWeight H u = 0 := by
  apply integral_odd_mul_gaussian_eq_zero H
    (fun u => dot c u * qφ ((Real.sqrt t)⁻¹ • u))
  intro u
  have h_dot : dot c (-u) = -(dot c u) := dot_neg c u
  have h_smul : (Real.sqrt t)⁻¹ • (-u) = -((Real.sqrt t)⁻¹ • u) := by
    simp [smul_neg]
  rw [h_dot, h_smul, qφ_even ((Real.sqrt t)⁻¹ • u)]
  ring

end ParityLemmas

section SharpHelpers

/-- **Sharp helper 1 (centered bilinear correction)**: the centered
bilinear factor `(dot a u · dot b u - m)` against `gW · exp(-s_t)`
integrates to `O(1/t)`, where `m := dot a (Hinv b)`.

The two-step argument:
- `∫ (dot a · dot b - m) · gW = m · Z - m · Z = 0` via `gaussian_dot_mul_dot`.
- `|∫ (dot a · dot b - m) · gW · (exp(-s_t) - 1)| ≤ K/t` via parity:
  expand `exp(-s_t) - 1 = -s_t + Taylor remainder`, then
  `s_t = t · cV((√t)⁻¹•u) + O(‖u‖^4/t)` (Stage 2 bound), and the leading
  `-(t·cV)` term integrates to zero against the even bilinear factor and
  even Gaussian weight. -/
private lemma abs_integral_centered_bilinear_sharp_le
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |∫ u : ι → ℝ, (dot a u * dot b u - dot a (Hinv b)) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))|
        ≤ K / t := by
  -- Strategy:
  -- ∫ (dot a · dot b - m) · gW · exp(-s_t)
  --   = ∫ (dot a · dot b - m) · gW · 1
  --     + ∫ (dot a · dot b - m) · gW · (exp(-s_t) - 1)
  --   = 0 + (parity-resolved bound).
  -- The first integral vanishes via gaussian_dot_mul_dot:
  --   ∫ dot a · dot b · gW = m · Z.
  --   ∫ gW = Z.
  --   So ∫ (dot a · dot b - m) · gW = m·Z - m·Z = 0.
  -- Bounding the second by parity is the technical heart.
  -- This proof is non-trivial (~500 LOC). For now we use the existing
  -- weak-track bound via |gW · (exp(-s_t)-1)| ≤ Cs·‖u‖³/√t locally + tail,
  -- combined with |dot a · dot b - m| ≤ (A·B+|m|)·(1 + ‖u‖²), giving an
  -- absolute bound of K/√t. To upgrade to K/t we need the parity argument
  -- exploiting oddness of `t · cV((√t)⁻¹•u)` — deferred to a follow-on file.
  sorry

/-- **Sharp helper 2/3 (cross term)**: `∫ dot c u · (φ((√t)⁻¹•u) -
(√t)⁻¹·dot d u) · gW · exp(-s_t)` integrates to `O(1/(t·√t))`. The proof
uses the quadratic jet decomposition `remψ = qφ((√t)⁻¹•u) + r₃` (Stage 2),
with `dot c · qφ((√t)⁻¹•u)` integrating to zero by parity (linear · even
= odd) against the even Gaussian. -/
private lemma abs_integral_dot_mul_jet_remainder_sharp_le
    (V φ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (dotCoef phiGrad : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hφ : ObservableJetApprox φ phiGrad)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |∫ u : ι → ℝ, dot dotCoef u *
          (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))|
        ≤ K / (t * Real.sqrt t) := by
  sorry

/-- **Sharp helper 4 (quadratic remainder)**: the product of two
observable remainders integrated against `gW · exp(-s_t)` is `O(1/t²)`.
Local: `|remφ · remψ| ≤ Cφ·Cψ·‖u‖^4/t²` via the quadratic jets. -/
private lemma abs_integral_remainder_remainder_sharp_le
    (V φ ψ : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hφ : ObservableJetApprox φ a)
    (hψ : ObservableJetApprox ψ b)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |∫ u : ι → ℝ,
          (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
          (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))|
        ≤ K / t ^ 2 := by
  sorry

end SharpHelpers

section CenteredNumerator

/-- **Centered pair-numerator bound (sharp rate)**.

The centered formulation `t·N_t(φψ) - m·D_t` (where `m := dot a (Hinv b)`,
`N_t` is the rescaled numerator, `D_t` is the rescaled partition) is `O(1/t)`.

Per the GPT-5.5 Pro consult, this is the cleanest target for the sharp
track: it avoids the requirement to also sharpen the partition asymptote
`D_t - Z`, which is only `O(1/√t)` in the weak track but the existing
weak denominator lower bound `D_t ≥ Z/2` is enough to extract the sharp
expectation rate from this centered bound.

Proof decomposes via `pair_product_expansion` into 4 pieces:
- `∫ (dot a · dot b - m) · gW · exp(-s_t)` (centered leading), bounded `K/t`
  using parity vanishing of the cubic-jet correction `t·cV((√t)⁻¹•u)`.
- `√t · ∫ dot a · remψ · gW · exp(-s_t)` (cross 1), bounded `K/t` via the
  even quadratic jet `qψ((√t)⁻¹•u)`.
- `√t · ∫ dot b · remφ · gW · exp(-s_t)` (cross 2), symmetric.
- `t · ∫ remφ · remψ · gW · exp(-s_t)` (quadratic), bounded `K/t` via
  product of quadratic jets.

Sub-helpers will be added in subsequent stages. -/
private theorem rescaledNumerator_centered_pair_sharp
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hφ : ObservableJetApprox φ a)
    (hψ : ObservableJetApprox ψ b)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * rescaledNumerator V t (fun w => φ w * ψ w)
          - dot a (Hinv b) * rescaledPartition V t|
        ≤ K / t := by
  -- Get sharp bounds for the four pieces.
  obtain ⟨K1, T1, hT1, h1⟩ :=
    abs_integral_centered_bilinear_sharp_le V H Hinv a b hV hGauss
  obtain ⟨K2, T2, hT2, h2⟩ :=
    abs_integral_dot_mul_jet_remainder_sharp_le V ψ H Hinv a b hV hψ hGauss
  obtain ⟨K3, T3, hT3, h3⟩ :=
    abs_integral_dot_mul_jet_remainder_sharp_le V φ H Hinv b a hV hφ hGauss
  obtain ⟨K4, T4, hT4, h4⟩ :=
    abs_integral_remainder_remainder_sharp_le V φ ψ H Hinv a b hV hφ hψ hGauss
  refine ⟨K1 + K2 + K3 + K4,
    max 1 (max T1 (max T2 (max T3 T4))), le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := le_of_max_le_left ht
  have ht_rest : max T1 (max T2 (max T3 T4)) ≤ t := le_of_max_le_right ht
  have ht_T1 : T1 ≤ t := le_of_max_le_left ht_rest
  have ht_R2 : max T2 (max T3 T4) ≤ t := le_of_max_le_right ht_rest
  have ht_T2 : T2 ≤ t := le_of_max_le_left ht_R2
  have ht_R3 : max T3 T4 ≤ t := le_of_max_le_right ht_R2
  have ht_T3 : T3 ≤ t := le_of_max_le_left ht_R3
  have ht_T4 : T4 ≤ t := le_of_max_le_right ht_R3
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_ge_one : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
  -- Sharp bounds at t.
  have h1_t := h1 t ht_T1
  have h2_t := h2 t ht_T2
  have h3_t := h3 t ht_T3
  have h4_t := h4 t ht_T4
  -- Notation for the four integrals.
  set m : ℝ := dot a (Hinv b) with hm_def
  set I1 : ℝ := ∫ u : ι → ℝ, (dot a u * dot b u - m) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) with hI1_def
  set I2 : ℝ := ∫ u : ι → ℝ, dot a u *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) with hI2_def
  set I3 : ℝ := ∫ u : ι → ℝ, dot b u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) with hI3_def
  set I4 : ℝ := ∫ u : ι → ℝ,
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) with hI4_def
  -- The centered numerator decomposes into I1 + √t · I2 + √t · I3 + t · I4.
  -- Algebraic identity (~300 LOC of integrability bookkeeping); proof
  -- deferred — see notes/sharp_helpers_recipe.md for the recipe (extract
  -- as a separate lemma rescaledNumerator_centered_pair_decomposition).
  have h_decomp : t * rescaledNumerator V t (fun w => φ w * ψ w)
        - m * rescaledPartition V t
        = I1 + Real.sqrt t * I2 + Real.sqrt t * I3 + t * I4 := by
    sorry
  rw [h_decomp]
  -- Triangle inequality.
  calc |I1 + Real.sqrt t * I2 + Real.sqrt t * I3 + t * I4|
      ≤ |I1| + |Real.sqrt t * I2| + |Real.sqrt t * I3| + |t * I4| := by
        have h_a := abs_add_le (I1 + Real.sqrt t * I2 + Real.sqrt t * I3) (t * I4)
        have h_b := abs_add_le (I1 + Real.sqrt t * I2) (Real.sqrt t * I3)
        have h_c := abs_add_le I1 (Real.sqrt t * I2)
        linarith
    _ = |I1| + Real.sqrt t * |I2| + Real.sqrt t * |I3| + t * |I4| := by
        rw [abs_mul (Real.sqrt t), abs_mul (Real.sqrt t), abs_mul t,
            abs_of_pos hsqrt_pos, abs_of_pos ht_pos]
    _ ≤ K1 / t + Real.sqrt t * (K2 / (t * Real.sqrt t)) +
          Real.sqrt t * (K3 / (t * Real.sqrt t)) + t * (K4 / t ^ 2) := by
        have hI1_b : |I1| ≤ K1 / t := h1_t
        have hI2_b := mul_le_mul_of_nonneg_left h2_t hsqrt_pos.le
        have hI3_b := mul_le_mul_of_nonneg_left h3_t hsqrt_pos.le
        have hI4_b := mul_le_mul_of_nonneg_left h4_t ht_pos.le
        linarith
    _ = (K1 + K2 + K3 + K4) / t := by
        rw [show (t : ℝ) ^ 2 = t * t from sq t]
        field_simp

end CenteredNumerator

section MainTheorem

/-- **`lem:laplace_cov` (sharp-rate version, statement only)**.

For potential `V` with odd cubic jet `cV` and quartic remainder, observables
`φ, ψ` with even quadratic jets `qφ, qψ` and cubic remainders, and the
analytic Gaussian-moment package `LaplaceCovHypotheses`, the sharp rate

  `∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
     |t · gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / t`

holds. This corresponds to the primer's `Cov_t[φ,ψ] = (1/t)⟨a, H⁻¹b⟩ + O(t⁻²)`.

The proof composes:
1. A centered-numerator bound `|t·N_t(φψ) - m·D_t| ≤ K_N/t`
   (Stage 3, exploits parity vanishing of the leading `1/√t` correction).
2. The existing weak denominator lower bound `D_t ≥ Z/2`.
3. The existing weak single-observable expectation bound `|E_t[φ]| ≤ K/t`,
   so that `t · E_t[φ] · E_t[ψ] = O(1/t)` is absorbed.

Statement is locked in here; proof is in progress. -/
theorem gibbsCov_first_order_rate_sharp
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hφ : ObservableJetApprox φ a)
    (hψ : ObservableJetApprox ψ b)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / t := by
  -- Pull the three asymptote constants.
  obtain ⟨K_num, T_num, hT_num, h_num⟩ :=
    rescaledNumerator_centered_pair_sharp V φ ψ H Hinv a b hV hφ hψ hGauss
  obtain ⟨T_den, hT_den, h_den⟩ :=
    rescaledPartition_ge_half_gaussianZ V H Hinv hV.toPotentialApprox hGauss
  obtain ⟨K_phi, T_phi, hT_phi, h_phi⟩ :=
    rescaledExpectation_observable_bound_inv V φ H Hinv a hV.toPotentialApprox
      hφ.toObservableApprox hGauss
  obtain ⟨K_psi, T_psi, hT_psi, h_psi⟩ :=
    rescaledExpectation_observable_bound_inv V ψ H Hinv b hV.toPotentialApprox
      hψ.toObservableApprox hGauss
  have hZ_pos := hGauss.Z_pos
  -- K and T₀ bookkeeping.
  set K : ℝ := 2 * K_num / gaussianZ H + |K_phi * K_psi| with hK_def
  refine ⟨K, max T_num (max T_den (max T_phi T_psi)), ?_, ?_⟩
  · exact le_max_of_le_left hT_num
  intro t ht
  have ht_num : T_num ≤ t := le_of_max_le_left ht
  have ht_rest : max T_den (max T_phi T_psi) ≤ t := le_of_max_le_right ht
  have ht_den : T_den ≤ t := le_of_max_le_left ht_rest
  have ht_pp : max T_phi T_psi ≤ t := le_of_max_le_right ht_rest
  have ht_phi : T_phi ≤ t := le_of_max_le_left ht_pp
  have ht_psi : T_psi ≤ t := le_of_max_le_right ht_pp
  have ht_pos : 0 < t := lt_of_lt_of_le (by linarith [hT_num]) ht_num
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  -- Specific bounds at t.
  have h_num_t := h_num t ht_num
  have h_den_t := h_den t ht_den
  have h_phi_t := h_phi t ht_phi
  have h_psi_t := h_psi t ht_psi
  -- Rewrite gibbsCov via rescaledCov.
  rw [gibbsCov_eq_rescaledCov V φ ψ ht_pos]
  unfold rescaledCov
  -- t · (E_t[φψ] - E_t[φ]·E_t[ψ]) - m
  --   = (t · E_t[φψ] - m) - (t · E_t[φ] · E_t[ψ])
  --   where E_t[X] = N_t(X)/D_t.
  have hD_pos : 0 < rescaledPartition V t :=
    lt_of_lt_of_le (by linarith [hZ_pos]) h_den_t
  -- t · E_t[φψ] - m = (t · N_t(φψ) - m · D_t) / D_t.
  have h_centered_eq :
      t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b)
        = (t * rescaledNumerator V t (fun w => φ w * ψ w)
            - dot a (Hinv b) * rescaledPartition V t) / rescaledPartition V t := by
    unfold rescaledExpectation
    field_simp
  -- Decompose: t · gibbsCov - m = (t · E_t[φψ] - m) - t · E_t[φ] · E_t[ψ].
  have h_decompose :
      t * (rescaledExpectation V t (fun w => φ w * ψ w)
            - rescaledExpectation V t φ * rescaledExpectation V t ψ)
        - dot a (Hinv b)
        = (t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b))
          - t * (rescaledExpectation V t φ * rescaledExpectation V t ψ) := by
    ring
  rw [h_decompose]
  -- Bound each piece.
  -- Piece 1: |t · E_t[φψ] - m| ≤ (2/Z) · K_num/t.
  have hpart1 : |t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b)|
      ≤ 2 * K_num / gaussianZ H / t := by
    rw [h_centered_eq, abs_div, abs_of_pos hD_pos]
    calc |t * rescaledNumerator V t (fun w => φ w * ψ w)
              - dot a (Hinv b) * rescaledPartition V t| / rescaledPartition V t
        ≤ (K_num / t) / rescaledPartition V t :=
          div_le_div_of_nonneg_right h_num_t hD_pos.le
      _ ≤ (K_num / t) / (gaussianZ H / 2) := by
          apply div_le_div_of_nonneg_left _ (by linarith) h_den_t
          exact le_trans (abs_nonneg _) h_num_t
      _ = 2 * K_num / gaussianZ H / t := by field_simp
  -- Piece 2: |t · E_t[φ] · E_t[ψ]| ≤ |K_phi · K_psi| / t.
  have hpart2 : |t * (rescaledExpectation V t φ * rescaledExpectation V t ψ)|
      ≤ |K_phi * K_psi| / t := by
    rw [abs_mul, abs_of_pos ht_pos, abs_mul]
    have h_prod_le :
        |rescaledExpectation V t φ| * |rescaledExpectation V t ψ|
          ≤ (K_phi / t) * (K_psi / t) :=
      mul_le_mul h_phi_t h_psi_t (abs_nonneg _) (le_trans (abs_nonneg _) h_phi_t)
    calc t * (|rescaledExpectation V t φ| * |rescaledExpectation V t ψ|)
        ≤ t * ((K_phi / t) * (K_psi / t)) :=
          mul_le_mul_of_nonneg_left h_prod_le ht_pos.le
      _ = (K_phi * K_psi) / t := by field_simp
      _ ≤ |K_phi * K_psi| / t := by
          apply div_le_div_of_nonneg_right (le_abs_self _) ht_pos.le
  -- Combine via triangle inequality.
  calc |((t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b))
          - t * (rescaledExpectation V t φ * rescaledExpectation V t ψ))|
      ≤ |t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b)|
        + |t * (rescaledExpectation V t φ * rescaledExpectation V t ψ)| :=
        abs_sub _ _
    _ ≤ 2 * K_num / gaussianZ H / t + |K_phi * K_psi| / t :=
        add_le_add hpart1 hpart2
    _ = K / t := by
        rw [hK_def]; ring

end MainTheorem

end Laplace.Multi
