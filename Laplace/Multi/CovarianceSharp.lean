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

* Stage 0 — jet hypothesis structures (`PotentialJetApprox`,
  `ObservableJetApprox`): complete.
* Stage 1 — scalar Taylor-1 bound `abs_exp_neg_sub_one_add_le`: complete.
* Stage 2 — rescaled decomposition lemmas
  (`abs_rescaledPerturbation_sub_scaledCubicJet_le`,
  `abs_rescaledObservable_quadratic_error_le`): complete.
* Stage 3 — centered numerator bound: structurally complete with two
  small technical sorries (both inside helper 1E):
  - `abs_integral_corrected_bracket_centered_bilinear_le` has its main
    proof structure formalized (constants, Glocal+Gtail majorants,
    pointwise bound, integrability). Two remaining sorries: the
    integral computations `∫ Glocal = K_loc/t` and `∫ Gtail = K_tail/t`,
    each ~50 LOC of integral_add + integral_const_mul composition.

  All other Stage 3 components are fully formalized:
  - The algebraic identity `h_decomp` inside
    `rescaledNumerator_centered_pair_sharp` (via `pair_product_expansion`
    + integral linearity).
  - Sharp helper 4 `abs_integral_remainder_remainder_sharp_le` (K/t²,
    Glocal+Gtail with k = 4 indicator).
  - Sharp helpers 2/3 `abs_integral_dot_mul_jet_remainder_sharp_le`
    (K/(t·√t), parity decomposition `qψ + r₃` plus Glocal+Gtail with
    k = 3 indicator).
* Stage 4 — `gibbsCov_first_order_rate_sharp`: complete given Stage 3.

The helper-1 statement reduces (via `integral_centered_bilinear_eq_corrected_bracket`)
to bounding `|∫ B · gW · (exp(-s_t) - 1 + c_t)|` by `K/t`, where
`B := dot a · dot b - m`, `c_t := t · cV((√t)⁻¹•u)`. Both `∫ B · gW = 0`
(centering identity) and `∫ B · gW · c_t = 0` (parity) are formalized.
The remaining work is the integrand-level Glocal+Gtail bound on the
corrected bracket itself.

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
  /-- Higher-moment integrability for the *bare* Gaussian weight:
  `‖u‖^k · gaussianWeight H u` is integrable for every `k : ℕ`.

  The corrected-bracket sharp-track decomposition (helper 1) requires
  `B · gW · c_t` integrability, which dominates by `polynomial(‖u‖) · gW`
  with degrees up to 5–6. The existing `LaplaceCovHypotheses.int_uk_uj_gW`
  only delivers quadratic Gaussian moments, so we include this stronger
  integrability hypothesis here. -/
  int_norm_pow_gW : ∀ k : ℕ,
    Integrable (fun u : ι → ℝ => ‖u‖ ^ k * gaussianWeight H u)
  /-- Coercive lower bound on the Gaussian quadratic form: there is a
  positive constant `H_coercive_const` such that `H_coercive_const · ‖u‖² ≤
  quadForm H u`. Used by the corrected-bracket pointwise bound to write
  `gW(u) ≤ exp(-(H_coercive_const/2)·‖u‖²)` and combine with `exp|s_t|`
  for Gaussian decay on the local ball.

  This is equivalent to *positive-definiteness* of `H` (which is implied
  by `LaplaceCovHypotheses.int_gW` plus injectivity, but the implication
  is non-trivial to formalise). The coercive constant also implies
  `int_norm_pow_gW` (via `integrable_norm_pow_mul_exp_neg_const_sq`),
  but we keep both fields for direct use. -/
  H_coercive_const : ℝ
  H_coercive_const_pos : 0 < H_coercive_const
  H_coercive_bound : ∀ u : ι → ℝ, H_coercive_const * ‖u‖ ^ 2 ≤ quadForm H u

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

/-- **Integrability of `dot a · dot b · gW`** (no `exp(-s_t)` factor) under
`LaplaceCovHypotheses`. Dominated by `A · B · ‖u‖² · gW`, and `‖u‖² · gW`
is integrable from `integrable_sq_norm_mul_gaussianWeight`. -/
private lemma integrable_dot_mul_dot_mul_gaussianWeight
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCovHypotheses H Hinv)
    (a b : ι → ℝ) :
    Integrable (fun u : ι → ℝ => dot a u * dot b u * gaussianWeight H u) := by
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
  have h_dom : Integrable (fun u : ι → ℝ =>
      A * B * (‖u‖ ^ 2 * gaussianWeight H u)) :=
    (integrable_sq_norm_mul_gaussianWeight hGauss).const_mul (A * B)
  refine h_dom.mono' ?_ ?_
  · exact ((h_dot_a_cont.mul h_dot_b_cont).mul
      (continuous_gaussianWeight H)).aestronglyMeasurable
  · filter_upwards with u
    have h_dot_a_le : |dot a u| ≤ A * ‖u‖ := by
      rw [hA_def]; exact abs_dot_le_l1_mul_norm a u
    have h_dot_b_le : |dot b u| ≤ B * ‖u‖ := by
      rw [hB_def]; exact abs_dot_le_l1_mul_norm b u
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_gW_nn, abs_mul]
    calc |dot a u| * |dot b u| * gaussianWeight H u
        ≤ (A * ‖u‖) * (B * ‖u‖) * gaussianWeight H u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h_dot_a_le h_dot_b_le (abs_nonneg _)
              (mul_nonneg hA_nn (norm_nonneg _))) h_gW_nn
      _ = A * B * (‖u‖ ^ 2 * gaussianWeight H u) := by
          rw [show ‖u‖ ^ 2 = ‖u‖ * ‖u‖ from sq _]; ring

/-- **Integrability of `dot c · qψ((√t)⁻¹•u) · gW`** (no exp factor).

Required for the parity reduction `∫ dot c · qψ · gW · exp(-s_t)
= ∫ dot c · qψ · gW · (exp(-s_t) - 1)` in helpers 2/3. Dominated by

  `|dot c · qψ · gW| ≤ DC · Cq / t · ‖u‖^3 · gW`,

and `‖u‖^3 · gW` integrable via `hV.int_norm_pow_gW 3`. -/
private lemma integrable_dot_mul_quadJet_mul_gaussianWeight
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialJetApprox V H) [Nonempty ι]
    (qψ : (ι → ℝ) → ℝ) (qψ_continuous : Continuous qψ)
    {Cq : ℝ} (hCq_nn : 0 ≤ Cq)
    (h_qψ_bound : ∀ w : ι → ℝ, |qψ w| ≤ Cq * ‖w‖ ^ 2)
    (dotCoef : ι → ℝ)
    {t : ℝ} (ht_pos : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u) := by
  set DC : ℝ := ∑ i, |dotCoef i| with hDC_def
  have hDC_nn : 0 ≤ DC := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_inv_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hsqrt_t_pos
  have h_dot_cont : Continuous (fun u : ι → ℝ => dot dotCoef u) := by
    unfold dot
    exact continuous_finset_sum _
      (fun i _ => continuous_const.mul (continuous_apply i))
  have h_smul_cont : Continuous (fun u : ι → ℝ => (Real.sqrt t)⁻¹ • u) :=
    continuous_const_smul _
  -- Dominant: K · ‖u‖^3 · gW where K = DC · Cq / t.
  set K : ℝ := DC * Cq / t with hK_def
  have hK_nn : 0 ≤ K := by
    rw [hK_def]
    exact div_nonneg (mul_nonneg hDC_nn hCq_nn) ht_pos.le
  have h_dom : Integrable (fun u : ι → ℝ =>
      K * (‖u‖ ^ 3 * gaussianWeight H u)) :=
    (hV.int_norm_pow_gW 3).const_mul K
  refine h_dom.mono' ?_ ?_
  · exact ((h_dot_cont.mul (qψ_continuous.comp h_smul_cont)).mul
      (continuous_gaussianWeight H)).aestronglyMeasurable
  · filter_upwards with u
    have h_dot_le : |dot dotCoef u| ≤ DC * ‖u‖ := by
      rw [hDC_def]; exact abs_dot_le_l1_mul_norm dotCoef u
    have h_qψ_le : |qψ ((Real.sqrt t)⁻¹ • u)| ≤ Cq * ‖u‖ ^ 2 / t := by
      have h := h_qψ_bound ((Real.sqrt t)⁻¹ • u)
      have h_norm_sm_sq : ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_t_inv_pos]
        rw [show ((Real.sqrt t)⁻¹ * ‖u‖) ^ 2
              = ((Real.sqrt t) ^ 2)⁻¹ * ‖u‖ ^ 2 from by
            rw [mul_pow, inv_pow]]
        rw [Real.sq_sqrt ht_pos.le]; ring
      rw [h_norm_sm_sq] at h
      rw [show Cq * ‖u‖ ^ 2 / t = Cq * (‖u‖ ^ 2 / t) from by ring]
      exact h
    have h_gW_nn : 0 ≤ gaussianWeight H u := (gaussianWeight_pos H u).le
    have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
    have h_DC_norm_nn : 0 ≤ DC * ‖u‖ := mul_nonneg hDC_nn h_norm_nn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_gW_nn, abs_mul]
    calc |dot dotCoef u| * |qψ ((Real.sqrt t)⁻¹ • u)| * gaussianWeight H u
        ≤ (DC * ‖u‖) * (Cq * ‖u‖ ^ 2 / t) * gaussianWeight H u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h_dot_le h_qψ_le (abs_nonneg _) h_DC_norm_nn) h_gW_nn
      _ = K * (‖u‖ ^ 3 * gaussianWeight H u) := by
          rw [hK_def]
          rw [show ‖u‖ ^ 3 = ‖u‖ * ‖u‖ ^ 2 from by ring]
          field_simp

/-- **Integrability of `dot c · qψ((√t)⁻¹•u) · gW · exp(-s_t)`**.

Required for the integral-level decomposition in helpers 2/3. Dominated by

  `(DC · Cq / t) · ‖u‖³ · exp(-c·‖u‖²)`

via `rescaled_weight_le_coercive`. -/
private lemma integrable_dot_mul_quadJet_mul_rescaled_weight
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (V_continuous : Continuous V)
    (qψ : (ι → ℝ) → ℝ) (qψ_continuous : Continuous qψ)
    {Cq : ℝ} (hCq_nn : 0 ≤ Cq)
    (h_qψ_bound : ∀ w : ι → ℝ, |qψ w| ≤ Cq * ‖w‖ ^ 2)
    (dotCoef : ι → ℝ)
    {t : ℝ} (ht_pos : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
  set DC : ℝ := ∑ i, |dotCoef i| with hDC_def
  have hDC_nn : 0 ≤ DC := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_inv_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hsqrt_t_pos
  have h_dot_cont : Continuous (fun u : ι → ℝ => dot dotCoef u) := by
    unfold dot
    exact continuous_finset_sum _
      (fun i _ => continuous_const.mul (continuous_apply i))
  have h_smul_cont : Continuous (fun u : ι → ℝ => (Real.sqrt t)⁻¹ • u) :=
    continuous_const_smul _
  -- Dominant: K · ‖u‖^3 · exp(-c·‖u‖²) where K = DC · Cq / t.
  set K : ℝ := DC * Cq / t with hK_def
  have hK_nn : 0 ≤ K := by
    rw [hK_def]
    exact div_nonneg (mul_nonneg hDC_nn hCq_nn) ht_pos.le
  have h_dom : Integrable (fun u : ι → ℝ =>
      K * (‖u‖ ^ 3 * Real.exp (-(c * ‖u‖ ^ 2)))) :=
    (integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 3).const_mul K
  refine h_dom.mono' ?_ ?_
  · exact (((h_dot_cont.mul (qψ_continuous.comp h_smul_cont)).mul
      (continuous_gaussianWeight H)).mul (Real.continuous_exp.comp
        (continuous_rescaledPerturbation V_continuous H t).neg)).aestronglyMeasurable
  · filter_upwards with u
    have h_dot_le : |dot dotCoef u| ≤ DC * ‖u‖ := by
      rw [hDC_def]; exact abs_dot_le_l1_mul_norm dotCoef u
    have h_qψ_le : |qψ ((Real.sqrt t)⁻¹ • u)| ≤ Cq * ‖u‖ ^ 2 / t := by
      have h := h_qψ_bound ((Real.sqrt t)⁻¹ • u)
      have h_norm_sm_sq : ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_t_inv_pos]
        rw [show ((Real.sqrt t)⁻¹ * ‖u‖) ^ 2
              = ((Real.sqrt t) ^ 2)⁻¹ * ‖u‖ ^ 2 from by
            rw [mul_pow, inv_pow]]
        rw [Real.sq_sqrt ht_pos.le]; ring
      rw [h_norm_sm_sq] at h
      rw [show Cq * ‖u‖ ^ 2 / t = Cq * (‖u‖ ^ 2 / t) from by ring]
      exact h
    have h_rw_le := rescaled_weight_le_coercive V H hc_pos h_coer ht_pos u
    have h_rw_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
    have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
    have h_DC_norm_nn : 0 ≤ DC * ‖u‖ := mul_nonneg hDC_nn h_norm_nn
    have h_qψ_div_nn : 0 ≤ Cq * ‖u‖ ^ 2 / t :=
      div_nonneg (mul_nonneg hCq_nn (sq_nonneg _)) ht_pos.le
    rw [Real.norm_eq_abs]
    rw [show dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
          = (dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u)) *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) from by ring]
    rw [abs_mul, abs_of_nonneg h_rw_nn, abs_mul]
    calc |dot dotCoef u| * |qψ ((Real.sqrt t)⁻¹ • u)| *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        ≤ (DC * ‖u‖) * (Cq * ‖u‖ ^ 2 / t) *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h_dot_le h_qψ_le (abs_nonneg _) h_DC_norm_nn) h_rw_nn
      _ ≤ (DC * ‖u‖) * (Cq * ‖u‖ ^ 2 / t) *
            Real.exp (-(c * ‖u‖ ^ 2)) := by
          have h_lhs_nn : 0 ≤ DC * ‖u‖ * (Cq * ‖u‖ ^ 2 / t) :=
            mul_nonneg h_DC_norm_nn h_qψ_div_nn
          exact mul_le_mul_of_nonneg_left h_rw_le h_lhs_nn
      _ = K * (‖u‖ ^ 3 * Real.exp (-(c * ‖u‖ ^ 2))) := by
          rw [hK_def]
          rw [show ‖u‖ ^ 3 = ‖u‖ * ‖u‖ ^ 2 from by ring]
          field_simp

/-- **Integrability of `(dot a u · dot b u - m) · gW · t · cV((√t)⁻¹•u)`**.

Under `PotentialJetApprox` (which provides `cV_bound` and the higher-moment
integrability `int_norm_pow_gW`), the centered-bilinear-times-scaled-cubic
integrand is integrable. Dominated pointwise by

  `(A·B·‖u‖² + |m|) · gW · (Cc/√t) · ‖u‖³`

which after expansion gives a sum of `‖u‖^5 · gW` and `‖u‖^3 · gW` pieces,
each integrable from `hV.int_norm_pow_gW`. -/
private lemma integrable_centered_bilinear_mul_gaussianWeight_mul_scaledCubic
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialJetApprox V H) [Nonempty ι]
    (a b : ι → ℝ) (m : ℝ)
    {t : ℝ} (ht_pos : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      (dot a u * dot b u - m) * gaussianWeight H u *
        (t * hV.cV ((Real.sqrt t)⁻¹ • u))) := by
  set A : ℝ := ∑ i, |a i| with hA_def
  set B : ℝ := ∑ i, |b i| with hB_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set Cc : ℝ := hV.cV_bound_const with hCc_def
  have hCc_nn : 0 ≤ Cc := hV.cV_bound_const_nonneg
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_inv_nn : 0 ≤ (Real.sqrt t)⁻¹ := inv_nonneg.mpr hsqrt_t_pos.le
  have hsqrt_t_sq : Real.sqrt t * Real.sqrt t = t :=
    Real.mul_self_sqrt ht_pos.le
  have h_dot_a_cont : Continuous (fun u : ι → ℝ => dot a u) := by
    unfold dot
    exact continuous_finset_sum _
      (fun i _ => continuous_const.mul (continuous_apply i))
  have h_dot_b_cont : Continuous (fun u : ι → ℝ => dot b u) := by
    unfold dot
    exact continuous_finset_sum _
      (fun i _ => continuous_const.mul (continuous_apply i))
  have h_smul_cont : Continuous (fun u : ι → ℝ => (Real.sqrt t)⁻¹ • u) :=
    continuous_const_smul _
  set K1 : ℝ := (Cc / Real.sqrt t) * (A * B) with hK1_def
  set K2 : ℝ := (Cc / Real.sqrt t) * |m| with hK2_def
  have hK1_nn : 0 ≤ K1 := by
    rw [hK1_def]
    exact mul_nonneg (div_nonneg hCc_nn hsqrt_t_pos.le)
      (mul_nonneg hA_nn hB_nn)
  have hK2_nn : 0 ≤ K2 := by
    rw [hK2_def]
    exact mul_nonneg (div_nonneg hCc_nn hsqrt_t_pos.le) (abs_nonneg _)
  have h_dom : Integrable (fun u : ι → ℝ =>
      K1 * (‖u‖ ^ 5 * gaussianWeight H u) +
      K2 * (‖u‖ ^ 3 * gaussianWeight H u)) :=
    ((hV.int_norm_pow_gW 5).const_mul K1).add
      ((hV.int_norm_pow_gW 3).const_mul K2)
  refine h_dom.mono' ?_ ?_
  · exact ((((h_dot_a_cont.mul h_dot_b_cont).sub continuous_const).mul
      (continuous_gaussianWeight H)).mul (continuous_const.mul
        (hV.cV_continuous.comp h_smul_cont))).aestronglyMeasurable
  · filter_upwards with u
    have h_dot_a_le : |dot a u| ≤ A * ‖u‖ := by
      rw [hA_def]; exact abs_dot_le_l1_mul_norm a u
    have h_dot_b_le : |dot b u| ≤ B * ‖u‖ := by
      rw [hB_def]; exact abs_dot_le_l1_mul_norm b u
    have h_diff_le : |dot a u * dot b u - m| ≤ A * B * ‖u‖ ^ 2 + |m| := by
      have h_prod : |dot a u| * |dot b u| ≤ (A * ‖u‖) * (B * ‖u‖) :=
        mul_le_mul h_dot_a_le h_dot_b_le (abs_nonneg _)
          (mul_nonneg hA_nn (norm_nonneg _))
      calc |dot a u * dot b u - m|
          ≤ |dot a u * dot b u| + |m| := abs_sub _ _
        _ = |dot a u| * |dot b u| + |m| := by rw [abs_mul]
        _ ≤ (A * ‖u‖) * (B * ‖u‖) + |m| := by linarith
        _ = A * B * ‖u‖ ^ 2 + |m| := by
            rw [show ‖u‖ ^ 2 = ‖u‖ * ‖u‖ from sq _]; ring
    have h_norm_smul : ‖(Real.sqrt t)⁻¹ • u‖ = (Real.sqrt t)⁻¹ * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt_t_inv_nn]
    have h_cV_le : |hV.cV ((Real.sqrt t)⁻¹ • u)| ≤
        Cc * ((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3 := by
      have h_raw := hV.cV_bound ((Real.sqrt t)⁻¹ • u)
      rw [h_norm_smul] at h_raw
      rw [show ((Real.sqrt t)⁻¹ * ‖u‖) ^ 3
            = ((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3 from by ring] at h_raw
      have hCc_eq : Cc = hV.cV_bound_const := rfl
      linarith
    have h_t_cV_le : |t * hV.cV ((Real.sqrt t)⁻¹ • u)| ≤
        (Cc / Real.sqrt t) * ‖u‖ ^ 3 := by
      rw [abs_mul, abs_of_pos ht_pos]
      have h_step : t * |hV.cV ((Real.sqrt t)⁻¹ • u)| ≤
          t * (Cc * ((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3) :=
        mul_le_mul_of_nonneg_left h_cV_le ht_pos.le
      have h_simp : t * (Cc * ((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3)
          = (Cc / Real.sqrt t) * ‖u‖ ^ 3 := by
        have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
        have h_t_inv_sq : t * ((Real.sqrt t)⁻¹) ^ 2 = 1 := by
          rw [show ((Real.sqrt t)⁻¹) ^ 2 = ((Real.sqrt t) ^ 2)⁻¹ from inv_pow _ _,
              Real.sq_sqrt ht_pos.le]
          exact mul_inv_cancel₀ ht_pos.ne'
        calc t * (Cc * ((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3)
            = (t * ((Real.sqrt t)⁻¹) ^ 2) *
                (Cc * (Real.sqrt t)⁻¹ * ‖u‖ ^ 3) := by ring
          _ = 1 * (Cc * (Real.sqrt t)⁻¹ * ‖u‖ ^ 3) := by rw [h_t_inv_sq]
          _ = (Cc / Real.sqrt t) * ‖u‖ ^ 3 := by
                rw [div_eq_mul_inv]; ring
      linarith
    have h_gW_pos : 0 < gaussianWeight H u := gaussianWeight_pos H u
    have h_lhs_eq : (dot a u * dot b u - m) * gaussianWeight H u *
        (t * hV.cV ((Real.sqrt t)⁻¹ • u))
        = (dot a u * dot b u - m) * (t * hV.cV ((Real.sqrt t)⁻¹ • u)) *
          gaussianWeight H u := by ring
    rw [Real.norm_eq_abs, h_lhs_eq, abs_mul, abs_of_pos h_gW_pos, abs_mul]
    have h_pos : (0 : ℝ) ≤ A * B * ‖u‖ ^ 2 + |m| := by
      have h1 : 0 ≤ A * B * ‖u‖ ^ 2 :=
        mul_nonneg (mul_nonneg hA_nn hB_nn) (sq_nonneg _)
      linarith [abs_nonneg m]
    have h_step1 : |dot a u * dot b u - m| *
        |t * hV.cV ((Real.sqrt t)⁻¹ • u)| ≤
        (A * B * ‖u‖ ^ 2 + |m|) * ((Cc / Real.sqrt t) * ‖u‖ ^ 3) :=
      mul_le_mul h_diff_le h_t_cV_le (abs_nonneg _) h_pos
    have h_step2 : (A * B * ‖u‖ ^ 2 + |m|) * ((Cc / Real.sqrt t) * ‖u‖ ^ 3)
        = K1 * ‖u‖ ^ 5 + K2 * ‖u‖ ^ 3 := by
      rw [hK1_def, hK2_def, show ‖u‖ ^ 5 = ‖u‖ ^ 2 * ‖u‖ ^ 3 from by ring]
      ring
    have h_step3 : (K1 * ‖u‖ ^ 5 + K2 * ‖u‖ ^ 3) * gaussianWeight H u
        = K1 * (‖u‖ ^ 5 * gaussianWeight H u) +
          K2 * (‖u‖ ^ 3 * gaussianWeight H u) := by ring
    calc |dot a u * dot b u - m| *
            |t * hV.cV ((Real.sqrt t)⁻¹ • u)| * gaussianWeight H u
        ≤ ((A * B * ‖u‖ ^ 2 + |m|) * ((Cc / Real.sqrt t) * ‖u‖ ^ 3)) *
            gaussianWeight H u :=
          mul_le_mul_of_nonneg_right h_step1 h_gW_pos.le
      _ = (K1 * ‖u‖ ^ 5 + K2 * ‖u‖ ^ 3) * gaussianWeight H u := by rw [h_step2]
      _ = K1 * (‖u‖ ^ 5 * gaussianWeight H u) +
          K2 * (‖u‖ ^ 3 * gaussianWeight H u) := h_step3

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

/-- **Centering identity for the bilinear factor**: for `m := dot a (Hinv b)`,
the centered bilinear factor `dot a u · dot b u - m` integrates to zero
against the Gaussian weight.

This is the `[1] = 0` piece of the corrected-bracket decomposition in
sharp helper 1: it is *not* a parity argument, but rather a direct
consequence of the second-moment formula `gaussian_dot_mul_dot`. -/
lemma integral_centered_bilinear_gaussianWeight_eq_zero
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)} [Nonempty ι]
    (hGauss : LaplaceCovHypotheses H Hinv)
    (a b : ι → ℝ) :
    ∫ u : ι → ℝ, (dot a u * dot b u - dot a (Hinv b)) *
      gaussianWeight H u = 0 := by
  set m := dot a (Hinv b) with hm_def
  -- ∫ dot a · dot b · gW = Z · m via gaussian_dot_mul_dot.
  have h_dot_dot : ∫ u : ι → ℝ, dot a u * dot b u * gaussianWeight H u
      = gaussianZ H * m :=
    gaussian_dot_mul_dot H Hinv hGauss.H_inv_right hGauss.H_inj
      hGauss.int_gW hGauss.int_uk_uj_gW hGauss.int_uj_Hi_gW
      hGauss.fubini_ibp a b
  -- ∫ m · gW = m · Z (constant times the partition definition).
  have h_const : ∫ u : ι → ℝ, m * gaussianWeight H u = m * gaussianZ H := by
    rw [MeasureTheory.integral_const_mul]
    rfl
  -- Integrability companions for the integral_sub split.
  have h_int_dot_dot :
      Integrable (fun u : ι → ℝ => dot a u * dot b u * gaussianWeight H u) :=
    integrable_dot_mul_dot_mul_gaussianWeight hGauss a b
  have h_int_m : Integrable (fun u : ι → ℝ => m * gaussianWeight H u) :=
    hGauss.int_gW.const_mul m
  -- Split via `integral_sub`.
  rw [show (fun u : ι → ℝ => (dot a u * dot b u - m) * gaussianWeight H u)
        = fun u => dot a u * dot b u * gaussianWeight H u
                 - m * gaussianWeight H u from by
        funext u; ring]
  rw [MeasureTheory.integral_sub h_int_dot_dot h_int_m, h_dot_dot, h_const]
  ring

/-- **Corrected-bracket decomposition for the centered bilinear integrand**.

The original integral `∫ B · gW · exp(-s_t)` (where `B(u) := dot a u · dot b u
- m`, `m := dot a (Hinv b)`) equals the *corrected-bracket* form

  `∫ B · gW · (exp(-s_t) - 1 + c_t)`

where `c_t(u) := t · cV((√t)⁻¹•u)`. The argument:
- pointwise `B · gW · (exp(-s_t) - 1 + c_t)
            = B · gW · exp(-s_t) - B · gW + B · gW · c_t`;
- `∫ B · gW = 0` (centering identity, helper 1A);
- `∫ B · gW · c_t = 0` (parity vanishing — `B` is even, `c_t` is odd).

This is the cleanest setup for the K/t bound: the corrected bracket is
`O(‖u‖^4/t · gW · exp_factor)` locally (Stage 1's Taylor remainder + Stage
2's quartic remainder), so the K/t rate falls out of the local bound + an
indicator-trick tail. -/
private lemma integral_centered_bilinear_eq_corrected_bracket
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ) [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv)
    {t : ℝ} (ht_pos : 0 < t) :
    ∫ u : ι → ℝ, (dot a u * dot b u - dot a (Hinv b)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
    = ∫ u : ι → ℝ, (dot a u * dot b u - dot a (Hinv b)) *
        gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
         t * hV.cV ((Real.sqrt t)⁻¹ • u)) := by
  set m := dot a (Hinv b) with hm_def
  -- Define the three integrand pieces as named functions for clean
  -- elaboration of `MeasureTheory.integral_{add,sub}`.
  set F : (ι → ℝ) → ℝ := fun u =>
    (dot a u * dot b u - m) * gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u)) with hF_def
  set G : (ι → ℝ) → ℝ := fun u =>
    (dot a u * dot b u - m) * gaussianWeight H u with hG_def
  set K : (ι → ℝ) → ℝ := fun u =>
    (dot a u * dot b u - m) * gaussianWeight H u *
      (t * hV.cV ((Real.sqrt t)⁻¹ • u)) with hK_def
  -- Pointwise: RHS_integrand = F - G + K.
  have h_pt : ∀ u : ι → ℝ,
      (dot a u * dot b u - m) * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
         t * hV.cV ((Real.sqrt t)⁻¹ • u))
      = F u - G u + K u := by
    intro u; rw [hF_def, hG_def, hK_def]; ring
  -- Integrability of F (the original LHS integrand).
  have h_int_dd_exp : Integrable (fun u : ι → ℝ =>
      dot a u * dot b u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_dot_mul_dot_mul_rescaled_weight V H a b
      hV.toPotentialApprox.V_continuous
      hV.toPotentialApprox.coercive_const_pos
      hV.toPotentialApprox.coercive_bound ht_pos
  have h_int_m_exp : Integrable (fun u : ι → ℝ =>
      m * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) :=
    (integrable_rescaled_weight V hV.toPotentialApprox.V_continuous H
      hV.toPotentialApprox.coercive_const_pos
      hV.toPotentialApprox.coercive_bound ht_pos).const_mul m
  have h_int_F : Integrable F := by
    rw [hF_def]
    have h_sum := h_int_dd_exp.sub h_int_m_exp
    apply h_sum.congr
    filter_upwards with u
    simp only [Pi.sub_apply]; ring
  -- Integrability of G.
  have h_int_G : Integrable G := by
    rw [hG_def]
    have h_dd := integrable_dot_mul_dot_mul_gaussianWeight hGauss a b
    have h_m := hGauss.int_gW.const_mul m
    have h_sum := h_dd.sub h_m
    apply h_sum.congr
    filter_upwards with u
    simp only [Pi.sub_apply]; ring
  -- Integrability of K.
  have h_int_K : Integrable K := by
    rw [hK_def]
    exact integrable_centered_bilinear_mul_gaussianWeight_mul_scaledCubic
      V H hV a b m ht_pos
  -- Integrability of F - G.
  have h_int_FsubG : Integrable (F - G) := h_int_F.sub h_int_G
  -- ∫ G = 0 (centering identity).
  have h_int_G_zero : ∫ u, G u = 0 := by
    rw [hG_def]
    exact integral_centered_bilinear_gaussianWeight_eq_zero hGauss a b
  -- ∫ K = 0 (parity).
  have h_int_K_zero : ∫ u, K u = 0 := by
    rw [hK_def]
    have h_rearrange : ∀ u : ι → ℝ,
        (dot a u * dot b u - m) * gaussianWeight H u *
          (t * hV.cV ((Real.sqrt t)⁻¹ • u))
        = t * ((dot a u * dot b u - m) *
              hV.cV ((Real.sqrt t)⁻¹ • u) *
              gaussianWeight H u) := by intro u; ring
    rw [show (fun u : ι → ℝ => (dot a u * dot b u - m) * gaussianWeight H u *
              (t * hV.cV ((Real.sqrt t)⁻¹ • u)))
            = fun u => t * ((dot a u * dot b u - m) *
                  hV.cV ((Real.sqrt t)⁻¹ • u) *
                  gaussianWeight H u) from funext h_rearrange]
    rw [MeasureTheory.integral_const_mul,
        integral_centered_bilinear_cubicJet_eq_zero H hV.cV hV.cV_odd a b m t]
    ring
  -- ∫ RHS_integrand = ∫ (F - G + K). Split via integral linearity:
  -- ∫ (F - G + K) = ∫ ((F + K) - G) = ∫ (F + K) - ∫ G = ∫ F + ∫ K - ∫ G.
  -- Using ∫ G = 0 and ∫ K = 0 (centering identity + parity), this equals ∫ F.
  -- Provide the F + K integrability witness in pointwise-lambda form so that
  -- `MeasureTheory.integral_sub` matches the rewrite pattern.
  have h_int_F_plus_K : Integrable (fun u : ι → ℝ => F u + K u) :=
    h_int_F.add h_int_K
  have h_int_RHS_eq : ∫ u : ι → ℝ,
        (dot a u * dot b u - m) * gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
           t * hV.cV ((Real.sqrt t)⁻¹ • u))
      = ∫ u, F u := by
    -- Step 1: Rewrite integrand to (F u + K u) - G u.
    rw [show (fun u : ι → ℝ =>
              (dot a u * dot b u - m) * gaussianWeight H u *
                (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                 t * hV.cV ((Real.sqrt t)⁻¹ • u)))
            = fun u => (F u + K u) - G u from funext (fun u => by
              rw [h_pt u]; ring)]
    -- Step 2: Apply integral_sub then integral_add.
    rw [MeasureTheory.integral_sub h_int_F_plus_K h_int_G,
        MeasureTheory.integral_add h_int_F h_int_K,
        h_int_G_zero, h_int_K_zero]
    ring
  rw [hF_def] at h_int_RHS_eq
  rw [← h_int_RHS_eq]

end ParityLemmas

section CorrectedBracketBounds

/-- **Pointwise local bound on the corrected bracket**.

On the local ball `‖u‖ ≤ hV.jet_radius · √t`, the corrected bracket
`exp(-s_t) - 1 + c_t` satisfies

  `|exp(-s_t) - 1 + c_t| ≤ s_t² · exp|s_t| + jet_const · ‖u‖^4 / t`.

The bound combines:
- Stage 1 (`abs_exp_neg_sub_one_add_le`) for `|exp(-s) - (1-s)| ≤ s² · exp|s|`;
- Stage 2 (`abs_rescaledPerturbation_sub_scaledCubicJet_le`) for
  `|c_t - s_t| ≤ jet_const · ‖u‖^4 / t` on the local ball.

This is the integrand-level pointwise step toward helper 1's K/t bound. -/
private lemma abs_corrected_bracket_local_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    {t : ℝ} (ht_pos : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ hV.jet_radius * Real.sqrt t) :
    |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
        t * hV.cV ((Real.sqrt t)⁻¹ • u)|
      ≤ rescaledPerturbation V H t u ^ 2 *
            Real.exp |rescaledPerturbation V H t u|
        + hV.jet_const * ‖u‖ ^ 4 / t := by
  have h_taylor :=
    abs_exp_neg_sub_one_add_le (rescaledPerturbation V H t u)
  have h_stage2 :=
    abs_rescaledPerturbation_sub_scaledCubicJet_le V hV.cV H
      hV.jet_bound ht_pos u hu
  have h_identity :
      Real.exp (-(rescaledPerturbation V H t u)) - 1 +
          t * hV.cV ((Real.sqrt t)⁻¹ • u)
        = (Real.exp (-(rescaledPerturbation V H t u)) -
              (1 - rescaledPerturbation V H t u))
          + (t * hV.cV ((Real.sqrt t)⁻¹ • u) -
              rescaledPerturbation V H t u) := by
    ring
  rw [h_identity]
  have h_neg : t * hV.cV ((Real.sqrt t)⁻¹ • u) -
        rescaledPerturbation V H t u
      = -(rescaledPerturbation V H t u -
          t * hV.cV ((Real.sqrt t)⁻¹ • u)) := by ring
  calc |(Real.exp (-(rescaledPerturbation V H t u)) -
              (1 - rescaledPerturbation V H t u))
          + (t * hV.cV ((Real.sqrt t)⁻¹ • u) -
              rescaledPerturbation V H t u)|
      ≤ |Real.exp (-(rescaledPerturbation V H t u)) -
              (1 - rescaledPerturbation V H t u)|
        + |t * hV.cV ((Real.sqrt t)⁻¹ • u) -
              rescaledPerturbation V H t u| := abs_add_le _ _
    _ = |Real.exp (-(rescaledPerturbation V H t u)) -
              (1 - rescaledPerturbation V H t u)|
        + |rescaledPerturbation V H t u -
              t * hV.cV ((Real.sqrt t)⁻¹ • u)| := by
            rw [h_neg, abs_neg]
    _ ≤ rescaledPerturbation V H t u ^ 2 *
            Real.exp |rescaledPerturbation V H t u|
          + hV.jet_const * ‖u‖ ^ 4 / t := by linarith

/-- **Pointwise bound on `gW · |exp(-s_t) - 1 + c_t|` on the local ball**.

Assuming the V coercive bound `c·‖w‖² ≤ V w` (hence
`gW(u) · exp|s_t| ≤ exp(-(c'/4)·‖u‖²)` for ρ small) and the H coercive
bound `c'·‖u‖² ≤ quadForm H u`, this packages helper 1C with the gW
pointwise control to give

  `gW · |exp(-s_t) - 1 + c_t| ≤ (Cs²·‖u‖^6 + jet_const·‖u‖^4) / t ·
                                  exp(-(c'/4)·‖u‖²)`

on `‖u‖ ≤ ρ·√t` with `ρ ≤ min(jet_radius, c'/(4·max(Cs,1)))`. -/
private lemma abs_gaussianWeight_mul_corrected_bracket_local_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hρ_le_jet_R : ρ ≤ hV.jet_radius)
    (hρ_le_local_R : ρ ≤ hV.toPotentialApprox.local_radius)
    (hρ_decay : hV.toPotentialApprox.local_const * ρ ≤
        hV.H_coercive_const / 4)
    {t : ℝ} (ht_pos : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ ρ * Real.sqrt t) :
    gaussianWeight H u *
        |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
          t * hV.cV ((Real.sqrt t)⁻¹ • u)|
      ≤ (hV.toPotentialApprox.local_const ^ 2 * ‖u‖ ^ 6 +
          hV.jet_const * ‖u‖ ^ 4) / t *
          Real.exp (-(hV.H_coercive_const / 4 * ‖u‖ ^ 2)) := by
  set Cs := hV.toPotentialApprox.local_const with hCs_def
  set R := hV.toPotentialApprox.local_radius with hR_def
  set c' := hV.H_coercive_const with hc'_def
  have hCs_nn : 0 ≤ Cs := hV.toPotentialApprox.local_const_nonneg
  have hR_pos : 0 < R := hV.toPotentialApprox.local_radius_pos
  have hc'_pos : 0 < c' := hV.H_coercive_const_pos
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_sq : Real.sqrt t * Real.sqrt t = t :=
    Real.mul_self_sqrt ht_pos.le
  have hu_le_R_sqrt : ‖u‖ ≤ R * Real.sqrt t :=
    le_trans hu (mul_le_mul_of_nonneg_right hρ_le_local_R hsqrt_t_pos.le)
  have hu_le_jetR_sqrt : ‖u‖ ≤ hV.jet_radius * Real.sqrt t :=
    le_trans hu (mul_le_mul_of_nonneg_right hρ_le_jet_R hsqrt_t_pos.le)
  -- Helper 1C local pointwise bound on the corrected bracket (no gW factor).
  have h_bracket :=
    abs_corrected_bracket_local_le V H hV ht_pos u hu_le_jetR_sqrt
  -- |s_t| ≤ Cs·‖u‖³/√t locally (V cubic bound).
  have h_st_le := abs_rescaledPerturbation_le V H
    hV.toPotentialApprox.local_bound ht_pos u hu_le_R_sqrt
  -- On local ball: |s_t| ≤ Cs·ρ·‖u‖² since ‖u‖/√t ≤ ρ.
  have h_norm_quotient : ‖u‖ / Real.sqrt t ≤ ρ := by
    rw [div_le_iff₀ hsqrt_t_pos]; linarith
  have h_st_quad : |rescaledPerturbation V H t u| ≤ Cs * ρ * ‖u‖ ^ 2 := by
    calc |rescaledPerturbation V H t u|
        ≤ Cs * ‖u‖ ^ 3 / Real.sqrt t := h_st_le
      _ = Cs * (‖u‖ / Real.sqrt t) * ‖u‖ ^ 2 := by
          have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
          field_simp
      _ ≤ Cs * ρ * ‖u‖ ^ 2 := by
          have h_pow_nn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
          have h_step : Cs * (‖u‖ / Real.sqrt t) ≤ Cs * ρ :=
            mul_le_mul_of_nonneg_left h_norm_quotient hCs_nn
          exact mul_le_mul_of_nonneg_right h_step h_pow_nn
  -- s_t² ≤ Cs²·‖u‖^6/t (square of |s_t| ≤ Cs·‖u‖³/√t).
  have h_st_sq : rescaledPerturbation V H t u ^ 2 ≤ Cs ^ 2 * ‖u‖ ^ 6 / t := by
    have h_abs_sq : rescaledPerturbation V H t u ^ 2 =
        |rescaledPerturbation V H t u| ^ 2 := by
      rw [sq_abs]
    rw [h_abs_sq]
    have h_div_nn : 0 ≤ Cs * ‖u‖ ^ 3 / Real.sqrt t :=
      div_nonneg (mul_nonneg hCs_nn (pow_nonneg (norm_nonneg _) _)) hsqrt_t_pos.le
    calc |rescaledPerturbation V H t u| ^ 2
        ≤ (Cs * ‖u‖ ^ 3 / Real.sqrt t) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) h_st_le 2
      _ = Cs ^ 2 * ‖u‖ ^ 6 / t := by
          rw [div_pow]
          rw [show (Cs * ‖u‖ ^ 3) ^ 2 = Cs ^ 2 * ‖u‖ ^ 6 from by ring,
              show (Real.sqrt t) ^ 2 = t from Real.sq_sqrt ht_pos.le]
  -- exp|s_t| ≤ exp(Cs·ρ·‖u‖²) on local ball.
  have h_exp_st : Real.exp |rescaledPerturbation V H t u| ≤
      Real.exp (Cs * ρ * ‖u‖ ^ 2) :=
    Real.exp_le_exp.mpr h_st_quad
  -- gW(u) ≤ exp(-(c'/2)·‖u‖²) using H_coercive_bound.
  have h_gW_le : gaussianWeight H u ≤ Real.exp (-(c' / 2 * ‖u‖ ^ 2)) := by
    rw [gaussianWeight_def]
    apply Real.exp_le_exp.mpr
    have h_coer := hV.H_coercive_bound u
    linarith [hV.H_coercive_bound u]
  have h_gW_pos : 0 < gaussianWeight H u := gaussianWeight_pos H u
  -- gW · exp|s_t| ≤ exp(-(c'/4)·‖u‖²) (using Cs·ρ ≤ c'/4).
  have h_gW_exp_st : gaussianWeight H u *
      Real.exp |rescaledPerturbation V H t u|
        ≤ Real.exp (-(c' / 4 * ‖u‖ ^ 2)) := by
    have h_norm_pow_nn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    have h_combine : gaussianWeight H u *
        Real.exp |rescaledPerturbation V H t u|
          ≤ Real.exp (-(c' / 2 * ‖u‖ ^ 2)) *
            Real.exp (Cs * ρ * ‖u‖ ^ 2) :=
      mul_le_mul h_gW_le h_exp_st (Real.exp_pos _).le (Real.exp_pos _).le
    have h_exp_combine : Real.exp (-(c' / 2 * ‖u‖ ^ 2)) *
        Real.exp (Cs * ρ * ‖u‖ ^ 2)
          = Real.exp (-(c' / 2 * ‖u‖ ^ 2) + Cs * ρ * ‖u‖ ^ 2) := by
      rw [← Real.exp_add]
    rw [h_exp_combine] at h_combine
    have h_arg_le : -(c' / 2 * ‖u‖ ^ 2) + Cs * ρ * ‖u‖ ^ 2 ≤
        -(c' / 4 * ‖u‖ ^ 2) := by
      have h_coef : Cs * ρ - c' / 2 ≤ -(c' / 4) := by linarith
      have : (-(c' / 2 * ‖u‖ ^ 2) + Cs * ρ * ‖u‖ ^ 2)
            = (Cs * ρ - c' / 2) * ‖u‖ ^ 2 := by ring
      rw [this]
      have h_mul := mul_le_mul_of_nonneg_right h_coef h_norm_pow_nn
      linarith
    have h_exp_le : Real.exp (-(c' / 2 * ‖u‖ ^ 2) + Cs * ρ * ‖u‖ ^ 2) ≤
        Real.exp (-(c' / 4 * ‖u‖ ^ 2)) := Real.exp_le_exp.mpr h_arg_le
    linarith
  -- Combine: gW · |exp(-s_t)-1+c_t| ≤ gW · (s_t² · exp|s_t| + jet_const · ‖u‖^4/t).
  have h_bracket_pos : 0 ≤ |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
      t * hV.cV ((Real.sqrt t)⁻¹ • u)| := abs_nonneg _
  have h_step1 : gaussianWeight H u *
      |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
        t * hV.cV ((Real.sqrt t)⁻¹ • u)|
      ≤ gaussianWeight H u *
        (rescaledPerturbation V H t u ^ 2 *
            Real.exp |rescaledPerturbation V H t u|
          + hV.jet_const * ‖u‖ ^ 4 / t) :=
    mul_le_mul_of_nonneg_left h_bracket h_gW_pos.le
  -- s_t² · exp|s_t| · gW ≤ s_t² · exp(-(c'/4)·‖u‖²).
  have h_st_sq_nn : 0 ≤ rescaledPerturbation V H t u ^ 2 := sq_nonneg _
  have h_step2_a : gaussianWeight H u *
      (rescaledPerturbation V H t u ^ 2 *
        Real.exp |rescaledPerturbation V H t u|)
      ≤ rescaledPerturbation V H t u ^ 2 *
        Real.exp (-(c' / 4 * ‖u‖ ^ 2)) := by
    have h_rearr : gaussianWeight H u *
        (rescaledPerturbation V H t u ^ 2 *
          Real.exp |rescaledPerturbation V H t u|)
        = rescaledPerturbation V H t u ^ 2 *
          (gaussianWeight H u *
            Real.exp |rescaledPerturbation V H t u|) := by ring
    rw [h_rearr]
    exact mul_le_mul_of_nonneg_left h_gW_exp_st h_st_sq_nn
  -- jet_const · ‖u‖^4/t · gW ≤ jet_const · ‖u‖^4/t · exp(-(c'/4)·‖u‖²).
  have hjet_div_nn : 0 ≤ hV.jet_const * ‖u‖ ^ 4 / t :=
    div_nonneg (mul_nonneg hV.jet_const_nonneg
      (pow_nonneg (norm_nonneg _) _)) ht_pos.le
  have h_gW_le_quarter : gaussianWeight H u ≤
      Real.exp (-(c' / 4 * ‖u‖ ^ 2)) := by
    have h_quarter : -(c' / 2 * ‖u‖ ^ 2) ≤ -(c' / 4 * ‖u‖ ^ 2) := by
      have : c' / 4 * ‖u‖ ^ 2 ≤ c' / 2 * ‖u‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        linarith
      linarith
    have h_exp_step : Real.exp (-(c' / 2 * ‖u‖ ^ 2)) ≤
        Real.exp (-(c' / 4 * ‖u‖ ^ 2)) := Real.exp_le_exp.mpr h_quarter
    linarith
  have h_step2_b : gaussianWeight H u * (hV.jet_const * ‖u‖ ^ 4 / t)
      ≤ hV.jet_const * ‖u‖ ^ 4 / t *
        Real.exp (-(c' / 4 * ‖u‖ ^ 2)) := by
    rw [mul_comm (gaussianWeight H u) _]
    exact mul_le_mul_of_nonneg_left h_gW_le_quarter hjet_div_nn
  -- Combine pointwise bounds.
  have h_st_bound : rescaledPerturbation V H t u ^ 2 ≤ Cs ^ 2 * ‖u‖ ^ 6 / t :=
    h_st_sq
  have h_st_sq_exp : rescaledPerturbation V H t u ^ 2 *
      Real.exp (-(c' / 4 * ‖u‖ ^ 2))
      ≤ Cs ^ 2 * ‖u‖ ^ 6 / t * Real.exp (-(c' / 4 * ‖u‖ ^ 2)) :=
    mul_le_mul_of_nonneg_right h_st_bound (Real.exp_pos _).le
  calc gaussianWeight H u *
        |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
          t * hV.cV ((Real.sqrt t)⁻¹ • u)|
      ≤ gaussianWeight H u *
        (rescaledPerturbation V H t u ^ 2 *
            Real.exp |rescaledPerturbation V H t u|
          + hV.jet_const * ‖u‖ ^ 4 / t) := h_step1
    _ = gaussianWeight H u *
          (rescaledPerturbation V H t u ^ 2 *
            Real.exp |rescaledPerturbation V H t u|)
        + gaussianWeight H u * (hV.jet_const * ‖u‖ ^ 4 / t) := by ring
    _ ≤ rescaledPerturbation V H t u ^ 2 *
          Real.exp (-(c' / 4 * ‖u‖ ^ 2))
        + hV.jet_const * ‖u‖ ^ 4 / t *
          Real.exp (-(c' / 4 * ‖u‖ ^ 2)) :=
        add_le_add h_step2_a h_step2_b
    _ ≤ Cs ^ 2 * ‖u‖ ^ 6 / t * Real.exp (-(c' / 4 * ‖u‖ ^ 2))
        + hV.jet_const * ‖u‖ ^ 4 / t *
          Real.exp (-(c' / 4 * ‖u‖ ^ 2)) := by linarith
    _ = (Cs ^ 2 * ‖u‖ ^ 6 + hV.jet_const * ‖u‖ ^ 4) / t *
          Real.exp (-(c' / 4 * ‖u‖ ^ 2)) := by
          field_simp

/-- **Global polynomial bound for the rescaled observable remainder**.

Given the polynomial-growth hypothesis `|φ(w)| ≤ K · (1 + ‖w‖^p)` and the
linear coefficient `a` (with l1-sum `A := ∑ |a i|`), for `t ≥ 1`,

  `|φ((√t)⁻¹•u) - (√t)⁻¹·dot a u| ≤ (2K + 2A) · (1 + ‖u‖^(p+1))`

globally in `u`. This is the workhorse global bound used by helpers 2/3
and helper 4 in the tail integration. -/
private lemma abs_rescaledObservable_global_le
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    {K : ℝ} {p : ℕ} (hK_nn : 0 ≤ K)
    (hpoly : ∀ w : ι → ℝ, |φ w| ≤ K * (1 + ‖w‖ ^ p))
    {t : ℝ} (ht : 1 ≤ t) (u : ι → ℝ) :
    |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u|
      ≤ (2 * K + 2 * (∑ i, |a i|)) * (1 + ‖u‖ ^ (p + 1)) := by
  set A : ℝ := ∑ i, |a i| with hA_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  have hsqrt_ge_one : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
  have hinv_sqrt_le_one : (Real.sqrt t)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hsqrt_ge_one
  have h_phi_le : |φ ((Real.sqrt t)⁻¹ • u)|
      ≤ K * (1 + ‖(Real.sqrt t)⁻¹ • u‖ ^ p) := hpoly _
  have h_norm_sm : ‖(Real.sqrt t)⁻¹ • u‖ ≤ ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos]
    exact mul_le_of_le_one_left (norm_nonneg _) hinv_sqrt_le_one
  have h_norm_sm_p : ‖(Real.sqrt t)⁻¹ • u‖ ^ p ≤ ‖u‖ ^ p :=
    pow_le_pow_left₀ (norm_nonneg _) h_norm_sm p
  have h_phi_le' : |φ ((Real.sqrt t)⁻¹ • u)| ≤ K + K * ‖u‖ ^ p := by
    calc |φ ((Real.sqrt t)⁻¹ • u)|
        ≤ K * (1 + ‖(Real.sqrt t)⁻¹ • u‖ ^ p) := h_phi_le
      _ ≤ K * (1 + ‖u‖ ^ p) :=
          mul_le_mul_of_nonneg_left (by linarith) hK_nn
      _ = K + K * ‖u‖ ^ p := by ring
  have h_dot_a_le : |dot a u| ≤ A * ‖u‖ := by
    rw [hA_def]; exact abs_dot_le_l1_mul_norm a u
  have h_lin_le : (Real.sqrt t)⁻¹ * |dot a u| ≤ A * ‖u‖ :=
    calc (Real.sqrt t)⁻¹ * |dot a u|
        ≤ 1 * (A * ‖u‖) :=
          mul_le_mul hinv_sqrt_le_one h_dot_a_le (abs_nonneg _) zero_le_one
      _ = A * ‖u‖ := by ring
  have h_step1 : |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u|
      ≤ K + K * ‖u‖ ^ p + A * ‖u‖ := by
    calc |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u|
        ≤ |φ ((Real.sqrt t)⁻¹ • u)| + |(Real.sqrt t)⁻¹ * dot a u| :=
            abs_sub _ _
      _ = |φ ((Real.sqrt t)⁻¹ • u)| + (Real.sqrt t)⁻¹ * |dot a u| := by
          rw [abs_mul, abs_of_pos hsqrt_inv_pos]
      _ ≤ (K + K * ‖u‖ ^ p) + A * ‖u‖ := add_le_add h_phi_le' h_lin_le
      _ = K + K * ‖u‖ ^ p + A * ‖u‖ := by ring
  have h_pow_le : ‖u‖ ^ p ≤ 1 + ‖u‖ ^ (p + 1) := by
    by_cases hu : ‖u‖ ≤ 1
    · have h_pow_le_one : ‖u‖ ^ p ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
      have h_pow_pos : 0 ≤ ‖u‖ ^ (p + 1) := pow_nonneg (norm_nonneg _) _
      linarith
    · push_neg at hu
      have h_le : ‖u‖ ^ p ≤ ‖u‖ ^ (p + 1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg (norm_nonneg u) p]
      linarith [pow_nonneg (norm_nonneg u) (p+1)]
  have h_norm_le_pow : ‖u‖ ≤ 1 + ‖u‖ ^ (p + 1) := by
    by_cases h1 : ‖u‖ ≤ 1
    · linarith [pow_nonneg (norm_nonneg u) (p+1)]
    · push_neg at h1
      have h_one_le : (1 : ℕ) ≤ p + 1 := Nat.le_add_left 1 p
      have h_pow_le' : ‖u‖ ^ 1 ≤ ‖u‖ ^ (p + 1) :=
        pow_le_pow_right₀ h1.le h_one_le
      rw [pow_one] at h_pow_le'
      linarith [pow_nonneg (norm_nonneg u) (p+1)]
  calc |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u|
      ≤ K + K * ‖u‖ ^ p + A * ‖u‖ := h_step1
    _ ≤ K + K * (1 + ‖u‖ ^ (p + 1)) + A * (1 + ‖u‖ ^ (p + 1)) := by
        have h1 : K * ‖u‖ ^ p ≤ K * (1 + ‖u‖ ^ (p+1)) :=
          mul_le_mul_of_nonneg_left h_pow_le hK_nn
        have h2 : A * ‖u‖ ≤ A * (1 + ‖u‖ ^ (p+1)) :=
          mul_le_mul_of_nonneg_left h_norm_le_pow hA_nn
        linarith
    _ = (K + K + A) + (K + A) * ‖u‖ ^ (p + 1) := by ring
    _ ≤ (2 * K + 2 * A) + (2 * K + 2 * A) * ‖u‖ ^ (p + 1) := by
        have h1 : K + K + A ≤ 2 * K + 2 * A := by linarith
        have h2 : (K + A) * ‖u‖ ^ (p+1) ≤ (2 * K + 2 * A) * ‖u‖ ^ (p+1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
        linarith
    _ = (2 * K + 2 * A) * (1 + ‖u‖ ^ (p + 1)) := by ring

/-- **Local pointwise bound on the product of two observable remainders**.

Under quadratic local Taylor remainders for `φ` and `ψ`,

  `|remφ(u) · remψ(u)| ≤ Cφ · Cψ · ‖u‖⁴ / t²`

on the local ball `‖u‖ ≤ min(Rφ, Rψ) · √t`. Used by sharp helper 4 to
extract the K/t² rate on the local region. -/
private lemma abs_remainder_mul_remainder_local_le
    (φ ψ : (ι → ℝ) → ℝ) (a b : ι → ℝ)
    {Cφ Cψ Rφ Rψ : ℝ}
    (hCφ_nn : 0 ≤ Cφ) (hCψ_nn : 0 ≤ Cψ)
    (h_obs_φ_local : ∀ w : ι → ℝ, ‖w‖ ≤ Rφ →
      |φ w - dot a w| ≤ Cφ * ‖w‖ ^ 2)
    (h_obs_ψ_local : ∀ w : ι → ℝ, ‖w‖ ≤ Rψ →
      |ψ w - dot b w| ≤ Cψ * ‖w‖ ^ 2)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ)
    (huφ : ‖u‖ ≤ Rφ * Real.sqrt t)
    (huψ : ‖u‖ ≤ Rψ * Real.sqrt t) :
    |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)|
      ≤ Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 := by
  have h_phi := abs_rescaledObservable_linear_error_le φ a h_obs_φ_local ht u huφ
  have h_psi := abs_rescaledObservable_linear_error_le ψ b h_obs_ψ_local ht u huψ
  have h_norm_pow_nn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have h_quotient_nn : 0 ≤ Cφ * ‖u‖ ^ 2 / t :=
    div_nonneg (mul_nonneg hCφ_nn h_norm_pow_nn) ht.le
  rw [abs_mul]
  calc |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u| *
          |ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u|
      ≤ (Cφ * ‖u‖ ^ 2 / t) * (Cψ * ‖u‖ ^ 2 / t) :=
        mul_le_mul h_phi h_psi (abs_nonneg _) h_quotient_nn
    _ = Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 := by
        rw [show Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 =
              Cφ * Cψ * (‖u‖ ^ 2 * ‖u‖ ^ 2) / (t * t) from by ring,
            show ‖u‖ ^ 2 * ‖u‖ ^ 2 = ‖u‖ ^ 4 from by ring]
        field_simp

/-- **Global polynomial bound for the product of two observable remainders**.

Composes `abs_rescaledObservable_global_le` for `φ` and `ψ`. -/
private lemma abs_remainder_mul_remainder_global_le
    (φ ψ : (ι → ℝ) → ℝ) (a b : ι → ℝ)
    {Kφ Kψ : ℝ} {p q : ℕ}
    (hKφ_nn : 0 ≤ Kφ) (hKψ_nn : 0 ≤ Kψ)
    (hpoly_φ : ∀ w : ι → ℝ, |φ w| ≤ Kφ * (1 + ‖w‖ ^ p))
    (hpoly_ψ : ∀ w : ι → ℝ, |ψ w| ≤ Kψ * (1 + ‖w‖ ^ q))
    {t : ℝ} (ht : 1 ≤ t) (u : ι → ℝ) :
    |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)|
      ≤ (2 * Kφ + 2 * (∑ i, |a i|)) * (2 * Kψ + 2 * (∑ i, |b i|)) *
          (1 + ‖u‖ ^ (p + 1)) * (1 + ‖u‖ ^ (q + 1)) := by
  rw [abs_mul]
  have h_phi := abs_rescaledObservable_global_le φ a hKφ_nn hpoly_φ ht u
  have h_psi := abs_rescaledObservable_global_le ψ b hKψ_nn hpoly_ψ ht u
  have hA_nn : 0 ≤ ∑ i, |a i| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hCφ_nn : 0 ≤ 2 * Kφ + 2 * (∑ i, |a i|) := by linarith
  have h_norm_pow_nn : 0 ≤ 1 + ‖u‖ ^ (p + 1) := by positivity
  have h_phi_rhs_nn : 0 ≤ (2 * Kφ + 2 * (∑ i, |a i|)) *
      (1 + ‖u‖ ^ (p + 1)) := mul_nonneg hCφ_nn h_norm_pow_nn
  calc |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u| *
          |ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u|
      ≤ ((2 * Kφ + 2 * (∑ i, |a i|)) * (1 + ‖u‖ ^ (p + 1))) *
          ((2 * Kψ + 2 * (∑ i, |b i|)) * (1 + ‖u‖ ^ (q + 1))) :=
        mul_le_mul h_phi h_psi (abs_nonneg _) h_phi_rhs_nn
    _ = (2 * Kφ + 2 * (∑ i, |a i|)) * (2 * Kψ + 2 * (∑ i, |b i|)) *
          (1 + ‖u‖ ^ (p + 1)) * (1 + ‖u‖ ^ (q + 1)) := by ring

/-- **Polynomial product unification**: for natural numbers `p, q`,

  `(1 + ‖u‖^(p+1)) · (1 + ‖u‖^(q+1)) ≤ 3 · (1 + ‖u‖^(p+q+2))`.

Used to dominate the rem·rem global bound by a single polynomial degree
for cleaner Gaussian-moment integration. -/
private lemma poly_pair_le_single
    (p q : ℕ) (u : ι → ℝ) :
    (1 + ‖u‖ ^ (p + 1)) * (1 + ‖u‖ ^ (q + 1)) ≤
      3 * (1 + ‖u‖ ^ (p + q + 2)) := by
  have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have h_pow_eq : ‖u‖ ^ (p + 1) * ‖u‖ ^ (q + 1) = ‖u‖ ^ (p + q + 2) := by
    rw [← pow_add]; congr 1; omega
  have h_p_pow_le : ‖u‖ ^ (p + 1) ≤ 1 + ‖u‖ ^ (p + q + 2) := by
    by_cases hu : ‖u‖ ≤ 1
    · have : ‖u‖ ^ (p + 1) ≤ 1 := pow_le_one₀ h_norm_nn hu
      have : 0 ≤ ‖u‖ ^ (p + q + 2) := pow_nonneg h_norm_nn _
      linarith
    · push_neg at hu
      have h_le : ‖u‖ ^ (p + 1) ≤ ‖u‖ ^ (p + q + 2) := by
        apply pow_le_pow_right₀ hu.le
        omega
      linarith [pow_nonneg h_norm_nn (p + q + 2)]
  have h_q_pow_le : ‖u‖ ^ (q + 1) ≤ 1 + ‖u‖ ^ (p + q + 2) := by
    by_cases hu : ‖u‖ ≤ 1
    · have : ‖u‖ ^ (q + 1) ≤ 1 := pow_le_one₀ h_norm_nn hu
      have : 0 ≤ ‖u‖ ^ (p + q + 2) := pow_nonneg h_norm_nn _
      linarith
    · push_neg at hu
      have h_le : ‖u‖ ^ (q + 1) ≤ ‖u‖ ^ (p + q + 2) := by
        apply pow_le_pow_right₀ hu.le
        omega
      linarith [pow_nonneg h_norm_nn (p + q + 2)]
  have h_pq_pow_nn : 0 ≤ ‖u‖ ^ (p + q + 2) := pow_nonneg h_norm_nn _
  calc (1 + ‖u‖ ^ (p + 1)) * (1 + ‖u‖ ^ (q + 1))
      = 1 + ‖u‖ ^ (p + 1) + ‖u‖ ^ (q + 1) +
          ‖u‖ ^ (p + 1) * ‖u‖ ^ (q + 1) := by ring
    _ = 1 + ‖u‖ ^ (p + 1) + ‖u‖ ^ (q + 1) +
          ‖u‖ ^ (p + q + 2) := by rw [h_pow_eq]
    _ ≤ 1 + (1 + ‖u‖ ^ (p + q + 2)) + (1 + ‖u‖ ^ (p + q + 2)) +
          ‖u‖ ^ (p + q + 2) := by linarith
    _ = 3 + 3 * ‖u‖ ^ (p + q + 2) := by ring
    _ = 3 * (1 + ‖u‖ ^ (p + q + 2)) := by ring

/-- **Glocal pointwise bound for the parity-reduced cross term** (helpers 2/3).

On the local ball `‖u‖ ≤ δ · √t` (with `δ ≤ R_pot`, `Cs · δ ≤ c/4`),
combining `|dot c| ≤ DC·‖u‖`, `|qψ((√t)⁻¹•u)| ≤ Cq·‖u‖²/t`, and
`|gW · (exp(-s_t) - 1)| ≤ Cs·‖u‖³/√t · exp(-(c/4)·‖u‖²)` gives

  `|dot c · qψ((√t)⁻¹•u) · gW · (exp(-s_t) - 1)|
    ≤ (DC·Cq·Cs / (t·√t)) · ‖u‖⁶ · exp(-(c/4)·‖u‖²)`.

This is the integrand-level Glocal bound after the parity reduction
(∫ dot c · qψ · gW = 0). -/
private lemma abs_dot_mul_quadJet_mul_gaussianWeight_mul_exp_sub_one_local_le
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    {c R Cs Cq : ℝ}
    (hc_pos : 0 < c) (hR_pos : 0 < R) (hCs_nn : 0 ≤ Cs) (hCq_nn : 0 ≤ Cq)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ Cs * ‖w‖ ^ 3)
    (qψ : (ι → ℝ) → ℝ)
    (h_qψ_bound : ∀ w : ι → ℝ, |qψ w| ≤ Cq * ‖w‖ ^ 2)
    (dotCoef : ι → ℝ)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_R : δ ≤ R)
    (hδ_const : Cs * δ ≤ c / 4)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ δ * Real.sqrt t) :
    |dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ ((∑ i, |dotCoef i|) * Cq * Cs / (t * Real.sqrt t)) * ‖u‖ ^ 6 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
  set DC : ℝ := ∑ i, |dotCoef i| with hDC_def
  have hDC_nn : 0 ≤ DC := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_t_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  have h_gW_exp_bound :=
    abs_gaussianWeight_mul_exp_sub_one_le_local V H hc_pos hR_pos hCs_nn
      h_coer h_local hδ_pos hδ_le_R hδ_const ht u hu
  -- |qψ((√t)⁻¹•u)| ≤ Cq · ‖u‖²/t (using ((√t)⁻¹)² = 1/t).
  have h_qψ_le : |qψ ((Real.sqrt t)⁻¹ • u)| ≤ Cq * ‖u‖ ^ 2 / t := by
    have h := h_qψ_bound ((Real.sqrt t)⁻¹ • u)
    have h_norm_sm : ‖(Real.sqrt t)⁻¹ • u‖ = (Real.sqrt t)⁻¹ * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_t_inv_pos]
    have h_norm_sm_sq : ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / t := by
      rw [h_norm_sm]
      rw [show ((Real.sqrt t)⁻¹ * ‖u‖) ^ 2
            = ((Real.sqrt t) ^ 2)⁻¹ * ‖u‖ ^ 2 from by
          rw [mul_pow, inv_pow]]
      rw [Real.sq_sqrt ht.le]
      ring
    rw [h_norm_sm_sq] at h
    -- h : |qψ ((√t)⁻¹ • u)| ≤ Cq * (‖u‖^2 / t)
    rw [show Cq * ‖u‖ ^ 2 / t = Cq * (‖u‖ ^ 2 / t) from by ring]
    exact h
  -- |dot c| ≤ DC · ‖u‖.
  have h_dot_le : |dot dotCoef u| ≤ DC * ‖u‖ := by
    rw [hDC_def]; exact abs_dot_le_l1_mul_norm dotCoef u
  -- Combine.
  have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have h_qψ_div_nn : 0 ≤ Cq * ‖u‖ ^ 2 / t :=
    div_nonneg (mul_nonneg hCq_nn (sq_nonneg _)) ht.le
  have h_gW_exp_nn : 0 ≤ Cs * ‖u‖ ^ 3 / Real.sqrt t *
      Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
    apply mul_nonneg _ (Real.exp_pos _).le
    apply div_nonneg _ hsqrt_pos.le
    exact mul_nonneg hCs_nn (pow_nonneg h_norm_nn _)
  have h_DC_norm_nn : 0 ≤ DC * ‖u‖ := mul_nonneg hDC_nn h_norm_nn
  rw [show dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)
      = (dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u)) *
        (gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)) from by ring]
  rw [abs_mul]
  rw [abs_mul (dot dotCoef u)]
  calc |dot dotCoef u| * |qψ ((Real.sqrt t)⁻¹ • u)| *
            |gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ (DC * ‖u‖) * (Cq * ‖u‖ ^ 2 / t) *
          (Cs * ‖u‖ ^ 3 / Real.sqrt t *
            Real.exp (-((c / 4) * ‖u‖ ^ 2))) := by
        have h1 : |dot dotCoef u| * |qψ ((Real.sqrt t)⁻¹ • u)| ≤
            (DC * ‖u‖) * (Cq * ‖u‖ ^ 2 / t) :=
          mul_le_mul h_dot_le h_qψ_le (abs_nonneg _) h_DC_norm_nn
        have h2_nn : 0 ≤ DC * ‖u‖ * (Cq * ‖u‖ ^ 2 / t) :=
          mul_nonneg h_DC_norm_nn h_qψ_div_nn
        exact mul_le_mul h1 h_gW_exp_bound (abs_nonneg _) h2_nn
    _ = (DC * Cq * Cs / (t * Real.sqrt t)) * ‖u‖ ^ 6 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
        rw [show ‖u‖ ^ 6 = ‖u‖ * ‖u‖ ^ 2 * ‖u‖ ^ 3 from by ring]
        field_simp

/-- **Glocal pointwise bound for the r₃ residual** (helpers 2/3).

On the local ball `‖u‖ ≤ jet_R · √t` (where `jet_R, jet_C` are the
Stage 2 sharp jet constants for the observable),

  `|dot c · (remψ - qψ((√t)⁻¹•u)) · gW · exp(-s_t)|
    ≤ (DC · jet_C / (t·√t)) · ‖u‖⁴ · exp(-c·‖u‖²)`.

Combines `|remψ - qψ((√t)⁻¹•u)| ≤ jet_C · ‖u‖³/(t·√t)` (Stage 2 sharp)
with `|dot c| ≤ DC·‖u‖` and `gW · exp(-s_t) ≤ exp(-c·‖u‖²)` (V coercive). -/
private lemma abs_dot_mul_cubic_remainder_mul_rescaled_weight_local_le
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    {c jet_R jet_C : ℝ}
    (hc_pos : 0 < c) (hjet_C_nn : 0 ≤ jet_C)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (qψ : (ι → ℝ) → ℝ) (phiGrad : ι → ℝ)
    (h_obs_jet : ∀ w : ι → ℝ, ‖w‖ ≤ jet_R →
      |φ w - (dot phiGrad w + qψ w)| ≤ jet_C * ‖w‖ ^ 3)
    (dotCoef : ι → ℝ)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ jet_R * Real.sqrt t) :
    |dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u
          - qψ ((Real.sqrt t)⁻¹ • u)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))|
      ≤ ((∑ i, |dotCoef i|) * jet_C / (t * Real.sqrt t)) * ‖u‖ ^ 4 *
          Real.exp (-(c * ‖u‖ ^ 2)) := by
  set DC : ℝ := ∑ i, |dotCoef i| with hDC_def
  have hDC_nn : 0 ≤ DC := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
  -- Stage 2 sharp local bound on r₃.
  have h_r3_le := abs_rescaledObservable_quadratic_error_le φ qψ phiGrad
    h_obs_jet ht u hu
  -- |dot c| ≤ DC · ‖u‖.
  have h_dot_le : |dot dotCoef u| ≤ DC * ‖u‖ := by
    rw [hDC_def]; exact abs_dot_le_l1_mul_norm dotCoef u
  -- gW · exp(-s_t) ≤ exp(-c·‖u‖²).
  have h_rw_le := rescaled_weight_le_coercive V H hc_pos h_coer ht u
  have h_rw_nn : 0 ≤ gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u)) :=
    mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
  -- Combine.
  have h_DC_norm_nn : 0 ≤ DC * ‖u‖ := mul_nonneg hDC_nn h_norm_nn
  have h_jet_div_nn : 0 ≤ jet_C * ‖u‖ ^ 3 / (t * Real.sqrt t) := by
    apply div_nonneg
    · exact mul_nonneg hjet_C_nn (pow_nonneg h_norm_nn _)
    · exact mul_nonneg ht.le hsqrt_pos.le
  rw [show dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
          qψ ((Real.sqrt t)⁻¹ • u)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
      = (dot dotCoef u *
          (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
            qψ ((Real.sqrt t)⁻¹ • u))) *
        (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) from by ring]
  rw [abs_mul]
  rw [abs_mul (dot dotCoef u)]
  rw [abs_of_nonneg h_rw_nn]
  calc |dot dotCoef u| *
          |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
            qψ ((Real.sqrt t)⁻¹ • u)| *
          (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
      ≤ (DC * ‖u‖) * (jet_C * ‖u‖ ^ 3 / (t * Real.sqrt t)) *
          Real.exp (-(c * ‖u‖ ^ 2)) := by
        have h1 : |dot dotCoef u| *
            |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
              qψ ((Real.sqrt t)⁻¹ • u)| ≤
            (DC * ‖u‖) * (jet_C * ‖u‖ ^ 3 / (t * Real.sqrt t)) :=
          mul_le_mul h_dot_le h_r3_le (abs_nonneg _) h_DC_norm_nn
        have h2 : (DC * ‖u‖) * (jet_C * ‖u‖ ^ 3 / (t * Real.sqrt t)) *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
            ≤ (DC * ‖u‖) * (jet_C * ‖u‖ ^ 3 / (t * Real.sqrt t)) *
              Real.exp (-(c * ‖u‖ ^ 2)) := by
          have h_lhs_nn : 0 ≤ (DC * ‖u‖) *
              (jet_C * ‖u‖ ^ 3 / (t * Real.sqrt t)) :=
            mul_nonneg h_DC_norm_nn h_jet_div_nn
          exact mul_le_mul_of_nonneg_left h_rw_le h_lhs_nn
        have h3 : |dot dotCoef u| *
              |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
                qψ ((Real.sqrt t)⁻¹ • u)| *
              (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))
            ≤ ((DC * ‖u‖) * (jet_C * ‖u‖ ^ 3 / (t * Real.sqrt t))) *
              (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u))) :=
          mul_le_mul_of_nonneg_right h1 h_rw_nn
        linarith
    _ = (DC * jet_C / (t * Real.sqrt t)) * ‖u‖ ^ 4 *
          Real.exp (-(c * ‖u‖ ^ 2)) := by
        rw [show ‖u‖ ^ 4 = ‖u‖ * ‖u‖ ^ 3 from by ring]
        field_simp

/-- **Glocal pointwise bound for helper 4**: on the local ball,

  `|remφ(u) · remψ(u) · gW · exp(-s_t)| ≤ Cφ · Cψ · ‖u‖⁴ / t² · exp(-c·‖u‖²)`

where `c` is the V coercive constant. Combines the local rem·rem bound
with `rescaled_weight_le_coercive`. -/
private lemma abs_remainder_mul_remainder_mul_rescaled_weight_local_le
    (V φ ψ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ) [Nonempty ι]
    {Cφ Cψ Rφ Rψ c : ℝ}
    (hCφ_nn : 0 ≤ Cφ) (hCψ_nn : 0 ≤ Cψ) (hc_pos : 0 < c)
    (h_obs_φ_local : ∀ w : ι → ℝ, ‖w‖ ≤ Rφ →
      |φ w - dot a w| ≤ Cφ * ‖w‖ ^ 2)
    (h_obs_ψ_local : ∀ w : ι → ℝ, ‖w‖ ≤ Rψ →
      |ψ w - dot b w| ≤ Cψ * ‖w‖ ^ 2)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ)
    (huφ : ‖u‖ ≤ Rφ * Real.sqrt t)
    (huψ : ‖u‖ ≤ Rψ * Real.sqrt t) :
    |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))|
      ≤ Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 * Real.exp (-(c * ‖u‖ ^ 2)) := by
  have h_rem_rem := abs_remainder_mul_remainder_local_le φ ψ a b
    hCφ_nn hCψ_nn h_obs_φ_local h_obs_ψ_local ht u huφ huψ
  have h_rw_bound := rescaled_weight_le_coercive V H hc_pos h_coer ht u
  have h_rw_nn : 0 ≤ gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u)) :=
    mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
  have h_rem_rem_nn : 0 ≤ Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hCφ_nn hCψ_nn)
      (pow_nonneg (norm_nonneg _) _)) (pow_pos ht 2).le
  have h_rearr : (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
      (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
      gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u))
      = ((φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)) *
        (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) := by ring
  rw [h_rearr, abs_mul, abs_of_nonneg h_rw_nn]
  calc |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)| *
          (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
      ≤ (Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2) *
          (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) :=
        mul_le_mul_of_nonneg_right h_rem_rem h_rw_nn
    _ ≤ (Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2) * Real.exp (-(c * ‖u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h_rw_bound h_rem_rem_nn

/-- **Gtail pointwise bound for the parity-reduced cross term** (helpers 2/3).

On the tail `‖u‖ > δ · √t`,

  `|dot c · qψ((√t)⁻¹•u) · gW · (exp(-s_t) - 1)|
    ≤ (2 · DC · Cq / t) · ‖u‖³ · exp(-(c/4)·‖u‖²) · exp(-(c·δ²/4)·t)`. -/
private lemma abs_dot_mul_quadJet_mul_gaussianWeight_mul_exp_sub_one_tail_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    {c R Cs Cq : ℝ}
    (hc_pos : 0 < c) (hR_pos : 0 < R) (hCs_nn : 0 ≤ Cs) (hCq_nn : 0 ≤ Cq)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ Cs * ‖w‖ ^ 3)
    (qψ : (ι → ℝ) → ℝ)
    (h_qψ_bound : ∀ w : ι → ℝ, |qψ w| ≤ Cq * ‖w‖ ^ 2)
    (dotCoef : ι → ℝ)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : δ * Real.sqrt t < ‖u‖) :
    |dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ (2 * (∑ i, |dotCoef i|) * Cq / t) * ‖u‖ ^ 3 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
          Real.exp (-((c * δ ^ 2 / 4) * t)) := by
  set DC : ℝ := ∑ i, |dotCoef i| with hDC_def
  have hDC_nn : 0 ≤ DC := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_t_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have h_gW_exp_bound :=
    abs_gaussianWeight_mul_exp_sub_one_le_tail V H hc_pos hR_pos hCs_nn
      h_coer h_local hδ_pos ht u hu
  have h_qψ_le : |qψ ((Real.sqrt t)⁻¹ • u)| ≤ Cq * ‖u‖ ^ 2 / t := by
    have h := h_qψ_bound ((Real.sqrt t)⁻¹ • u)
    have h_norm_sm_sq : ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_t_inv_pos]
      rw [show ((Real.sqrt t)⁻¹ * ‖u‖) ^ 2
            = ((Real.sqrt t) ^ 2)⁻¹ * ‖u‖ ^ 2 from by
          rw [mul_pow, inv_pow]]
      rw [Real.sq_sqrt ht.le]; ring
    rw [h_norm_sm_sq] at h
    rw [show Cq * ‖u‖ ^ 2 / t = Cq * (‖u‖ ^ 2 / t) from by ring]
    exact h
  have h_dot_le : |dot dotCoef u| ≤ DC * ‖u‖ := by
    rw [hDC_def]; exact abs_dot_le_l1_mul_norm dotCoef u
  have h_DC_norm_nn : 0 ≤ DC * ‖u‖ := mul_nonneg hDC_nn h_norm_nn
  have h_qψ_div_nn : 0 ≤ Cq * ‖u‖ ^ 2 / t :=
    div_nonneg (mul_nonneg hCq_nn (sq_nonneg _)) ht.le
  have h_exp1_nn : 0 ≤ 2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
      Real.exp (-((c * δ ^ 2 / 4) * t)) := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num) (Real.exp_pos _).le
    · exact (Real.exp_pos _).le
  rw [show dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)
      = (dot dotCoef u * qψ ((Real.sqrt t)⁻¹ • u)) *
        (gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)) from by ring]
  rw [abs_mul]
  rw [abs_mul (dot dotCoef u)]
  calc |dot dotCoef u| * |qψ ((Real.sqrt t)⁻¹ • u)| *
            |gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ (DC * ‖u‖) * (Cq * ‖u‖ ^ 2 / t) *
          (2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
            Real.exp (-((c * δ ^ 2 / 4) * t))) := by
        have h1 : |dot dotCoef u| * |qψ ((Real.sqrt t)⁻¹ • u)| ≤
            (DC * ‖u‖) * (Cq * ‖u‖ ^ 2 / t) :=
          mul_le_mul h_dot_le h_qψ_le (abs_nonneg _) h_DC_norm_nn
        have h2_nn : 0 ≤ DC * ‖u‖ * (Cq * ‖u‖ ^ 2 / t) :=
          mul_nonneg h_DC_norm_nn h_qψ_div_nn
        exact mul_le_mul h1 h_gW_exp_bound (abs_nonneg _) h2_nn
    _ = (2 * DC * Cq / t) * ‖u‖ ^ 3 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
          Real.exp (-((c * δ ^ 2 / 4) * t)) := by
        rw [show ‖u‖ ^ 3 = ‖u‖ * ‖u‖ ^ 2 from by ring]
        field_simp

/-- **Global bound on `|r₃|`** (helpers 2/3 tail).

For `t ≥ 1`, the cubic remainder
`r₃(u, t) := remψ(u) - qψ((√t)⁻¹•u)` satisfies

  `|r₃(u, t)| ≤ (2 Cφ' + Cq) · (1 + ‖u‖^(p+2))`

where `Cφ' := 2 Kφ + 2 (∑|phiGrad|)` from the global polynomial bound on
`remψ`, and `Cq` from `|qψ(w)| ≤ Cq · ‖w‖²`. -/
private lemma abs_cubic_remainder_global_le
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    {Kφ : ℝ} {p : ℕ} (hKφ_nn : 0 ≤ Kφ)
    (hpoly : ∀ w : ι → ℝ, |φ w| ≤ Kφ * (1 + ‖w‖ ^ p))
    (qψ : (ι → ℝ) → ℝ)
    {Cq : ℝ} (hCq_nn : 0 ≤ Cq)
    (h_qψ_bound : ∀ w : ι → ℝ, |qψ w| ≤ Cq * ‖w‖ ^ 2)
    {t : ℝ} (ht : 1 ≤ t) (u : ι → ℝ) :
    |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u -
        qψ ((Real.sqrt t)⁻¹ • u)|
      ≤ (2 * (2 * Kφ + 2 * (∑ i, |a i|)) + Cq) *
          (1 + ‖u‖ ^ (p + 2)) := by
  set Cφ' : ℝ := 2 * Kφ + 2 * (∑ i, |a i|) with hCφ'_def
  have hA_nn : 0 ≤ ∑ i, |a i| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hCφ'_nn : 0 ≤ Cφ' := by rw [hCφ'_def]; linarith
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have h_pow_nn : 0 ≤ ‖u‖ ^ (p + 2) := pow_nonneg h_norm_nn _
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  -- |remψ| ≤ Cφ' · (1 + ‖u‖^(p+1)).
  have h_remψ : |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u|
      ≤ Cφ' * (1 + ‖u‖ ^ (p + 1)) := by
    rw [hCφ'_def]
    exact abs_rescaledObservable_global_le φ a hKφ_nn hpoly ht u
  -- |qψ((√t)⁻¹•u)| ≤ Cq · ‖u‖²/t ≤ Cq · ‖u‖² for t ≥ 1.
  have h_qψ : |qψ ((Real.sqrt t)⁻¹ • u)| ≤ Cq * ‖u‖ ^ 2 := by
    have h := h_qψ_bound ((Real.sqrt t)⁻¹ • u)
    have h_norm_sm : ‖(Real.sqrt t)⁻¹ • u‖ ≤ ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_t_inv_pos]
      have h_inv_le_one : (Real.sqrt t)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; exact Real.one_le_sqrt.mpr ht
      exact mul_le_of_le_one_left h_norm_nn h_inv_le_one
    have h_norm_sm_sq : ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h_norm_sm 2
    calc |qψ ((Real.sqrt t)⁻¹ • u)|
        ≤ Cq * ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 := h
      _ ≤ Cq * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left h_norm_sm_sq hCq_nn
  -- ‖u‖^(p+1) ≤ 1 + ‖u‖^(p+2).
  have h_p1_le : ‖u‖ ^ (p + 1) ≤ 1 + ‖u‖ ^ (p + 2) := by
    by_cases hu : ‖u‖ ≤ 1
    · have : ‖u‖ ^ (p + 1) ≤ 1 := pow_le_one₀ h_norm_nn hu
      linarith
    · push_neg at hu
      have h_le : ‖u‖ ^ (p + 1) ≤ ‖u‖ ^ (p + 2) := by
        apply pow_le_pow_right₀ hu.le
        omega
      linarith
  -- ‖u‖^2 ≤ 1 + ‖u‖^(p+2).
  have h_2_le : ‖u‖ ^ 2 ≤ 1 + ‖u‖ ^ (p + 2) := by
    by_cases hu : ‖u‖ ≤ 1
    · have : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ h_norm_nn hu
      linarith
    · push_neg at hu
      have h_le : ‖u‖ ^ 2 ≤ ‖u‖ ^ (p + 2) := by
        apply pow_le_pow_right₀ hu.le
        omega
      linarith
  calc |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u -
            qψ ((Real.sqrt t)⁻¹ • u)|
      ≤ |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u| +
          |qψ ((Real.sqrt t)⁻¹ • u)| := by
            rw [show φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u -
                  qψ ((Real.sqrt t)⁻¹ • u)
                = (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) -
                  qψ ((Real.sqrt t)⁻¹ • u) from by ring]
            exact abs_sub _ _
    _ ≤ Cφ' * (1 + ‖u‖ ^ (p + 1)) + Cq * ‖u‖ ^ 2 :=
        add_le_add h_remψ h_qψ
    _ ≤ Cφ' * (1 + (1 + ‖u‖ ^ (p + 2))) +
          Cq * (1 + ‖u‖ ^ (p + 2)) := by
        have h1 : Cφ' * (1 + ‖u‖ ^ (p + 1)) ≤
            Cφ' * (1 + (1 + ‖u‖ ^ (p + 2))) := by
          apply mul_le_mul_of_nonneg_left _ hCφ'_nn
          linarith
        have h2 : Cq * ‖u‖ ^ 2 ≤ Cq * (1 + ‖u‖ ^ (p + 2)) :=
          mul_le_mul_of_nonneg_left h_2_le hCq_nn
        linarith
    _ = (2 * Cφ' + Cq) + (Cφ' + Cq) * ‖u‖ ^ (p + 2) := by ring
    _ ≤ (2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2)) := by
        rw [show (2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))
              = (2 * Cφ' + Cq) + (2 * Cφ' + Cq) * ‖u‖ ^ (p + 2) from by ring]
        have h_le : (Cφ' + Cq) * ‖u‖ ^ (p + 2) ≤
            (2 * Cφ' + Cq) * ‖u‖ ^ (p + 2) := by
          apply mul_le_mul_of_nonneg_right _ h_pow_nn
          linarith
        linarith

/-- **Gtail pointwise bound for the r₃ residual** (helpers 2/3, with
indicator k = 3 already applied).

On tail `‖u‖ > δ·√t` (and t ≥ 1),

  `|dot c · (remψ - qψ((√t)⁻¹•u)) · gW · exp(-s_t)| · 1_{‖u‖>δ√t}
    ≤ (DC · (2Cφ' + Cq) / (δ³·t·√t)) ·
        ‖u‖⁴ · (1 + ‖u‖^(p+2)) · exp(-c·‖u‖²)`

where `Cφ' := 2 Kφ + 2 (∑|phiGrad|)`. Combines:
- global cubic remainder bound `abs_cubic_remainder_global_le`;
- |dot c| ≤ DC·‖u‖;
- `rescaled_weight_le_coercive`;
- indicator trick `1 ≤ ‖u‖³/(δ³·t·√t)` on tail. -/
private lemma abs_dot_mul_cubic_remainder_mul_rescaled_weight_tail_le
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {Kφ : ℝ} {p : ℕ} (hKφ_nn : 0 ≤ Kφ)
    (hpoly : ∀ w : ι → ℝ, |φ w| ≤ Kφ * (1 + ‖w‖ ^ p))
    (qψ : (ι → ℝ) → ℝ)
    {Cq : ℝ} (hCq_nn : 0 ≤ Cq)
    (h_qψ_bound : ∀ w : ι → ℝ, |qψ w| ≤ Cq * ‖w‖ ^ 2)
    (dotCoef phiGrad : ι → ℝ)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (ht1 : 1 ≤ t)
    (u : ι → ℝ) (hu : δ * Real.sqrt t < ‖u‖) :
    |dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
          qψ ((Real.sqrt t)⁻¹ • u)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))|
      ≤ ((∑ i, |dotCoef i|) *
          (2 * (2 * Kφ + 2 * (∑ i, |phiGrad i|)) + Cq) /
          (δ ^ 3 * (t * Real.sqrt t))) *
          ‖u‖ ^ 4 * (1 + ‖u‖ ^ (p + 2)) *
          Real.exp (-(c * ‖u‖ ^ 2)) := by
  set DC : ℝ := ∑ i, |dotCoef i| with hDC_def
  have hDC_nn : 0 ≤ DC := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set Cφ' : ℝ := 2 * Kφ + 2 * (∑ i, |phiGrad i|) with hCφ'_def
  have hPG_nn : 0 ≤ ∑ i, |phiGrad i| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hCφ'_nn : 0 ≤ Cφ' := by rw [hCφ'_def]; linarith
  have hC_nn : 0 ≤ 2 * Cφ' + Cq := by linarith
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have hδ3_pos : 0 < δ ^ 3 := pow_pos hδ_pos 3
  have hδt_pos : 0 < δ ^ 3 * (t * Real.sqrt t) :=
    mul_pos hδ3_pos (mul_pos ht_pos hsqrt_t_pos)
  -- Global r₃ bound.
  have h_r3_le := abs_cubic_remainder_global_le φ phiGrad hKφ_nn hpoly qψ
    hCq_nn h_qψ_bound ht1 u
  -- |dot c| ≤ DC·‖u‖.
  have h_dot_le : |dot dotCoef u| ≤ DC * ‖u‖ := by
    rw [hDC_def]; exact abs_dot_le_l1_mul_norm dotCoef u
  -- Rescaled weight.
  have h_rw_le := rescaled_weight_le_coercive V H hc_pos h_coer ht_pos u
  have h_rw_nn : 0 ≤ gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u)) :=
    mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
  -- Indicator.
  have h_pow_le : (δ * Real.sqrt t) ^ 3 ≤ ‖u‖ ^ 3 :=
    pow_le_pow_left₀ (mul_pos hδ_pos hsqrt_t_pos).le hu.le 3
  have h_RT3 : (δ * Real.sqrt t) ^ 3 = δ ^ 3 * (t * Real.sqrt t) := by
    rw [mul_pow]
    rw [show (Real.sqrt t) ^ 3 = (Real.sqrt t) ^ 2 * Real.sqrt t from by ring,
        Real.sq_sqrt ht_pos.le]
  have h_indicator : 1 ≤ ‖u‖ ^ 3 / (δ ^ 3 * (t * Real.sqrt t)) := by
    rw [le_div_iff₀ hδt_pos]
    rw [show δ ^ 3 * (t * Real.sqrt t) = (δ * Real.sqrt t) ^ 3 from h_RT3.symm]
    linarith
  -- Combine.
  have h_DC_norm_nn : 0 ≤ DC * ‖u‖ := mul_nonneg hDC_nn h_norm_nn
  have h_C_pow_nn : 0 ≤ (2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2)) := by
    apply mul_nonneg hC_nn
    positivity
  rw [show dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
          qψ ((Real.sqrt t)⁻¹ • u)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
      = (dot dotCoef u *
          (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
            qψ ((Real.sqrt t)⁻¹ • u))) *
        (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) from by ring]
  rw [abs_mul, abs_of_nonneg h_rw_nn, abs_mul]
  -- Step 1: dot · r3 abs bound.
  have h_step1 : |dot dotCoef u| *
        |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
          qψ ((Real.sqrt t)⁻¹ • u)|
      ≤ (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) := by
    rw [hCφ'_def]
    exact mul_le_mul h_dot_le h_r3_le (abs_nonneg _) h_DC_norm_nn
  -- Step 2: multiply by gW · exp.
  have h_step2 : |dot dotCoef u| *
        |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
          qψ ((Real.sqrt t)⁻¹ • u)| *
        (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
      ≤ (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
        Real.exp (-(c * ‖u‖ ^ 2)) := by
    have h_a := mul_le_mul_of_nonneg_right h_step1 h_rw_nn
    have h_b : (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
        (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
        ≤ (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
          Real.exp (-(c * ‖u‖ ^ 2)) := by
      have h_lhs_nn : 0 ≤ (DC * ‖u‖) *
          ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) :=
        mul_nonneg h_DC_norm_nn h_C_pow_nn
      exact mul_le_mul_of_nonneg_left h_rw_le h_lhs_nn
    linarith
  -- Step 3: multiply by indicator gain.
  have h_RHS_nn : 0 ≤ (DC * ‖u‖) *
      ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
      Real.exp (-(c * ‖u‖ ^ 2)) := by
    have h1 : 0 ≤ (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) :=
      mul_nonneg h_DC_norm_nn h_C_pow_nn
    exact mul_nonneg h1 (Real.exp_pos _).le
  calc |dot dotCoef u| *
            |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
              qψ ((Real.sqrt t)⁻¹ • u)| *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
      ≤ (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
          Real.exp (-(c * ‖u‖ ^ 2)) := h_step2
    _ ≤ (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
          Real.exp (-(c * ‖u‖ ^ 2)) *
          (‖u‖ ^ 3 / (δ ^ 3 * (t * Real.sqrt t))) := by
        calc (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
              Real.exp (-(c * ‖u‖ ^ 2))
            = (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
              Real.exp (-(c * ‖u‖ ^ 2)) * 1 := (mul_one _).symm
          _ ≤ (DC * ‖u‖) * ((2 * Cφ' + Cq) * (1 + ‖u‖ ^ (p + 2))) *
              Real.exp (-(c * ‖u‖ ^ 2)) *
              (‖u‖ ^ 3 / (δ ^ 3 * (t * Real.sqrt t))) :=
            mul_le_mul_of_nonneg_left h_indicator h_RHS_nn
    _ = (DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t))) *
          ‖u‖ ^ 4 * (1 + ‖u‖ ^ (p + 2)) *
          Real.exp (-(c * ‖u‖ ^ 2)) := by
        rw [show ‖u‖ ^ 4 = ‖u‖ * ‖u‖ ^ 3 from by ring]
        field_simp

end CorrectedBracketBounds

section SharpHelpers

/-- **Bound on the corrected-bracket integral** (the technical heart of
sharp helper 1).

Given the centered bilinear factor `B(u) := dot a u · dot b u - m` and the
scaled cubic jet `c_t(u) := t · cV((√t)⁻¹•u)`, we bound

  `|∫ B · gW · (exp(-s_t) - 1 + c_t)| ≤ K/t`.

The argument splits the integral by `1_{‖u‖ ≤ ρ√t} + 1_{‖u‖ > ρ√t}`:

* **Local** (`‖u‖ ≤ ρ√t`): use Stage 1 (`|exp(-r) - (1-r)| ≤ r² · exp|r|`)
  and Stage 2 (`|s_t - c_t| ≤ C₄·‖u‖^4/t`). Pick `ρ` small enough that
  `gW · exp|s_t|` decays as a Gaussian on the local ball, then the
  integrand is `O(‖u‖^p / t · exp(-α·‖u‖²))` for various `p`, with
  finite Gaussian moments.

* **Tail** (`‖u‖ > ρ√t`): use the indicator trick
  `1 ≤ ‖u‖² / (ρ²·t)` to gain `1/t` from the tail mass, combined with
  the crude bound `|exp(-s_t) - 1 + c_t| ≤ exp(-s_t) + 1 + |c_t|`
  and existing rescaled-weight integrability.

This is the Glocal+Gtail bookkeeping that mirrors the weak helpers but at
the sharp scale. ~500-700 LOC of integral arithmetic — deferred. -/
private lemma abs_integral_corrected_bracket_centered_bilinear_le
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |∫ u : ι → ℝ, (dot a u * dot b u - dot a (Hinv b)) *
          gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
           t * hV.cV ((Real.sqrt t)⁻¹ • u))|
        ≤ K / t := by
  -- Constants.
  set c := hV.toPotentialApprox.coercive_const with hc_def
  have hc_pos : 0 < c := hV.toPotentialApprox.coercive_const_pos
  have h_coer := hV.toPotentialApprox.coercive_bound
  set Cs := hV.toPotentialApprox.local_const with hCs_def
  set R_pot := hV.toPotentialApprox.local_radius with hR_pot_def
  have hCs_nn : 0 ≤ Cs := hV.toPotentialApprox.local_const_nonneg
  have hR_pot_pos : 0 < R_pot := hV.toPotentialApprox.local_radius_pos
  have h_V_local := hV.toPotentialApprox.local_bound
  set jet_R := hV.jet_radius with hjet_R_def
  set jet_C := hV.jet_const with hjet_C_def
  have hjet_R_pos : 0 < jet_R := hV.jet_radius_pos
  have hjet_C_nn : 0 ≤ jet_C := hV.jet_const_nonneg
  set Cc := hV.cV_bound_const with hCc_def
  have hCc_nn : 0 ≤ Cc := hV.cV_bound_const_nonneg
  set c' := hV.H_coercive_const with hc'_def
  have hc'_pos : 0 < c' := hV.H_coercive_const_pos
  set m : ℝ := dot a (Hinv b) with hm_def
  set A : ℝ := ∑ i, |a i| with hA_def
  set B : ℝ := ∑ i, |b i| with hB_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- Choose ρ ≤ min(R_pot, jet_R, c'/(4·(Cs+1))).
  have hCs1_pos : (0 : ℝ) < Cs + 1 := by linarith
  set ρ : ℝ := min (min R_pot jet_R) (c' / (4 * (Cs + 1))) with hρ_def
  have hρ_pos : 0 < ρ :=
    lt_min (lt_min hR_pot_pos hjet_R_pos) (by positivity)
  have hρ_le_R_pot : ρ ≤ R_pot :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ_le_jet_R : ρ ≤ jet_R :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ_decay : Cs * ρ ≤ c' / 4 := by
    have h_le : ρ ≤ c' / (4 * (Cs + 1)) := min_le_right _ _
    calc Cs * ρ ≤ Cs * (c' / (4 * (Cs + 1))) :=
          mul_le_mul_of_nonneg_left h_le hCs_nn
      _ = (Cs / (Cs + 1)) * (c' / 4) := by field_simp
      _ ≤ 1 * (c' / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ c'/4)
          rw [div_le_one hCs1_pos]; linarith
      _ = c' / 4 := one_mul _
  -- Tail decay rate (use min(c, c'/2) for global Gaussian decay).
  set α : ℝ := min c (c' / 2) with hα_def
  have hα_pos : 0 < α := lt_min hc_pos (by linarith)
  have hα_le_c : α ≤ c := min_le_left _ _
  have hα_le_c'_half : α ≤ c' / 2 := min_le_right _ _
  -- Gaussian moment constants for Glocal.
  set M_loc_4 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 4 *
    Real.exp (-((c' / 4) * ‖u‖ ^ 2)) with hM_loc_4_def
  set M_loc_6 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 6 *
    Real.exp (-((c' / 4) * ‖u‖ ^ 2)) with hM_loc_6_def
  set M_loc_8 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 8 *
    Real.exp (-((c' / 4) * ‖u‖ ^ 2)) with hM_loc_8_def
  -- Gaussian moment constants for Gtail.
  set M_tail_4 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 4 *
    Real.exp (-(α * ‖u‖ ^ 2)) with hM_tail_4_def
  set M_tail_5 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 5 *
    Real.exp (-(α * ‖u‖ ^ 2)) with hM_tail_5_def
  set M_tail_2 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 2 *
    Real.exp (-(α * ‖u‖ ^ 2)) with hM_tail_2_def
  set M_tail_7 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 7 *
    Real.exp (-(α * ‖u‖ ^ 2)) with hM_tail_7_def
  have hM_loc_4_nn : 0 ≤ M_loc_4 := by
    rw [hM_loc_4_def]
    exact MeasureTheory.integral_nonneg fun u =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_loc_6_nn : 0 ≤ M_loc_6 := by
    rw [hM_loc_6_def]
    exact MeasureTheory.integral_nonneg fun u =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_loc_8_nn : 0 ≤ M_loc_8 := by
    rw [hM_loc_8_def]
    exact MeasureTheory.integral_nonneg fun u =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_tail_4_nn : 0 ≤ M_tail_4 := by
    rw [hM_tail_4_def]
    exact MeasureTheory.integral_nonneg fun u =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_tail_5_nn : 0 ≤ M_tail_5 := by
    rw [hM_tail_5_def]
    exact MeasureTheory.integral_nonneg fun u =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_tail_2_nn : 0 ≤ M_tail_2 := by
    rw [hM_tail_2_def]
    exact MeasureTheory.integral_nonneg fun u =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_tail_7_nn : 0 ≤ M_tail_7 := by
    rw [hM_tail_7_def]
    exact MeasureTheory.integral_nonneg fun u =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  -- K and T₀.
  -- Glocal contributes: A·B·Cs²·M_loc_8 + (A·B·jet_C + |m|·Cs²)·M_loc_6 +
  --                     |m|·jet_C·M_loc_4.
  -- Gtail contributes: (1/ρ²) · (2·A·B·M_tail_4 + 2·|m|·M_tail_2 +
  --                              A·B·Cc·M_tail_7 + |m|·Cc·M_tail_5).
  set K_loc : ℝ :=
    A * B * Cs ^ 2 * M_loc_8 +
    (A * B * jet_C + |m| * Cs ^ 2) * M_loc_6 +
    |m| * jet_C * M_loc_4 with hK_loc_def
  set K_tail : ℝ :=
    (1 / ρ ^ 2) *
    (2 * A * B * M_tail_4 + 2 * |m| * M_tail_2 +
     A * B * Cc * M_tail_7 + |m| * Cc * M_tail_5) with hK_tail_def
  refine ⟨K_loc + K_tail, 1, le_refl _, ?_⟩
  intro t ht1
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_inv_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hsqrt_pos
  have hsqrt_inv_le_one : (Real.sqrt t)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact Real.one_le_sqrt.mpr ht1
  -- Define Glocal and Gtail majorants (global functions of u).
  set Glocal : (ι → ℝ) → ℝ := fun u =>
    (A * B * ‖u‖ ^ 2 + |m|) *
      ((Cs ^ 2 * ‖u‖ ^ 6 + jet_C * ‖u‖ ^ 4) / t) *
      Real.exp (-((c' / 4) * ‖u‖ ^ 2)) with hGlocal_def
  set Gtail : (ι → ℝ) → ℝ := fun u =>
    ‖u‖ ^ 2 / (ρ ^ 2 * t) *
      ((A * B * ‖u‖ ^ 2 + |m|) * (2 + Cc * ‖u‖ ^ 3)) *
      Real.exp (-(α * ‖u‖ ^ 2)) with hGtail_def
  have hGlocal_nn : ∀ u, 0 ≤ Glocal u := by
    intro u
    rw [hGlocal_def]
    have h1 : 0 ≤ A * B * ‖u‖ ^ 2 + |m| := by
      have h1a : 0 ≤ A * B * ‖u‖ ^ 2 :=
        mul_nonneg (mul_nonneg hA_nn hB_nn) (sq_nonneg _)
      linarith [abs_nonneg m]
    have h2 : 0 ≤ (Cs ^ 2 * ‖u‖ ^ 6 + jet_C * ‖u‖ ^ 4) / t := by
      apply div_nonneg _ ht_pos.le
      have h2a : 0 ≤ Cs ^ 2 * ‖u‖ ^ 6 :=
        mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
      have h2b : 0 ≤ jet_C * ‖u‖ ^ 4 :=
        mul_nonneg hjet_C_nn (pow_nonneg (norm_nonneg _) _)
      linarith
    exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
  have hGtail_nn : ∀ u, 0 ≤ Gtail u := by
    intro u
    rw [hGtail_def]
    have h1 : 0 ≤ ‖u‖ ^ 2 / (ρ ^ 2 * t) := by
      apply div_nonneg (sq_nonneg _)
      exact mul_nonneg (pow_nonneg hρ_pos.le 2) ht_pos.le
    have h2 : 0 ≤ A * B * ‖u‖ ^ 2 + |m| := by
      have : 0 ≤ A * B * ‖u‖ ^ 2 :=
        mul_nonneg (mul_nonneg hA_nn hB_nn) (sq_nonneg _)
      linarith [abs_nonneg m]
    have h3 : 0 ≤ 2 + Cc * ‖u‖ ^ 3 := by
      have : 0 ≤ Cc * ‖u‖ ^ 3 :=
        mul_nonneg hCc_nn (pow_nonneg (norm_nonneg _) _)
      linarith
    exact mul_nonneg (mul_nonneg h1 (mul_nonneg h2 h3)) (Real.exp_pos _).le
  -- Pointwise: |F(u)| ≤ Glocal(u) + Gtail(u).
  have hpt : ∀ u : ι → ℝ,
      |(dot a u * dot b u - m) * gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
           t * hV.cV ((Real.sqrt t)⁻¹ • u))|
      ≤ Glocal u + Gtail u := by
    intro u
    -- |dot a · dot b - m| ≤ A·B·‖u‖² + |m|.
    have h_dot_a_le : |dot a u| ≤ A * ‖u‖ := by
      rw [hA_def]; exact abs_dot_le_l1_mul_norm a u
    have h_dot_b_le : |dot b u| ≤ B * ‖u‖ := by
      rw [hB_def]; exact abs_dot_le_l1_mul_norm b u
    have h_diff_le : |dot a u * dot b u - m| ≤ A * B * ‖u‖ ^ 2 + |m| := by
      have h_prod : |dot a u| * |dot b u| ≤ (A * ‖u‖) * (B * ‖u‖) :=
        mul_le_mul h_dot_a_le h_dot_b_le (abs_nonneg _)
          (mul_nonneg hA_nn (norm_nonneg _))
      calc |dot a u * dot b u - m|
          ≤ |dot a u * dot b u| + |m| := abs_sub _ _
        _ = |dot a u| * |dot b u| + |m| := by rw [abs_mul]
        _ ≤ (A * ‖u‖) * (B * ‖u‖) + |m| := by linarith
        _ = A * B * ‖u‖ ^ 2 + |m| := by
            rw [show ‖u‖ ^ 2 = ‖u‖ * ‖u‖ from sq _]; ring
    have h_diff_nn : 0 ≤ A * B * ‖u‖ ^ 2 + |m| := by
      have : 0 ≤ A * B * ‖u‖ ^ 2 :=
        mul_nonneg (mul_nonneg hA_nn hB_nn) (sq_nonneg _)
      linarith [abs_nonneg m]
    by_cases hu : ‖u‖ ≤ ρ * Real.sqrt t
    · -- Local case.
      have huρ_jet : ‖u‖ ≤ hV.jet_radius * Real.sqrt t :=
        le_trans hu (mul_le_mul_of_nonneg_right hρ_le_jet_R hsqrt_pos.le)
      have huρ_pot : ‖u‖ ≤ R_pot * Real.sqrt t :=
        le_trans hu (mul_le_mul_of_nonneg_right hρ_le_R_pot hsqrt_pos.le)
      have h_local := abs_gaussianWeight_mul_corrected_bracket_local_le
        V H hV hρ_pos hρ_le_jet_R hρ_le_R_pot hρ_decay ht_pos u hu
      -- |B · gW · brack| ≤ |B| · gW · |brack| ≤ |B| · local_bound.
      have h_F_le : |(dot a u * dot b u - m) * gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
           t * hV.cV ((Real.sqrt t)⁻¹ • u))|
          ≤ Glocal u := by
        have h_gW_pos : 0 < gaussianWeight H u := gaussianWeight_pos H u
        have h_rearr : (dot a u * dot b u - m) * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
              t * hV.cV ((Real.sqrt t)⁻¹ • u))
            = (dot a u * dot b u - m) *
              (gaussianWeight H u *
                (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                  t * hV.cV ((Real.sqrt t)⁻¹ • u))) := by ring
        rw [h_rearr, abs_mul]
        calc |dot a u * dot b u - m| *
              |gaussianWeight H u *
                (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                  t * hV.cV ((Real.sqrt t)⁻¹ • u))|
            ≤ (A * B * ‖u‖ ^ 2 + |m|) *
              ((Cs ^ 2 * ‖u‖ ^ 6 + jet_C * ‖u‖ ^ 4) / t *
                Real.exp (-(c' / 4 * ‖u‖ ^ 2))) := by
              have h_abs_split : |gaussianWeight H u *
                  (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                    t * hV.cV ((Real.sqrt t)⁻¹ • u))|
                  = gaussianWeight H u *
                  |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                    t * hV.cV ((Real.sqrt t)⁻¹ • u)| := by
                rw [abs_mul, abs_of_pos h_gW_pos]
              rw [h_abs_split]
              exact mul_le_mul h_diff_le h_local (by positivity) h_diff_nn
          _ = Glocal u := by rw [hGlocal_def]; ring
      linarith [hGtail_nn u]
    · -- Tail case.
      push_neg at hu
      have h_indicator : 1 ≤ ‖u‖ ^ 2 / (ρ ^ 2 * t) := by
        have h_pos : 0 < ρ * Real.sqrt t := mul_pos hρ_pos hsqrt_pos
        have h_pow_le : (ρ * Real.sqrt t) ^ 2 ≤ ‖u‖ ^ 2 :=
          pow_le_pow_left₀ h_pos.le hu.le 2
        have h_pow_pos : 0 < (ρ * Real.sqrt t) ^ 2 := pow_pos h_pos 2
        have h_RT2 : (ρ * Real.sqrt t) ^ 2 = ρ ^ 2 * t := by
          rw [mul_pow]; rw [Real.sq_sqrt ht_pos.le]
        rw [le_div_iff₀ (mul_pos (pow_pos hρ_pos 2) ht_pos)]
        rw [show ρ ^ 2 * t = (ρ * Real.sqrt t) ^ 2 from h_RT2.symm]
        linarith
      -- Crude bound: |corrected bracket| ≤ exp(-s_t) + 1 + |c_t|.
      have h_brack_le : |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
          t * hV.cV ((Real.sqrt t)⁻¹ • u)|
          ≤ Real.exp (-(rescaledPerturbation V H t u)) + 1 +
            t * |hV.cV ((Real.sqrt t)⁻¹ • u)| := by
        have h_exp_pos : 0 < Real.exp (-(rescaledPerturbation V H t u)) :=
          Real.exp_pos _
        have h_t_pos : 0 < t := ht_pos
        calc |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                t * hV.cV ((Real.sqrt t)⁻¹ • u)|
            ≤ |Real.exp (-(rescaledPerturbation V H t u)) - 1| +
              |t * hV.cV ((Real.sqrt t)⁻¹ • u)| := abs_add_le _ _
          _ ≤ (Real.exp (-(rescaledPerturbation V H t u)) + 1) +
              t * |hV.cV ((Real.sqrt t)⁻¹ • u)| := by
              have h1 : |Real.exp (-(rescaledPerturbation V H t u)) - 1|
                  ≤ Real.exp (-(rescaledPerturbation V H t u)) + 1 := by
                rw [abs_sub_le_iff]
                refine ⟨?_, ?_⟩ <;> linarith [h_exp_pos]
              have h2 : |t * hV.cV ((Real.sqrt t)⁻¹ • u)|
                  = t * |hV.cV ((Real.sqrt t)⁻¹ • u)| := by
                rw [abs_mul, abs_of_pos h_t_pos]
              linarith
      -- gW · (exp(-s_t) + 1 + t·|cV(...)|) ≤ 2·exp(-α·‖u‖²) + Cc·‖u‖^3·exp(-α·‖u‖²)·(1/√t)
      -- ≤ (2 + Cc·‖u‖^3)·exp(-α·‖u‖²) for t ≥ 1 (since 1/√t ≤ 1).
      have h_gW_pos : 0 < gaussianWeight H u := gaussianWeight_pos H u
      have h_rw_le := rescaled_weight_le_coercive V H hc_pos h_coer ht_pos u
      -- gW ≤ exp(-(c'/2)·‖u‖²) ≤ exp(-α·‖u‖²).
      have h_gW_le_α : gaussianWeight H u ≤ Real.exp (-(α * ‖u‖ ^ 2)) := by
        rw [gaussianWeight_def]
        apply Real.exp_le_exp.mpr
        have h_coer_H := hV.H_coercive_bound u
        have h_arg_le : -(α * ‖u‖ ^ 2) ≥ -(1 / 2 * quadForm H u) := by
          have h_α_le : α * ‖u‖ ^ 2 ≤ c' / 2 * ‖u‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hα_le_c'_half (sq_nonneg _)
          have h_qf : c' / 2 * ‖u‖ ^ 2 ≤ 1 / 2 * quadForm H u := by
            have h_pre : c' * ‖u‖ ^ 2 ≤ quadForm H u := h_coer_H
            linarith
          linarith
        linarith
      -- gW · exp(-s_t) ≤ exp(-α·‖u‖²).
      have h_rw_le_α : gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
          ≤ Real.exp (-(α * ‖u‖ ^ 2)) := by
        have h_rw_to_c := h_rw_le
        have h_arg_le : -(c * ‖u‖ ^ 2) ≤ -(α * ‖u‖ ^ 2) := by
          have h_α_le : α * ‖u‖ ^ 2 ≤ c * ‖u‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hα_le_c (sq_nonneg _)
          linarith
        have h_exp_le : Real.exp (-(c * ‖u‖ ^ 2)) ≤
            Real.exp (-(α * ‖u‖ ^ 2)) := Real.exp_le_exp.mpr h_arg_le
        linarith
      -- t · |cV((√t)⁻¹•u)| ≤ Cc/√t · ‖u‖^3 ≤ Cc·‖u‖^3 for t ≥ 1.
      have h_cV_le : t * |hV.cV ((Real.sqrt t)⁻¹ • u)| ≤ Cc * ‖u‖ ^ 3 := by
        have h_cV_bound := hV.cV_bound ((Real.sqrt t)⁻¹ • u)
        have h_norm_sm : ‖(Real.sqrt t)⁻¹ • u‖ = (Real.sqrt t)⁻¹ * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_t_inv_pos]
        have h_norm_sm_3 : ‖(Real.sqrt t)⁻¹ • u‖ ^ 3 =
            ((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3 := by
          rw [h_norm_sm]; ring
        -- t · ((√t)⁻¹)^3 = (√t)⁻¹.
        have h_t_inv_sq : t * ((Real.sqrt t)⁻¹) ^ 2 = 1 := by
          rw [show ((Real.sqrt t)⁻¹) ^ 2 = ((Real.sqrt t) ^ 2)⁻¹ from
                inv_pow _ _, Real.sq_sqrt ht_pos.le]
          exact mul_inv_cancel₀ ht_pos.ne'
        have h_t_pow : t * ((Real.sqrt t)⁻¹) ^ 3 = (Real.sqrt t)⁻¹ := by
          calc t * ((Real.sqrt t)⁻¹) ^ 3
              = (t * ((Real.sqrt t)⁻¹) ^ 2) * (Real.sqrt t)⁻¹ := by ring
            _ = 1 * (Real.sqrt t)⁻¹ := by rw [h_t_inv_sq]
            _ = (Real.sqrt t)⁻¹ := one_mul _
        have h_pow_nn : 0 ≤ ‖u‖ ^ 3 := pow_nonneg (norm_nonneg _) _
        calc t * |hV.cV ((Real.sqrt t)⁻¹ • u)|
            ≤ t * (Cc * ‖(Real.sqrt t)⁻¹ • u‖ ^ 3) :=
              mul_le_mul_of_nonneg_left h_cV_bound ht_pos.le
          _ = t * (Cc * (((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3)) := by
              rw [h_norm_sm_3]
          _ = Cc * (t * ((Real.sqrt t)⁻¹) ^ 3) * ‖u‖ ^ 3 := by ring
          _ = Cc * (Real.sqrt t)⁻¹ * ‖u‖ ^ 3 := by rw [h_t_pow]
          _ ≤ Cc * 1 * ‖u‖ ^ 3 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsqrt_inv_le_one hCc_nn) h_pow_nn
          _ = Cc * ‖u‖ ^ 3 := by ring
      -- gW · (exp(-s_t) + 1 + t·|cV(...)|) ≤ (2 + Cc·‖u‖^3) · exp(-α·‖u‖²).
      have h_gW_brack : gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) + 1 +
            t * |hV.cV ((Real.sqrt t)⁻¹ • u)|)
          ≤ (2 + Cc * ‖u‖ ^ 3) * Real.exp (-(α * ‖u‖ ^ 2)) := by
        have h_split : gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) + 1 +
              t * |hV.cV ((Real.sqrt t)⁻¹ • u)|)
            = gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)) +
              gaussianWeight H u +
              gaussianWeight H u *
                (t * |hV.cV ((Real.sqrt t)⁻¹ • u)|) := by ring
        rw [h_split]
        have h_part1 : gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
            ≤ Real.exp (-(α * ‖u‖ ^ 2)) := h_rw_le_α
        have h_part2 : gaussianWeight H u ≤ Real.exp (-(α * ‖u‖ ^ 2)) :=
          h_gW_le_α
        have h_part3 : gaussianWeight H u *
            (t * |hV.cV ((Real.sqrt t)⁻¹ • u)|)
            ≤ Cc * ‖u‖ ^ 3 * Real.exp (-(α * ‖u‖ ^ 2)) := by
          calc gaussianWeight H u *
                (t * |hV.cV ((Real.sqrt t)⁻¹ • u)|)
              ≤ Real.exp (-(α * ‖u‖ ^ 2)) *
                (t * |hV.cV ((Real.sqrt t)⁻¹ • u)|) :=
                mul_le_mul_of_nonneg_right h_gW_le_α
                  (mul_nonneg ht_pos.le (abs_nonneg _))
            _ ≤ Real.exp (-(α * ‖u‖ ^ 2)) * (Cc * ‖u‖ ^ 3) :=
                mul_le_mul_of_nonneg_left h_cV_le (Real.exp_pos _).le
            _ = Cc * ‖u‖ ^ 3 * Real.exp (-(α * ‖u‖ ^ 2)) := by ring
        linarith
      -- Now combine: |F(u)| ≤ |B| · gW · |brack| ≤ |B| · (2 + Cc·‖u‖^3) · exp(-α·‖u‖²).
      -- With indicator: ≤ (1/(ρ²·t)) · ‖u‖² · |B| · (2 + Cc·‖u‖^3) · exp(-α·‖u‖²) = Gtail(u).
      have h_F_abs : |(dot a u * dot b u - m) * gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
            t * hV.cV ((Real.sqrt t)⁻¹ • u))|
          = |dot a u * dot b u - m| * gaussianWeight H u *
            |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
              t * hV.cV ((Real.sqrt t)⁻¹ • u)| := by
        rw [show (dot a u * dot b u - m) * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                t * hV.cV ((Real.sqrt t)⁻¹ • u))
            = (dot a u * dot b u - m) *
              (gaussianWeight H u *
                (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                  t * hV.cV ((Real.sqrt t)⁻¹ • u))) from by ring]
        rw [abs_mul, abs_mul, abs_of_pos h_gW_pos]
        ring
      rw [h_F_abs]
      have h_2Cc_nn : 0 ≤ 2 + Cc * ‖u‖ ^ 3 := by
        have : 0 ≤ Cc * ‖u‖ ^ 3 :=
          mul_nonneg hCc_nn (pow_nonneg (norm_nonneg _) _)
        linarith
      have h_F_bound : |dot a u * dot b u - m| * gaussianWeight H u *
          |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
            t * hV.cV ((Real.sqrt t)⁻¹ • u)|
          ≤ (A * B * ‖u‖ ^ 2 + |m|) *
            ((2 + Cc * ‖u‖ ^ 3) * Real.exp (-(α * ‖u‖ ^ 2))) := by
        calc |dot a u * dot b u - m| * gaussianWeight H u *
                |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                  t * hV.cV ((Real.sqrt t)⁻¹ • u)|
            = |dot a u * dot b u - m| *
              (gaussianWeight H u *
                |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
                  t * hV.cV ((Real.sqrt t)⁻¹ • u)|) := by ring
          _ ≤ |dot a u * dot b u - m| *
              (gaussianWeight H u *
                (Real.exp (-(rescaledPerturbation V H t u)) + 1 +
                  t * |hV.cV ((Real.sqrt t)⁻¹ • u)|)) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_left h_brack_le h_gW_pos.le
          _ ≤ (A * B * ‖u‖ ^ 2 + |m|) *
              ((2 + Cc * ‖u‖ ^ 3) * Real.exp (-(α * ‖u‖ ^ 2))) := by
              apply mul_le_mul h_diff_le h_gW_brack _ h_diff_nn
              apply mul_nonneg (gaussianWeight_pos H u).le
              have h_exp_pos := Real.exp_pos (-(rescaledPerturbation V H t u))
              linarith [abs_nonneg (hV.cV ((Real.sqrt t)⁻¹ • u)),
                mul_nonneg ht_pos.le
                  (abs_nonneg (hV.cV ((Real.sqrt t)⁻¹ • u)))]
      -- Now apply indicator gain.
      have h_RHS_nn : 0 ≤ (A * B * ‖u‖ ^ 2 + |m|) *
          ((2 + Cc * ‖u‖ ^ 3) * Real.exp (-(α * ‖u‖ ^ 2))) :=
        mul_nonneg h_diff_nn
          (mul_nonneg h_2Cc_nn (Real.exp_pos _).le)
      have h_step_indicator : (A * B * ‖u‖ ^ 2 + |m|) *
          ((2 + Cc * ‖u‖ ^ 3) * Real.exp (-(α * ‖u‖ ^ 2)))
          ≤ ‖u‖ ^ 2 / (ρ ^ 2 * t) *
            ((A * B * ‖u‖ ^ 2 + |m|) * (2 + Cc * ‖u‖ ^ 3)) *
            Real.exp (-(α * ‖u‖ ^ 2)) := by
        calc (A * B * ‖u‖ ^ 2 + |m|) *
              ((2 + Cc * ‖u‖ ^ 3) * Real.exp (-(α * ‖u‖ ^ 2)))
            = (A * B * ‖u‖ ^ 2 + |m|) * (2 + Cc * ‖u‖ ^ 3) *
              Real.exp (-(α * ‖u‖ ^ 2)) := by ring
          _ = (A * B * ‖u‖ ^ 2 + |m|) * (2 + Cc * ‖u‖ ^ 3) *
              Real.exp (-(α * ‖u‖ ^ 2)) * 1 := (mul_one _).symm
          _ ≤ (A * B * ‖u‖ ^ 2 + |m|) * (2 + Cc * ‖u‖ ^ 3) *
              Real.exp (-(α * ‖u‖ ^ 2)) *
              (‖u‖ ^ 2 / (ρ ^ 2 * t)) := by
              have h_lhs_nn : 0 ≤ (A * B * ‖u‖ ^ 2 + |m|) *
                  (2 + Cc * ‖u‖ ^ 3) * Real.exp (-(α * ‖u‖ ^ 2)) :=
                mul_nonneg (mul_nonneg h_diff_nn h_2Cc_nn)
                  (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left h_indicator h_lhs_nn
          _ = ‖u‖ ^ 2 / (ρ ^ 2 * t) *
              ((A * B * ‖u‖ ^ 2 + |m|) * (2 + Cc * ‖u‖ ^ 3)) *
              Real.exp (-(α * ‖u‖ ^ 2)) := by ring
      have h_F_le_Gtail : |dot a u * dot b u - m| * gaussianWeight H u *
          |Real.exp (-(rescaledPerturbation V H t u)) - 1 +
            t * hV.cV ((Real.sqrt t)⁻¹ • u)|
          ≤ Gtail u := by
        rw [hGtail_def]
        exact le_trans h_F_bound h_step_indicator
      linarith [hGlocal_nn u]
  -- Integrability of the original integrand.
  have h_F_int : Integrable (fun u : ι → ℝ =>
      (dot a u * dot b u - dot a (Hinv b)) * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
         t * hV.cV ((Real.sqrt t)⁻¹ • u))) := by
    -- = B · gW · exp(-s_t) - B · gW + B · gW · c_t. All three integrable.
    have h_int_dd_exp : Integrable (fun u : ι → ℝ =>
        dot a u * dot b u * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) :=
      integrable_dot_mul_dot_mul_rescaled_weight V H a b
        hV.toPotentialApprox.V_continuous
        hV.toPotentialApprox.coercive_const_pos
        hV.toPotentialApprox.coercive_bound ht_pos
    have h_int_m_exp : Integrable (fun u : ι → ℝ =>
        m * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))) :=
      (integrable_rescaled_weight V hV.toPotentialApprox.V_continuous H
        hV.toPotentialApprox.coercive_const_pos
        hV.toPotentialApprox.coercive_bound ht_pos).const_mul m
    have h_int_F_exp : Integrable (fun u : ι → ℝ =>
        (dot a u * dot b u - m) * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) := by
      have h_sum := h_int_dd_exp.sub h_int_m_exp
      apply h_sum.congr
      filter_upwards with u
      simp only [Pi.sub_apply]; ring
    have h_int_BgW : Integrable (fun u : ι → ℝ =>
        (dot a u * dot b u - m) * gaussianWeight H u) := by
      have h_dd := integrable_dot_mul_dot_mul_gaussianWeight hGauss a b
      have h_m := hGauss.int_gW.const_mul m
      have h_sum := h_dd.sub h_m
      apply h_sum.congr
      filter_upwards with u
      simp only [Pi.sub_apply]; ring
    have h_int_Bct : Integrable (fun u : ι → ℝ =>
        (dot a u * dot b u - m) * gaussianWeight H u *
          (t * hV.cV ((Real.sqrt t)⁻¹ • u))) :=
      integrable_centered_bilinear_mul_gaussianWeight_mul_scaledCubic
        V H hV a b m ht_pos
    -- Combine: F = (B · gW · exp) - (B · gW) + (B · gW · c_t).
    have h_eq : (fun u : ι → ℝ => (dot a u * dot b u - m) *
          gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
            t * hV.cV ((Real.sqrt t)⁻¹ • u)))
        = fun u => ((dot a u * dot b u - m) * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)) -
            (dot a u * dot b u - m) * gaussianWeight H u) +
          ((dot a u * dot b u - m) * gaussianWeight H u *
            (t * hV.cV ((Real.sqrt t)⁻¹ • u))) := by
      funext u; ring
    rw [h_eq]
    exact (h_int_F_exp.sub h_int_BgW).add h_int_Bct
  -- Integrability of Glocal.
  have hGlocal_int : Integrable Glocal := by
    rw [hGlocal_def]
    have h4 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι)
      (by linarith : 0 < c' / 4) 4
    have h6 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι)
      (by linarith : 0 < c' / 4) 6
    have h8 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι)
      (by linarith : 0 < c' / 4) 8
    have h_sum : Integrable (fun u : ι → ℝ =>
        A * B * Cs ^ 2 * (‖u‖ ^ 8 * Real.exp (-((c' / 4) * ‖u‖ ^ 2))) +
        (A * B * jet_C + |m| * Cs ^ 2) *
          (‖u‖ ^ 6 * Real.exp (-((c' / 4) * ‖u‖ ^ 2))) +
        |m| * jet_C * (‖u‖ ^ 4 * Real.exp (-((c' / 4) * ‖u‖ ^ 2)))) :=
      ((h8.const_mul (A * B * Cs ^ 2)).add
        (h6.const_mul (A * B * jet_C + |m| * Cs ^ 2))).add
        (h4.const_mul (|m| * jet_C))
    have h_eq : (fun u : ι → ℝ =>
          (A * B * ‖u‖ ^ 2 + |m|) *
            ((Cs ^ 2 * ‖u‖ ^ 6 + jet_C * ‖u‖ ^ 4) / t) *
            Real.exp (-(c' / 4 * ‖u‖ ^ 2)))
        = fun u =>
          (A * B * Cs ^ 2 / t) *
            (‖u‖ ^ 8 * Real.exp (-(c' / 4 * ‖u‖ ^ 2))) +
          ((A * B * jet_C + |m| * Cs ^ 2) / t) *
            (‖u‖ ^ 6 * Real.exp (-(c' / 4 * ‖u‖ ^ 2))) +
          (|m| * jet_C / t) *
            (‖u‖ ^ 4 * Real.exp (-(c' / 4 * ‖u‖ ^ 2))) := by
      funext u
      have h_pow8 : ‖u‖ ^ 2 * ‖u‖ ^ 6 = ‖u‖ ^ 8 := by ring
      have h_pow6 : ‖u‖ ^ 2 * ‖u‖ ^ 4 = ‖u‖ ^ 6 := by ring
      field_simp
      ring
    rw [h_eq]
    have h4' := h4.const_mul (|m| * jet_C / t)
    have h6' := h6.const_mul ((A * B * jet_C + |m| * Cs ^ 2) / t)
    have h8' := h8.const_mul (A * B * Cs ^ 2 / t)
    exact (h8'.add h6').add h4'
  -- Integrability of Gtail.
  have hGtail_int : Integrable Gtail := by
    rw [hGtail_def]
    have h2 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hα_pos 2
    have h4 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hα_pos 4
    have h5 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hα_pos 5
    have h7 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hα_pos 7
    have h_sum : Integrable (fun u : ι → ℝ =>
        (2 * A * B / (ρ ^ 2 * t)) *
          (‖u‖ ^ 4 * Real.exp (-(α * ‖u‖ ^ 2))) +
        (2 * |m| / (ρ ^ 2 * t)) *
          (‖u‖ ^ 2 * Real.exp (-(α * ‖u‖ ^ 2))) +
        (A * B * Cc / (ρ ^ 2 * t)) *
          (‖u‖ ^ 7 * Real.exp (-(α * ‖u‖ ^ 2))) +
        (|m| * Cc / (ρ ^ 2 * t)) *
          (‖u‖ ^ 5 * Real.exp (-(α * ‖u‖ ^ 2)))) :=
      (((h4.const_mul (2 * A * B / (ρ ^ 2 * t))).add
        (h2.const_mul (2 * |m| / (ρ ^ 2 * t)))).add
        (h7.const_mul (A * B * Cc / (ρ ^ 2 * t)))).add
        (h5.const_mul (|m| * Cc / (ρ ^ 2 * t)))
    have h_eq : (fun u : ι → ℝ =>
          ‖u‖ ^ 2 / (ρ ^ 2 * t) *
            ((A * B * ‖u‖ ^ 2 + |m|) * (2 + Cc * ‖u‖ ^ 3)) *
            Real.exp (-(α * ‖u‖ ^ 2)))
        = fun u =>
          (2 * A * B / (ρ ^ 2 * t)) *
            (‖u‖ ^ 4 * Real.exp (-(α * ‖u‖ ^ 2))) +
          (2 * |m| / (ρ ^ 2 * t)) *
            (‖u‖ ^ 2 * Real.exp (-(α * ‖u‖ ^ 2))) +
          (A * B * Cc / (ρ ^ 2 * t)) *
            (‖u‖ ^ 7 * Real.exp (-(α * ‖u‖ ^ 2))) +
          (|m| * Cc / (ρ ^ 2 * t)) *
            (‖u‖ ^ 5 * Real.exp (-(α * ‖u‖ ^ 2))) := by
      funext u
      have h7eq : ‖u‖ ^ 2 * ‖u‖ ^ 5 = ‖u‖ ^ 7 := by ring
      have h5eq : ‖u‖ ^ 2 * ‖u‖ ^ 3 = ‖u‖ ^ 5 := by ring
      have h4eq : ‖u‖ ^ 2 * ‖u‖ ^ 2 = ‖u‖ ^ 4 := by ring
      field_simp
      ring
    rw [h_eq]
    exact h_sum
  -- Integrate Glocal: ∫ Glocal = K_loc / t. Deferred — multi-step
  -- integral_add + integral_const_mul composition, ~50 LOC.
  have hGlocal_eq : ∫ u, Glocal u =
      (A * B * Cs ^ 2 * M_loc_8 +
       (A * B * jet_C + |m| * Cs ^ 2) * M_loc_6 +
       |m| * jet_C * M_loc_4) / t := by
    sorry
  -- Integrate Gtail: ∫ Gtail = K_tail / t. Deferred.
  have hGtail_eq : ∫ u, Gtail u =
      (1 / ρ ^ 2) *
        (2 * A * B * M_tail_4 + 2 * |m| * M_tail_2 +
         A * B * Cc * M_tail_7 + |m| * Cc * M_tail_5) / t := by
    sorry
  -- Combine.
  calc |∫ u : ι → ℝ, (dot a u * dot b u - dot a (Hinv b)) *
            gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
             t * hV.cV ((Real.sqrt t)⁻¹ • u))|
      ≤ ∫ u : ι → ℝ, |(dot a u * dot b u - dot a (Hinv b)) *
            gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
             t * hV.cV ((Real.sqrt t)⁻¹ • u))| := by
            rw [show |∫ u, _| = ‖∫ u, _‖ from (Real.norm_eq_abs _).symm]
            exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u, (Glocal u + Gtail u) := by
        apply MeasureTheory.integral_mono_ae h_F_int.norm
          (hGlocal_int.add hGtail_int)
        filter_upwards with u
        rw [Real.norm_eq_abs]
        exact hpt u
    _ = (∫ u, Glocal u) + ∫ u, Gtail u :=
        MeasureTheory.integral_add hGlocal_int hGtail_int
    _ = (A * B * Cs ^ 2 * M_loc_8 +
         (A * B * jet_C + |m| * Cs ^ 2) * M_loc_6 +
         |m| * jet_C * M_loc_4) / t +
        (1 / ρ ^ 2) *
          (2 * A * B * M_tail_4 + 2 * |m| * M_tail_2 +
           A * B * Cc * M_tail_7 + |m| * Cc * M_tail_5) / t := by
        rw [hGlocal_eq, hGtail_eq]
    _ = (K_loc + K_tail) / t := by
        rw [hK_loc_def, hK_tail_def]
        field_simp

/-- **Sharp helper 1 (centered bilinear correction)**: the centered
bilinear factor `(dot a u · dot b u - m)` against `gW · exp(-s_t)`
integrates to `O(1/t)`, where `m := dot a (Hinv b)`.

This is the parity-resolved upgrade of the weak `O(1/√t)` bound. The
strategy:
- the original integral equals the *corrected-bracket* integral
  `∫ B · gW · (exp(-s_t) - 1 + c_t)` via
  `integral_centered_bilinear_eq_corrected_bracket`;
- the corrected bracket is `O(1/t)` on the local ball (Stage 1's Taylor
  remainder + Stage 2's quartic remainder) and `O(1/t)` on the tail
  (indicator trick `1_{‖u‖ ≥ ρ√t} ≤ ‖u‖²/(ρ²·t)`);
- combining gives the K/t bound. -/
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
  obtain ⟨K, T₀, hT₀, h_bound⟩ :=
    abs_integral_corrected_bracket_centered_bilinear_le V H Hinv a b hV hGauss
  refine ⟨K, T₀, hT₀, ?_⟩
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans hT₀ ht)
  rw [integral_centered_bilinear_eq_corrected_bracket V H Hinv a b hV hGauss
        ht_pos]
  exact h_bound t ht

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
  -- Constants.
  set c := hV.toPotentialApprox.coercive_const with hc_def
  have hc_pos : 0 < c := hV.toPotentialApprox.coercive_const_pos
  have h_coer := hV.toPotentialApprox.coercive_bound
  set Cs := hV.toPotentialApprox.local_const with hCs_def
  set R_pot := hV.toPotentialApprox.local_radius with hR_pot_def
  have hCs_nn : 0 ≤ Cs := hV.toPotentialApprox.local_const_nonneg
  have hR_pot_pos : 0 < R_pot := hV.toPotentialApprox.local_radius_pos
  have h_V_local := hV.toPotentialApprox.local_bound
  set Cq := hφ.qφ_bound_const with hCq_def
  have hCq_nn : 0 ≤ Cq := hφ.qφ_bound_const_nonneg
  have h_qψ_bound := hφ.qφ_bound
  set jet_R := hφ.jet_radius with hjet_R_def
  set jet_C := hφ.jet_const with hjet_C_def
  have hjet_R_pos : 0 < jet_R := hφ.jet_radius_pos
  have hjet_C_nn : 0 ≤ jet_C := hφ.jet_const_nonneg
  have h_jet_bound := hφ.jet_bound
  obtain ⟨Kφ, p, hKφ_nn, hpoly_φ⟩ := hφ.toObservableApprox.poly_growth
  set DC : ℝ := ∑ i, |dotCoef i| with hDC_def
  set PG : ℝ := ∑ i, |phiGrad i| with hPG_def
  have hDC_nn : 0 ≤ DC := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hPG_nn : 0 ≤ PG := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set Cφ' : ℝ := 2 * Kφ + 2 * PG with hCφ'_def
  have hCφ'_nn : 0 ≤ Cφ' := by rw [hCφ'_def]; linarith
  -- Choose δ ≤ min(R_pot, jet_R, c/(4·(Cs+1))).
  have hCs1_pos : (0 : ℝ) < Cs + 1 := by linarith
  set δ : ℝ := min (min R_pot jet_R) (c / (4 * (Cs + 1))) with hδ_def
  have hδ_pos : 0 < δ :=
    lt_min (lt_min hR_pot_pos hjet_R_pos) (by positivity)
  have hδ_le_R_pot : δ ≤ R_pot := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_le_jet_R : δ ≤ jet_R :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ_const : Cs * δ ≤ c / 4 := by
    have h_le : δ ≤ c / (4 * (Cs + 1)) := min_le_right _ _
    calc Cs * δ ≤ Cs * (c / (4 * (Cs + 1))) :=
          mul_le_mul_of_nonneg_left h_le hCs_nn
      _ = (Cs / (Cs + 1)) * (c / 4) := by field_simp
      _ ≤ 1 * (c / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ c/4)
          rw [div_le_one hCs1_pos]; linarith
      _ = c / 4 := one_mul _
  -- Tail decay constant.
  set β : ℝ := c * δ ^ 2 / 4 with hβ_def
  have hβ_pos : 0 < β := by rw [hβ_def]; positivity
  -- Polynomial degree for r₃ tail.
  set N_r : ℕ := p + 2 with hN_r_def
  -- Gaussian moments.
  set M_loc_q : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 6 *
    Real.exp (-((c / 4) * ‖u‖ ^ 2)) with hM_loc_q_def
  set M_tail_q : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 3 *
    Real.exp (-((c / 4) * ‖u‖ ^ 2)) with hM_tail_q_def
  set M_loc_r : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 4 *
    Real.exp (-(c * ‖u‖ ^ 2)) with hM_loc_r_def
  set M_tail_r : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) *
    Real.exp (-(c * ‖u‖ ^ 2)) with hM_tail_r_def
  have hM_loc_q_nn : 0 ≤ M_loc_q := by
    rw [hM_loc_q_def]
    apply MeasureTheory.integral_nonneg
    intro u
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_tail_q_nn : 0 ≤ M_tail_q := by
    rw [hM_tail_q_def]
    apply MeasureTheory.integral_nonneg
    intro u
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_loc_r_nn : 0 ≤ M_loc_r := by
    rw [hM_loc_r_def]
    apply MeasureTheory.integral_nonneg
    intro u
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_tail_r_nn : 0 ≤ M_tail_r := by
    rw [hM_tail_r_def]
    apply MeasureTheory.integral_nonneg
    intro u
    have h1 : 0 ≤ ‖u‖ ^ 4 := pow_nonneg (norm_nonneg _) _
    have h2 : 0 ≤ 1 + ‖u‖ ^ N_r := by positivity
    exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
  -- K and T₀.
  set K : ℝ :=
    DC * Cq * Cs * M_loc_q +
    2 * DC * Cq * M_tail_q +
    DC * jet_C * M_loc_r +
    DC * (2 * Cφ' + Cq) / δ ^ 3 * M_tail_r with hK_def
  refine ⟨K, max 1 (1 / β ^ 2), le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := le_of_max_le_left ht
  have htβ : 1 / β ^ 2 ≤ t := le_of_max_le_right ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have ht_sqrt_pos : 0 < t * Real.sqrt t := mul_pos ht_pos hsqrt_pos
  have h_tail_decay : Real.exp (-(β * t)) ≤ 1 / Real.sqrt t :=
    exp_neg_const_mul_le_inv_sqrt hβ_pos htβ
  -- Define the four majorant pieces (global functions).
  set Glocal_q : (ι → ℝ) → ℝ := fun u =>
    DC * Cq * Cs / (t * Real.sqrt t) * ‖u‖ ^ 6 *
      Real.exp (-((c / 4) * ‖u‖ ^ 2)) with hGlocal_q_def
  set Gtail_q : (ι → ℝ) → ℝ := fun u =>
    2 * DC * Cq / (t * Real.sqrt t) * ‖u‖ ^ 3 *
      Real.exp (-((c / 4) * ‖u‖ ^ 2)) with hGtail_q_def
  set Glocal_r : (ι → ℝ) → ℝ := fun u =>
    DC * jet_C / (t * Real.sqrt t) * ‖u‖ ^ 4 *
      Real.exp (-(c * ‖u‖ ^ 2)) with hGlocal_r_def
  set Gtail_r : (ι → ℝ) → ℝ := fun u =>
    DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
      ‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) *
      Real.exp (-(c * ‖u‖ ^ 2)) with hGtail_r_def
  -- All majorants are nonneg.
  have hGlocal_q_nn : ∀ u, 0 ≤ Glocal_q u := by
    intro u
    rw [hGlocal_q_def]
    have h1 : 0 ≤ DC * Cq * Cs / (t * Real.sqrt t) :=
      div_nonneg (mul_nonneg (mul_nonneg hDC_nn hCq_nn) hCs_nn)
        ht_sqrt_pos.le
    have h2 : 0 ≤ ‖u‖ ^ 6 := pow_nonneg (norm_nonneg _) _
    exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
  have hGtail_q_nn : ∀ u, 0 ≤ Gtail_q u := by
    intro u
    rw [hGtail_q_def]
    have h1 : 0 ≤ 2 * DC * Cq / (t * Real.sqrt t) :=
      div_nonneg (by positivity) ht_sqrt_pos.le
    have h2 : 0 ≤ ‖u‖ ^ 3 := pow_nonneg (norm_nonneg _) _
    exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
  have hGlocal_r_nn : ∀ u, 0 ≤ Glocal_r u := by
    intro u
    rw [hGlocal_r_def]
    have h1 : 0 ≤ DC * jet_C / (t * Real.sqrt t) :=
      div_nonneg (mul_nonneg hDC_nn hjet_C_nn) ht_sqrt_pos.le
    have h2 : 0 ≤ ‖u‖ ^ 4 := pow_nonneg (norm_nonneg _) _
    exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
  have hGtail_r_nn : ∀ u, 0 ≤ Gtail_r u := by
    intro u
    rw [hGtail_r_def]
    have h1 : 0 ≤ DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) := by
      apply div_nonneg (mul_nonneg hDC_nn (by linarith))
      exact mul_nonneg (pow_nonneg hδ_pos.le 3) ht_sqrt_pos.le
    have h2 : 0 ≤ DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
        ‖u‖ ^ 4 := mul_nonneg h1 (pow_nonneg (norm_nonneg _) _)
    have h3 : 0 ≤ DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
        ‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) :=
      mul_nonneg h2 (by positivity)
    exact mul_nonneg h3 (Real.exp_pos _).le
  -- Integrability of the original integrand and its qψ/r₃ split pieces.
  have h_int_F : Integrable (fun u : ι → ℝ =>
      dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_dot_mul_remainder_mul_rescaled_weight V φ H Hinv dotCoef phiGrad
      hV.toPotentialApprox hφ.toObservableApprox hGauss ht1
  have h_int_F_q : Integrable (fun u : ι → ℝ =>
      dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_dot_mul_quadJet_mul_rescaled_weight V H hc_pos h_coer
      hV.toPotentialApprox.V_continuous hφ.qφ hφ.qφ_continuous hCq_nn
      h_qψ_bound dotCoef ht_pos
  have h_int_F_r : Integrable (fun u : ι → ℝ =>
      dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
          hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
    have h_diff := h_int_F.sub h_int_F_q
    apply h_diff.congr
    filter_upwards with u
    simp only [Pi.sub_apply]
    ring
  -- Pointwise: F(u) = F_q(u) + F_r(u).
  have h_F_split : ∀ u : ι → ℝ,
      dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
      = (dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
        + (dot dotCoef u *
          (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
            hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) := by
    intro u; ring
  -- ∫ F = ∫ F_q + ∫ F_r.
  have h_int_F_eq : ∫ u : ι → ℝ,
      dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
    = (∫ u : ι → ℝ, dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
      + (∫ u : ι → ℝ, dot dotCoef u *
          (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
            hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) := by
    rw [show (fun u : ι → ℝ => dot dotCoef u *
              (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
            = fun u =>
              (dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
                gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))
              + (dot dotCoef u *
                (φ ((Real.sqrt t)⁻¹ • u) -
                  (Real.sqrt t)⁻¹ * dot phiGrad u -
                  hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
                gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u))) from funext h_F_split]
    exact MeasureTheory.integral_add h_int_F_q h_int_F_r
  -- Parity rewriting of ∫ F_q.
  -- ∫ F_q = ∫ dot c · qψ · gW · (exp(-s_t) - 1) via integral_sub + parity.
  have h_int_qψ_gW : Integrable (fun u : ι → ℝ =>
      dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u) :=
    integrable_dot_mul_quadJet_mul_gaussianWeight V H hV hφ.qφ
      hφ.qφ_continuous hCq_nn h_qψ_bound dotCoef ht_pos
  have h_parity : ∫ u : ι → ℝ, dot dotCoef u *
      hφ.qφ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u = 0 :=
    integral_dot_mul_quadJet_eq_zero H hφ.qφ hφ.qφ_even dotCoef t
  have h_F_q_parity : ∫ u : ι → ℝ,
        dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
      = ∫ u : ι → ℝ, dot dotCoef u *
          hφ.qφ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1) := by
    have h_pt : ∀ u : ι → ℝ,
        dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
        = dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
            gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1) +
          dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
            gaussianWeight H u := by intro u; ring
    have h_int_diff : Integrable (fun u : ι → ℝ =>
        dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
          gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)) := by
      have h_sum := h_int_F_q.sub h_int_qψ_gW
      apply h_sum.congr
      filter_upwards with u
      simp only [Pi.sub_apply]
      ring
    rw [show (fun u : ι → ℝ => dot dotCoef u *
              hφ.qφ ((Real.sqrt t)⁻¹ • u) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
            = fun u => (dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
                gaussianWeight H u *
                (Real.exp (-(rescaledPerturbation V H t u)) - 1)) +
              (dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
                gaussianWeight H u) from funext h_pt]
    rw [MeasureTheory.integral_add h_int_diff h_int_qψ_gW]
    rw [h_parity, add_zero]
  -- Pointwise bound on |F_q(u)| via Glocal_q + Gtail_q.
  have hpt_q : ∀ u : ι → ℝ,
      |dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ Glocal_q u + Gtail_q u := by
    intro u
    by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
    · -- Local case.
      have h_local := abs_dot_mul_quadJet_mul_gaussianWeight_mul_exp_sub_one_local_le
        V φ H hc_pos hR_pot_pos hCs_nn hCq_nn h_coer h_V_local hφ.qφ
        h_qψ_bound dotCoef hδ_pos hδ_le_R_pot hδ_const ht_pos u hu
      have h_eq : DC * Cq * Cs / (t * Real.sqrt t) * ‖u‖ ^ 6 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) = Glocal_q u := by rw [hGlocal_q_def]
      have h_bound : DC * Cq * Cs / (t * Real.sqrt t) * ‖u‖ ^ 6 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) =
          (DC * Cq * Cs / (t * Real.sqrt t)) * ‖u‖ ^ 6 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := rfl
      have h_local' : |dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
          gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
          ≤ Glocal_q u := by
        rw [← h_eq]
        rw [show DC * Cq * Cs / (t * Real.sqrt t) * ‖u‖ ^ 6 *
              Real.exp (-((c / 4) * ‖u‖ ^ 2))
            = DC * Cq * Cs / (t * Real.sqrt t) * ‖u‖ ^ 6 *
              Real.exp (-((c / 4) * ‖u‖ ^ 2)) from rfl]
        have h_simp : ((∑ i, |dotCoef i|) * Cq * Cs / (t * Real.sqrt t)) *
            ‖u‖ ^ 6 * Real.exp (-((c / 4) * ‖u‖ ^ 2))
            = DC * Cq * Cs / (t * Real.sqrt t) * ‖u‖ ^ 6 *
              Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
          rw [hDC_def]
        rw [← h_simp]
        exact h_local
      linarith [hGtail_q_nn u]
    · -- Tail case.
      push_neg at hu
      have h_tail := abs_dot_mul_quadJet_mul_gaussianWeight_mul_exp_sub_one_tail_le
        V H hc_pos hR_pot_pos hCs_nn hCq_nn h_coer h_V_local hφ.qφ
        h_qψ_bound dotCoef hδ_pos ht_pos u hu
      -- h_tail : ... ≤ (2 · DC · Cq / t) · ‖u‖³ · exp(-(c/4)·‖u‖²) · exp(-β·t)
      have h_step : (2 * DC * Cq / t) * ‖u‖ ^ 3 *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
          Real.exp (-((c * δ ^ 2 / 4) * t))
          ≤ Gtail_q u := by
        rw [hGtail_q_def]
        have h_decay : Real.exp (-(β * t)) ≤ 1 / Real.sqrt t := h_tail_decay
        have h_β_eq : c * δ ^ 2 / 4 = β := by rw [hβ_def]
        rw [h_β_eq]
        have h_lhs_nn : 0 ≤ (2 * DC * Cq / t) * ‖u‖ ^ 3 *
            Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
          have h1 : 0 ≤ 2 * DC * Cq / t :=
            div_nonneg (by positivity) ht_pos.le
          have h2 : 0 ≤ ‖u‖ ^ 3 := pow_nonneg (norm_nonneg _) _
          exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
        have h_decay_step : (2 * DC * Cq / t) * ‖u‖ ^ 3 *
            Real.exp (-((c / 4) * ‖u‖ ^ 2)) * Real.exp (-(β * t))
            ≤ (2 * DC * Cq / t) * ‖u‖ ^ 3 *
            Real.exp (-((c / 4) * ‖u‖ ^ 2)) * (1 / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left h_decay h_lhs_nn
        calc (2 * DC * Cq / t) * ‖u‖ ^ 3 *
              Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
              Real.exp (-(β * t))
            ≤ (2 * DC * Cq / t) * ‖u‖ ^ 3 *
              Real.exp (-((c / 4) * ‖u‖ ^ 2)) * (1 / Real.sqrt t) :=
            h_decay_step
          _ = 2 * DC * Cq / (t * Real.sqrt t) * ‖u‖ ^ 3 *
              Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
            field_simp
      have h_simp_lhs : (∑ i, |dotCoef i|) = DC := hDC_def.symm
      rw [h_simp_lhs] at h_tail
      have h_F_q_le_Gtail : |dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
          gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
          ≤ Gtail_q u := le_trans h_tail h_step
      linarith [hGlocal_q_nn u]
  -- Pointwise bound on |F_r(u)| via Glocal_r + Gtail_r.
  have hpt_r : ∀ u : ι → ℝ,
      |dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
          hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))|
      ≤ Glocal_r u + Gtail_r u := by
    intro u
    by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
    · -- Local case.
      have hu_jet : ‖u‖ ≤ jet_R * Real.sqrt t :=
        le_trans hu (mul_le_mul_of_nonneg_right hδ_le_jet_R hsqrt_pos.le)
      have h_local := abs_dot_mul_cubic_remainder_mul_rescaled_weight_local_le
        V φ H hc_pos hjet_C_nn h_coer hφ.qφ phiGrad h_jet_bound dotCoef
        ht_pos u hu_jet
      -- h_local : |F_r(u)| ≤ (DC·jet_C/(t·√t))·‖u‖^4·exp(-c·‖u‖²)
      have h_simp : (∑ i, |dotCoef i|) = DC := hDC_def.symm
      rw [h_simp] at h_local
      have h_eq : DC * jet_C / (t * Real.sqrt t) * ‖u‖ ^ 4 *
          Real.exp (-(c * ‖u‖ ^ 2)) = Glocal_r u := by rw [hGlocal_r_def]
      rw [h_eq] at h_local
      linarith [hGtail_r_nn u]
    · -- Tail case.
      push_neg at hu
      have h_tail := abs_dot_mul_cubic_remainder_mul_rescaled_weight_tail_le
        V φ H hc_pos h_coer hKφ_nn hpoly_φ hφ.qφ hCq_nn h_qψ_bound
        dotCoef phiGrad hδ_pos ht1 u hu
      -- h_tail : |F_r(u)| ≤ (DC·(2·Cφ' + Cq)/(δ³·t·√t))·‖u‖^4·(1+‖u‖^(p+2))·exp(-c·‖u‖²)
      have h_simp_DC : (∑ i, |dotCoef i|) = DC := hDC_def.symm
      have h_simp_Cφ' : 2 * Kφ + 2 * (∑ i, |phiGrad i|) = Cφ' := by
        rw [hCφ'_def, hPG_def]
      have h_simp_N : p + 2 = N_r := hN_r_def.symm
      rw [h_simp_DC, h_simp_Cφ', h_simp_N] at h_tail
      have h_eq : DC * (2 * Cφ' + Cq) /
          (δ ^ 3 * (t * Real.sqrt t)) * ‖u‖ ^ 4 *
          (1 + ‖u‖ ^ N_r) * Real.exp (-(c * ‖u‖ ^ 2)) = Gtail_r u := by
        rw [hGtail_r_def]
      rw [h_eq] at h_tail
      linarith [hGlocal_r_nn u]
  -- Integrability of the four majorants.
  have hGlocal_q_int : Integrable Glocal_q := by
    rw [hGlocal_q_def]
    have h := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι)
      (by linarith : 0 < c / 4) 6
    have h_eq : (fun u : ι → ℝ =>
          DC * Cq * Cs / (t * Real.sqrt t) * ‖u‖ ^ 6 *
            Real.exp (-((c / 4) * ‖u‖ ^ 2)))
        = fun u => (DC * Cq * Cs / (t * Real.sqrt t)) *
            (‖u‖ ^ 6 * Real.exp (-((c / 4) * ‖u‖ ^ 2))) := by
      funext u; ring
    rw [h_eq]
    exact h.const_mul _
  have hGtail_q_int : Integrable Gtail_q := by
    rw [hGtail_q_def]
    have h := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι)
      (by linarith : 0 < c / 4) 3
    have h_eq : (fun u : ι → ℝ =>
          2 * DC * Cq / (t * Real.sqrt t) * ‖u‖ ^ 3 *
            Real.exp (-((c / 4) * ‖u‖ ^ 2)))
        = fun u => (2 * DC * Cq / (t * Real.sqrt t)) *
            (‖u‖ ^ 3 * Real.exp (-((c / 4) * ‖u‖ ^ 2))) := by
      funext u; ring
    rw [h_eq]
    exact h.const_mul _
  have hGlocal_r_int : Integrable Glocal_r := by
    rw [hGlocal_r_def]
    have h := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 4
    have h_eq : (fun u : ι → ℝ =>
          DC * jet_C / (t * Real.sqrt t) * ‖u‖ ^ 4 *
            Real.exp (-(c * ‖u‖ ^ 2)))
        = fun u => (DC * jet_C / (t * Real.sqrt t)) *
            (‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2))) := by
      funext u; ring
    rw [h_eq]
    exact h.const_mul _
  have hGtail_r_int : Integrable Gtail_r := by
    rw [hGtail_r_def]
    have h_a := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 4
    have h_b := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos
      (4 + N_r)
    have h_sum : Integrable (fun u : ι → ℝ =>
        ‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2)) +
        ‖u‖ ^ (4 + N_r) * Real.exp (-(c * ‖u‖ ^ 2))) := h_a.add h_b
    have h_eq : (fun u : ι → ℝ =>
          DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
            ‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) *
            Real.exp (-(c * ‖u‖ ^ 2)))
        = fun u => (DC * (2 * Cφ' + Cq) /
            (δ ^ 3 * (t * Real.sqrt t))) *
            (‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2)) +
             ‖u‖ ^ (4 + N_r) * Real.exp (-(c * ‖u‖ ^ 2))) := by
      funext u
      have h_pow_eq : ‖u‖ ^ 4 * ‖u‖ ^ N_r = ‖u‖ ^ (4 + N_r) := by
        rw [← pow_add]
      have h1 : ‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) =
          ‖u‖ ^ 4 + ‖u‖ ^ (4 + N_r) := by
        rw [show ‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) =
              ‖u‖ ^ 4 + ‖u‖ ^ 4 * ‖u‖ ^ N_r from by ring]
        rw [h_pow_eq]
      calc DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
              ‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) * Real.exp (-(c * ‖u‖ ^ 2))
          = DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
              (‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r)) *
              Real.exp (-(c * ‖u‖ ^ 2)) := by ring
        _ = DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
              (‖u‖ ^ 4 + ‖u‖ ^ (4 + N_r)) *
              Real.exp (-(c * ‖u‖ ^ 2)) := by rw [h1]
        _ = DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
              (‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2)) +
               ‖u‖ ^ (4 + N_r) * Real.exp (-(c * ‖u‖ ^ 2))) := by ring
    rw [h_eq]
    exact h_sum.const_mul _
  -- ∫ Glocal_q = (DC·Cq·Cs/(t·√t)) · M_loc_q.
  have hGlocal_q_eq : ∫ u, Glocal_q u =
      DC * Cq * Cs / (t * Real.sqrt t) * M_loc_q := by
    rw [hGlocal_q_def, hM_loc_q_def]
    rw [show (fun u : ι → ℝ =>
              DC * Cq * Cs / (t * Real.sqrt t) * ‖u‖ ^ 6 *
                Real.exp (-((c / 4) * ‖u‖ ^ 2)))
            = fun u => (DC * Cq * Cs / (t * Real.sqrt t)) *
                (‖u‖ ^ 6 * Real.exp (-((c / 4) * ‖u‖ ^ 2))) from by
        funext u; ring]
    rw [MeasureTheory.integral_const_mul]
  have hGtail_q_eq : ∫ u, Gtail_q u =
      2 * DC * Cq / (t * Real.sqrt t) * M_tail_q := by
    rw [hGtail_q_def, hM_tail_q_def]
    rw [show (fun u : ι → ℝ =>
              2 * DC * Cq / (t * Real.sqrt t) * ‖u‖ ^ 3 *
                Real.exp (-((c / 4) * ‖u‖ ^ 2)))
            = fun u => (2 * DC * Cq / (t * Real.sqrt t)) *
                (‖u‖ ^ 3 * Real.exp (-((c / 4) * ‖u‖ ^ 2))) from by
        funext u; ring]
    rw [MeasureTheory.integral_const_mul]
  have hGlocal_r_eq : ∫ u, Glocal_r u =
      DC * jet_C / (t * Real.sqrt t) * M_loc_r := by
    rw [hGlocal_r_def, hM_loc_r_def]
    rw [show (fun u : ι → ℝ =>
              DC * jet_C / (t * Real.sqrt t) * ‖u‖ ^ 4 *
                Real.exp (-(c * ‖u‖ ^ 2)))
            = fun u => (DC * jet_C / (t * Real.sqrt t)) *
                (‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2))) from by
        funext u; ring]
    rw [MeasureTheory.integral_const_mul]
  have hGtail_r_eq : ∫ u, Gtail_r u =
      DC * (2 * Cφ' + Cq) / δ ^ 3 / (t * Real.sqrt t) * M_tail_r := by
    rw [hGtail_r_def, hM_tail_r_def]
    rw [show (fun u : ι → ℝ =>
              DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) *
                ‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) *
                Real.exp (-(c * ‖u‖ ^ 2)))
            = fun u => (DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t))) *
                (‖u‖ ^ 4 * (1 + ‖u‖ ^ N_r) *
                  Real.exp (-(c * ‖u‖ ^ 2))) from by
        funext u; ring]
    rw [MeasureTheory.integral_const_mul]
    have hδ3_ne : δ ^ 3 ≠ 0 := pow_ne_zero 3 hδ_pos.ne'
    have ht_sqrt_ne : t * Real.sqrt t ≠ 0 := ht_sqrt_pos.ne'
    rw [show DC * (2 * Cφ' + Cq) / δ ^ 3 / (t * Real.sqrt t) =
          DC * (2 * Cφ' + Cq) / (δ ^ 3 * (t * Real.sqrt t)) from by
        field_simp]
  -- Combine via triangle.
  have h_int_F_q_abs : Integrable (fun u : ι → ℝ =>
      dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)) := by
    have h_sum := h_int_F_q.sub h_int_qψ_gW
    apply h_sum.congr
    filter_upwards with u
    simp only [Pi.sub_apply]
    ring
  -- |∫ F_q| ≤ ∫ |F_q (parity-rewritten)| ≤ ∫ Glocal_q + ∫ Gtail_q.
  have h_F_q_bound : |∫ u : ι → ℝ,
      dot dotCoef u * hφ.qφ ((Real.sqrt t)⁻¹ • u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))|
      ≤ DC * Cq * Cs / (t * Real.sqrt t) * M_loc_q +
        2 * DC * Cq / (t * Real.sqrt t) * M_tail_q := by
    rw [h_F_q_parity]
    calc |∫ u : ι → ℝ, dot dotCoef u *
              hφ.qφ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
        ≤ ∫ u : ι → ℝ, |dot dotCoef u *
            hφ.qφ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1)| := by
          rw [show |∫ u, _| = ‖∫ u, _‖ from (Real.norm_eq_abs _).symm]
          exact MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ u, (Glocal_q u + Gtail_q u) := by
          apply MeasureTheory.integral_mono_ae h_int_F_q_abs.norm
            (hGlocal_q_int.add hGtail_q_int)
          filter_upwards with u
          rw [Real.norm_eq_abs]
          exact hpt_q u
      _ = (∫ u, Glocal_q u) + ∫ u, Gtail_q u :=
          MeasureTheory.integral_add hGlocal_q_int hGtail_q_int
      _ = DC * Cq * Cs / (t * Real.sqrt t) * M_loc_q +
          2 * DC * Cq / (t * Real.sqrt t) * M_tail_q := by
          rw [hGlocal_q_eq, hGtail_q_eq]
  -- |∫ F_r| ≤ ∫ |F_r| ≤ ∫ Glocal_r + ∫ Gtail_r.
  have h_F_r_bound : |∫ u : ι → ℝ,
      dot dotCoef u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
          hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))|
      ≤ DC * jet_C / (t * Real.sqrt t) * M_loc_r +
        DC * (2 * Cφ' + Cq) / δ ^ 3 / (t * Real.sqrt t) * M_tail_r := by
    calc |∫ u : ι → ℝ, dot dotCoef u *
              (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
                hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))|
        ≤ ∫ u : ι → ℝ, |dot dotCoef u *
            (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
              hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))| := by
          rw [show |∫ u, _| = ‖∫ u, _‖ from (Real.norm_eq_abs _).symm]
          exact MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ u, (Glocal_r u + Gtail_r u) := by
          apply MeasureTheory.integral_mono_ae h_int_F_r.norm
            (hGlocal_r_int.add hGtail_r_int)
          filter_upwards with u
          rw [Real.norm_eq_abs]
          exact hpt_r u
      _ = (∫ u, Glocal_r u) + ∫ u, Gtail_r u :=
          MeasureTheory.integral_add hGlocal_r_int hGtail_r_int
      _ = DC * jet_C / (t * Real.sqrt t) * M_loc_r +
          DC * (2 * Cφ' + Cq) / δ ^ 3 / (t * Real.sqrt t) * M_tail_r := by
          rw [hGlocal_r_eq, hGtail_r_eq]
  -- Combine.
  rw [h_int_F_eq]
  calc |(∫ u : ι → ℝ, dot dotCoef u *
              hφ.qφ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) +
            ∫ u : ι → ℝ, dot dotCoef u *
              (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
                hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))|
      ≤ |(∫ u : ι → ℝ, dot dotCoef u *
              hφ.qφ ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))| +
          |∫ u : ι → ℝ, dot dotCoef u *
              (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot phiGrad u -
                hφ.qφ ((Real.sqrt t)⁻¹ • u)) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))| := abs_add_le _ _
    _ ≤ (DC * Cq * Cs / (t * Real.sqrt t) * M_loc_q +
          2 * DC * Cq / (t * Real.sqrt t) * M_tail_q) +
        (DC * jet_C / (t * Real.sqrt t) * M_loc_r +
          DC * (2 * Cφ' + Cq) / δ ^ 3 / (t * Real.sqrt t) * M_tail_r) := by
        linarith
    _ = K / (t * Real.sqrt t) := by
        rw [hK_def]
        field_simp
        ring

/-- **Sharp helper 4 (quadratic remainder)**: the product of two
observable remainders integrated against `gW · exp(-s_t)` is `O(1/t²)`.

The bound uses the Glocal+Gtail template from the weak helpers, with two
upgrades:
* the local bound `|remφ · remψ| ≤ Cφ·Cψ·‖u‖⁴/t²` already gives `K/t²`
  on the local ball (from the weak quadratic Taylor bound, no parity
  needed);
* the tail uses the indicator trick `1_{‖u‖>R√t} ≤ ‖u‖⁴/(R⁴·t²)`
  (k = 4) to gain `1/t²` over the global polynomial bound.

This is essentially the weak helper 4 with `k = 3` indicator replaced by
`k = 4`. The two key local pointwise bounds
(`abs_remainder_mul_remainder_local_le` and
`abs_remainder_mul_remainder_mul_rescaled_weight_local_le`) are
formalized above; the remaining ~250-300 LOC Gtail+integration
bookkeeping is deferred. -/
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
  -- Constants from hypotheses.
  set c := hV.toPotentialApprox.coercive_const with hc_def
  have hc_pos : 0 < c := hV.toPotentialApprox.coercive_const_pos
  have h_coer := hV.toPotentialApprox.coercive_bound
  set Cφ := hφ.toObservableApprox.local_const with hCφ_def
  set Cψ := hψ.toObservableApprox.local_const with hCψ_def
  set Rφ := hφ.toObservableApprox.local_radius with hRφ_def
  set Rψ := hψ.toObservableApprox.local_radius with hRψ_def
  have hCφ_nn : 0 ≤ Cφ := hφ.toObservableApprox.local_const_nonneg
  have hCψ_nn : 0 ≤ Cψ := hψ.toObservableApprox.local_const_nonneg
  have hRφ_pos : 0 < Rφ := hφ.toObservableApprox.local_radius_pos
  have hRψ_pos : 0 < Rψ := hψ.toObservableApprox.local_radius_pos
  have h_obs_φ_local := hφ.toObservableApprox.local_bound
  have h_obs_ψ_local := hψ.toObservableApprox.local_bound
  obtain ⟨Kφ, p, hKφ_nn, hpoly_φ⟩ := hφ.toObservableApprox.poly_growth
  obtain ⟨Kψ, q, hKψ_nn, hpoly_ψ⟩ := hψ.toObservableApprox.poly_growth
  set A : ℝ := ∑ i, |a i| with hA_def
  set B : ℝ := ∑ i, |b i| with hB_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set Cφ' : ℝ := 2 * Kφ + 2 * A with hCφ'_def
  set Cψ' : ℝ := 2 * Kψ + 2 * B with hCψ'_def
  have hCφ'_nn : 0 ≤ Cφ' := by rw [hCφ'_def]; linarith
  have hCψ'_nn : 0 ≤ Cψ' := by rw [hCψ'_def]; linarith
  -- Local radius and tail decay constant.
  set R : ℝ := min Rφ Rψ with hR_def
  have hR_pos : 0 < R := lt_min hRφ_pos hRψ_pos
  have hR_le_Rφ : R ≤ Rφ := min_le_left _ _
  have hR_le_Rψ : R ≤ Rψ := min_le_right _ _
  -- Polynomial degree for the tail.
  set N : ℕ := p + q + 2 with hN_def
  -- Gaussian moment constants.
  set M4 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2))
    with hM4_def
  set M_N4 : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 4 *
    (1 + ‖u‖ ^ N) * Real.exp (-(c * ‖u‖ ^ 2)) with hM_N4_def
  have hM4_nn : 0 ≤ M4 := by
    rw [hM4_def]
    apply MeasureTheory.integral_nonneg
    intro u
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hM_N4_nn : 0 ≤ M_N4 := by
    rw [hM_N4_def]
    apply MeasureTheory.integral_nonneg
    intro u
    have h1 : 0 ≤ ‖u‖ ^ 4 := pow_nonneg (norm_nonneg _) _
    have h2 : 0 ≤ 1 + ‖u‖ ^ N := by positivity
    exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
  -- Choose K and T₀.
  refine ⟨Cφ * Cψ * M4 + (3 * Cφ' * Cψ' / R ^ 4) * M_N4,
    1, le_refl _, ?_⟩
  intro t ht1
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have ht_sq_pos : 0 < t ^ 2 := pow_pos ht_pos 2
  -- Define Glocal and Gtail majorants.
  set Glocal : (ι → ℝ) → ℝ := fun u =>
    Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 * Real.exp (-(c * ‖u‖ ^ 2))
    with hGlocal_def
  set Gtail : (ι → ℝ) → ℝ := fun u =>
    (3 * Cφ' * Cψ' / R ^ 4 / t ^ 2) * (‖u‖ ^ 4 * (1 + ‖u‖ ^ N)) *
      Real.exp (-(c * ‖u‖ ^ 2)) with hGtail_def
  have hGlocal_nn : ∀ u, 0 ≤ Glocal u := by
    intro u
    rw [hGlocal_def]
    have h1 : 0 ≤ Cφ * Cψ * ‖u‖ ^ 4 :=
      mul_nonneg (mul_nonneg hCφ_nn hCψ_nn) (pow_nonneg (norm_nonneg _) _)
    exact mul_nonneg (div_nonneg h1 ht_sq_pos.le) (Real.exp_pos _).le
  have hGtail_nn : ∀ u, 0 ≤ Gtail u := by
    intro u
    rw [hGtail_def]
    have h1 : 0 ≤ 3 * Cφ' * Cψ' / R ^ 4 / t ^ 2 := by
      apply div_nonneg
      apply div_nonneg
      · positivity
      · positivity
      · exact ht_sq_pos.le
    have h2 : 0 ≤ ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) := by positivity
    exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
  -- Pointwise bound: |F(u)| ≤ Glocal(u) + Gtail(u).
  have hpt : ∀ u : ι → ℝ,
      |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
          (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))|
        ≤ Glocal u + Gtail u := by
    intro u
    by_cases hu : ‖u‖ ≤ R * Real.sqrt t
    · -- Local case.
      have huφ : ‖u‖ ≤ Rφ * Real.sqrt t :=
        le_trans hu (mul_le_mul_of_nonneg_right hR_le_Rφ hsqrt_pos.le)
      have huψ : ‖u‖ ≤ Rψ * Real.sqrt t :=
        le_trans hu (mul_le_mul_of_nonneg_right hR_le_Rψ hsqrt_pos.le)
      have h_local := abs_remainder_mul_remainder_mul_rescaled_weight_local_le
        V φ ψ H a b hCφ_nn hCψ_nn hc_pos h_obs_φ_local h_obs_ψ_local
        h_coer ht_pos u huφ huψ
      have h_glocal_eq : Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 *
            Real.exp (-(c * ‖u‖ ^ 2)) = Glocal u := by
        rw [hGlocal_def]
      rw [h_glocal_eq] at h_local
      linarith [hGtail_nn u]
    · -- Tail case.
      push_neg at hu
      have h_tail_indicator : 1 ≤ ‖u‖ ^ 4 / (R * Real.sqrt t) ^ 4 := by
        have h_pos : 0 < R * Real.sqrt t := mul_pos hR_pos hsqrt_pos
        have h_pow_le : (R * Real.sqrt t) ^ 4 ≤ ‖u‖ ^ 4 :=
          pow_le_pow_left₀ h_pos.le hu.le 4
        have h_pow_pos : 0 < (R * Real.sqrt t) ^ 4 := pow_pos h_pos 4
        rw [le_div_iff₀ h_pow_pos]
        linarith
      have h_RT4 : (R * Real.sqrt t) ^ 4 = R ^ 4 * t ^ 2 := by
        rw [mul_pow]
        rw [show (Real.sqrt t) ^ 4 = ((Real.sqrt t) ^ 2) ^ 2 from by ring,
            Real.sq_sqrt ht_pos.le]
      have h_tail_indicator' : 1 ≤ ‖u‖ ^ 4 / (R ^ 4 * t ^ 2) := by
        rw [← h_RT4]; exact h_tail_indicator
      -- Crude rem bound: |remφ · remψ · gW · exp| ≤ |remφ · remψ| · exp(-c·‖u‖²).
      have h_rw_le := rescaled_weight_le_coercive V H hc_pos h_coer ht_pos u
      have h_rem_glob := abs_remainder_mul_remainder_global_le φ ψ a b
        hKφ_nn hKψ_nn hpoly_φ hpoly_ψ ht1 u
      have h_poly_unify := poly_pair_le_single (ι := ι) p q u
      have hCφ'_eq : 2 * Kφ + 2 * (∑ i, |a i|) = Cφ' := by
        rw [hCφ'_def, hA_def]
      have hCψ'_eq : 2 * Kψ + 2 * (∑ i, |b i|) = Cψ' := by
        rw [hCψ'_def, hB_def]
      rw [hCφ'_eq, hCψ'_eq] at h_rem_glob
      -- Unify: |remφ · remψ| ≤ Cφ' · Cψ' · 3 · (1 + ‖u‖^N).
      have h_rem_unified : |(φ ((Real.sqrt t)⁻¹ • u) -
            (Real.sqrt t)⁻¹ * dot a u) *
          (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)|
          ≤ Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) := by
        have h_step1 : |(φ ((Real.sqrt t)⁻¹ • u) -
                (Real.sqrt t)⁻¹ * dot a u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)|
            ≤ Cφ' * Cψ' * ((1 + ‖u‖ ^ (p + 1)) *
                (1 + ‖u‖ ^ (q + 1))) := by
          have h := h_rem_glob
          -- h : ... ≤ Cφ' * Cψ' * (1 + ‖u‖^(p+1)) * (1 + ‖u‖^(q+1))
          have hCφψ_nn : 0 ≤ Cφ' * Cψ' := mul_nonneg hCφ'_nn hCψ'_nn
          linarith [h]
        have hCφψ_nn : 0 ≤ Cφ' * Cψ' := mul_nonneg hCφ'_nn hCψ'_nn
        have h_step2 : Cφ' * Cψ' * ((1 + ‖u‖ ^ (p + 1)) *
                (1 + ‖u‖ ^ (q + 1)))
            ≤ Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) := by
          rw [hN_def]
          exact mul_le_mul_of_nonneg_left h_poly_unify hCφψ_nn
        linarith
      -- Now combine: |F u| ≤ |remφ·remψ| · gW · exp ≤ ... · exp(-c‖u‖²).
      have h_rw_nn : 0 ≤ gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)) :=
        mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
      have h_rearr : (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
          = ((φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)) *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))) := by ring
      rw [h_rearr, abs_mul, abs_of_nonneg h_rw_nn]
      have hCφψ3_nn : 0 ≤ Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) := by
        apply mul_nonneg (mul_nonneg hCφ'_nn hCψ'_nn)
        positivity
      have h_step_a :
          |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)| *
              (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))
          ≤ (Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N))) *
              Real.exp (-(c * ‖u‖ ^ 2)) := by
        calc |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
              (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)| *
              (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))
            ≤ (Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N))) *
              (gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u))) :=
              mul_le_mul_of_nonneg_right h_rem_unified h_rw_nn
          _ ≤ (Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N))) *
              Real.exp (-(c * ‖u‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left h_rw_le hCφψ3_nn
      -- Multiply by indicator gain.
      have h_step_b : (Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N))) *
            Real.exp (-(c * ‖u‖ ^ 2))
          ≤ Gtail u := by
        rw [hGtail_def]
        have h_exp_nn : 0 ≤ Real.exp (-(c * ‖u‖ ^ 2)) := (Real.exp_pos _).le
        have h_R4_pos : 0 < R ^ 4 := pow_pos hR_pos 4
        -- Use indicator: 1 ≤ ‖u‖^4 / (R^4 · t²).
        have h_lhs_le : Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) ≤
            Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) *
              (‖u‖ ^ 4 / (R ^ 4 * t ^ 2)) := by
          have h_lhs_nn : 0 ≤ Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) := hCφψ3_nn
          calc Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N))
              = Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) * 1 := (mul_one _).symm
            _ ≤ Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) *
                (‖u‖ ^ 4 / (R ^ 4 * t ^ 2)) :=
                mul_le_mul_of_nonneg_left h_tail_indicator' h_lhs_nn
        have h_step_b_calc : Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) *
              (‖u‖ ^ 4 / (R ^ 4 * t ^ 2)) *
              Real.exp (-(c * ‖u‖ ^ 2))
            = 3 * Cφ' * Cψ' / R ^ 4 / t ^ 2 *
              (‖u‖ ^ 4 * (1 + ‖u‖ ^ N)) *
              Real.exp (-(c * ‖u‖ ^ 2)) := by
          field_simp
        calc (Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N))) *
              Real.exp (-(c * ‖u‖ ^ 2))
            ≤ (Cφ' * Cψ' * (3 * (1 + ‖u‖ ^ N)) *
                (‖u‖ ^ 4 / (R ^ 4 * t ^ 2))) *
                Real.exp (-(c * ‖u‖ ^ 2)) :=
              mul_le_mul_of_nonneg_right h_lhs_le h_exp_nn
          _ = 3 * Cφ' * Cψ' / R ^ 4 / t ^ 2 *
              (‖u‖ ^ 4 * (1 + ‖u‖ ^ N)) *
              Real.exp (-(c * ‖u‖ ^ 2)) := h_step_b_calc
      have h_F_le_Gtail :
          |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
              (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)| *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
          ≤ Gtail u := le_trans h_step_a h_step_b
      linarith [hGlocal_nn u]
  -- Integrability of Glocal, Gtail.
  have hGlocal_int : MeasureTheory.Integrable Glocal := by
    rw [hGlocal_def]
    have h1 := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 4
    -- Glocal = (Cφ·Cψ/t²) · (‖u‖^4 · exp(-c·‖u‖²))
    have h_eq : (fun u : ι → ℝ =>
          Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 * Real.exp (-(c * ‖u‖ ^ 2)))
        = fun u => (Cφ * Cψ / t ^ 2) *
            (‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2))) := by
      funext u; ring
    rw [h_eq]
    exact h1.const_mul _
  have hGtail_int : MeasureTheory.Integrable Gtail := by
    rw [hGtail_def]
    have h_a : MeasureTheory.Integrable (fun u : ι → ℝ =>
        ‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2))) :=
      integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 4
    have h_b : MeasureTheory.Integrable (fun u : ι → ℝ =>
        ‖u‖ ^ (4 + N) * Real.exp (-(c * ‖u‖ ^ 2))) :=
      integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos (4 + N)
    have h_sum : MeasureTheory.Integrable (fun u : ι → ℝ =>
        ‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2)) +
        ‖u‖ ^ (4 + N) * Real.exp (-(c * ‖u‖ ^ 2))) := h_a.add h_b
    have h_eq : (fun u : ι → ℝ =>
          3 * Cφ' * Cψ' / R ^ 4 / t ^ 2 * (‖u‖ ^ 4 * (1 + ‖u‖ ^ N)) *
            Real.exp (-(c * ‖u‖ ^ 2)))
        = fun u => (3 * Cφ' * Cψ' / R ^ 4 / t ^ 2) *
            (‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2)) +
             ‖u‖ ^ (4 + N) * Real.exp (-(c * ‖u‖ ^ 2))) := by
      funext u
      have h_pow_eq : ‖u‖ ^ 4 * ‖u‖ ^ N = ‖u‖ ^ (4 + N) := by
        rw [← pow_add]
      rw [show ‖u‖ ^ 4 * (1 + ‖u‖ ^ N) = ‖u‖ ^ 4 + ‖u‖ ^ 4 * ‖u‖ ^ N from
            by ring,
          h_pow_eq]
      ring
    rw [h_eq]
    exact h_sum.const_mul _
  -- ∫ Glocal = (Cφ·Cψ/t²) · M4.
  have hGlocal_eq : ∫ u : ι → ℝ, Glocal u = Cφ * Cψ * M4 / t ^ 2 := by
    rw [hGlocal_def, hM4_def]
    rw [show (fun u : ι → ℝ =>
              Cφ * Cψ * ‖u‖ ^ 4 / t ^ 2 * Real.exp (-(c * ‖u‖ ^ 2)))
            = fun u => (Cφ * Cψ / t ^ 2) *
                (‖u‖ ^ 4 * Real.exp (-(c * ‖u‖ ^ 2))) from by
        funext u; ring]
    rw [MeasureTheory.integral_const_mul]
    ring
  -- ∫ Gtail = (3·Cφ'·Cψ'/(R^4·t²)) · M_N4.
  have hGtail_eq : ∫ u : ι → ℝ, Gtail u =
      (3 * Cφ' * Cψ' / R ^ 4) * M_N4 / t ^ 2 := by
    rw [hGtail_def, hM_N4_def]
    rw [show (fun u : ι → ℝ =>
              3 * Cφ' * Cψ' / R ^ 4 / t ^ 2 * (‖u‖ ^ 4 * (1 + ‖u‖ ^ N)) *
                Real.exp (-(c * ‖u‖ ^ 2)))
            = fun u => (3 * Cφ' * Cψ' / R ^ 4 / t ^ 2) *
                (‖u‖ ^ 4 * (1 + ‖u‖ ^ N) *
                  Real.exp (-(c * ‖u‖ ^ 2))) from by
        funext u; ring]
    rw [MeasureTheory.integral_const_mul]
    ring
  -- Combine via triangle + integral_mono.
  have h_F_int_abs : MeasureTheory.Integrable (fun u : ι → ℝ =>
      (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
      (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
      gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u))) :=
    integrable_remainder_mul_remainder_mul_rescaled_weight V φ ψ H Hinv a b
      hV.toPotentialApprox hφ.toObservableApprox hψ.toObservableApprox
      hGauss ht1
  calc |∫ u : ι → ℝ,
            (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))|
      ≤ ∫ u : ι → ℝ,
          |(φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))| := by
            rw [show |∫ u, _| = ‖∫ u, _‖ from (Real.norm_eq_abs _).symm]
            exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u : ι → ℝ, (Glocal u + Gtail u) := by
          apply MeasureTheory.integral_mono_ae h_F_int_abs.norm
            (hGlocal_int.add hGtail_int)
          filter_upwards with u
          rw [Real.norm_eq_abs]
          exact hpt u
    _ = (∫ u, Glocal u) + ∫ u, Gtail u :=
          MeasureTheory.integral_add hGlocal_int hGtail_int
    _ = Cφ * Cψ * M4 / t ^ 2 +
        (3 * Cφ' * Cψ' / R ^ 4) * M_N4 / t ^ 2 := by
          rw [hGlocal_eq, hGtail_eq]
    _ = (Cφ * Cψ * M4 + (3 * Cφ' * Cψ' / R ^ 4) * M_N4) / t ^ 2 := by
          field_simp

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
  -- Strategy: pair_product_expansion + integral linearity, mirroring the
  -- weak-track decomposition with `m · rescaledPartition` subtracted off.
  have ht1' : (1 : ℝ) ≤ t := ht1
  have h_t_ne : t ≠ 0 := ht_pos.ne'
  have h_sqrt_ne : Real.sqrt t ≠ 0 := hsqrt_pos.ne'
  have h_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht_pos.le
  have h_decomp : t * rescaledNumerator V t (fun w => φ w * ψ w)
        - m * rescaledPartition V t
        = I1 + Real.sqrt t * I2 + Real.sqrt t * I3 + t * I4 := by
    set G1 : (ι → ℝ) → ℝ := fun u =>
      dot a u * dot b u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) with hG1_def
    set G2f : (ι → ℝ) → ℝ := fun u =>
      dot a u *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) with hG2f_def
    set G3f : (ι → ℝ) → ℝ := fun u =>
      dot b u *
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) with hG3f_def
    set G4f : (ι → ℝ) → ℝ := fun u =>
      (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
        (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) with hG4f_def
    -- I2 = ∫ G2f, etc. (definitional unfolding via funext).
    have hI2_eq : I2 = ∫ u, G2f u := by rw [hI2_def, hG2f_def]
    have hI3_eq : I3 = ∫ u, G3f u := by rw [hI3_def, hG3f_def]
    have hI4_eq : I4 = ∫ u, G4f u := by rw [hI4_def, hG4f_def]
    -- Pointwise algebraic identity from pair_product_expansion.
    have h_pp_pointwise : ∀ u : ι → ℝ,
        t * (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
        = G1 u + Real.sqrt t * G2f u + Real.sqrt t * G3f u + t * G4f u := by
      intro u
      have h_pp := pair_product_expansion φ ψ a b t ht_pos u
      have h_t_inv_sqrt : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
        field_simp
        rw [sq]; exact h_sq.symm
      have h_t_inv_self : t * (1/t) = 1 := mul_one_div_cancel h_t_ne
      rw [hG1_def, hG2f_def, hG3f_def, hG4f_def]
      show t * (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
        = dot a u * dot b u * gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))
          + Real.sqrt t *
              (dot a u *
                (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
                gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u))) +
            Real.sqrt t *
              (dot b u *
                (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
                gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u))) +
            t *
              ((φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
                (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) *
                gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))
      rw [h_pp]
      linear_combination
        (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)) *
          (dot a u * dot b u)) * h_t_inv_self +
        (gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)) *
          (dot a u *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) +
           dot b u *
            (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u))) *
          h_t_inv_sqrt
    -- Integrability companions for G1, G2f, G3f, G4f.
    have hG1_int : Integrable G1 :=
      integrable_dot_mul_dot_mul_rescaled_weight V H a b
        hV.toPotentialApprox.V_continuous
        hV.toPotentialApprox.coercive_const_pos
        hV.toPotentialApprox.coercive_bound ht_pos
    have hG2f_int : Integrable G2f :=
      integrable_dot_mul_remainder_mul_rescaled_weight V ψ H Hinv a b
        hV.toPotentialApprox hψ.toObservableApprox hGauss ht1'
    have hG3f_int : Integrable G3f :=
      integrable_dot_mul_remainder_mul_rescaled_weight V φ H Hinv b a
        hV.toPotentialApprox hφ.toObservableApprox hGauss ht1'
    have hG4f_int : Integrable G4f :=
      integrable_remainder_mul_remainder_mul_rescaled_weight V φ ψ H Hinv a b
        hV.toPotentialApprox hφ.toObservableApprox hψ.toObservableApprox
        hGauss ht1'
    -- Integrability of the sum and of t · pair · gW · exp.
    have hG_sum_int : Integrable (fun u : ι → ℝ =>
        G1 u + Real.sqrt t * G2f u + Real.sqrt t * G3f u + t * G4f u) := by
      have h_G2 := hG2f_int.const_mul (Real.sqrt t)
      have h_G3 := hG3f_int.const_mul (Real.sqrt t)
      have h_G4 := hG4f_int.const_mul t
      exact ((hG1_int.add h_G2).add h_G3).add h_G4
    have h_int_t_pair : Integrable (fun u : ι → ℝ =>
        t * (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) := by
      apply hG_sum_int.congr
      filter_upwards with u
      exact (h_pp_pointwise u).symm
    -- Integrate the pointwise identity:
    -- ∫ t · pair · gW · exp = ∫ G1 + √t · ∫ G2f + √t · ∫ G3f + t · ∫ G4f.
    have h_int_eq : ∫ u : ι → ℝ,
          t * (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)) *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))
        = (∫ u, G1 u) + Real.sqrt t * (∫ u, G2f u) +
            Real.sqrt t * (∫ u, G3f u) + t * (∫ u, G4f u) := by
      have h_int_sum_eq : ∫ u : ι → ℝ,
            t * (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))
          = ∫ u, G1 u + Real.sqrt t * G2f u + Real.sqrt t * G3f u +
              t * G4f u := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        exact h_pp_pointwise u
      rw [h_int_sum_eq]
      -- ∫ (G1 + √t·G2f + √t·G3f + t·G4f) = sum of integrals.
      rw [show (fun u : ι → ℝ => G1 u + Real.sqrt t * G2f u +
                Real.sqrt t * G3f u + t * G4f u)
              = fun u => (G1 u + Real.sqrt t * G2f u +
                  Real.sqrt t * G3f u) + t * G4f u from rfl]
      have h_inner3 : Integrable (fun u : ι → ℝ =>
          G1 u + Real.sqrt t * G2f u + Real.sqrt t * G3f u) := by
        have h_G2 := hG2f_int.const_mul (Real.sqrt t)
        have h_G3 := hG3f_int.const_mul (Real.sqrt t)
        exact (hG1_int.add h_G2).add h_G3
      have h_t_G4 : Integrable (fun u : ι → ℝ => t * G4f u) :=
        hG4f_int.const_mul t
      rw [MeasureTheory.integral_add h_inner3 h_t_G4]
      have h_inner2 : Integrable (fun u : ι → ℝ =>
          G1 u + Real.sqrt t * G2f u) := by
        have h_G2 := hG2f_int.const_mul (Real.sqrt t)
        exact hG1_int.add h_G2
      have h_sqrt_G3 : Integrable (fun u : ι → ℝ =>
          Real.sqrt t * G3f u) := hG3f_int.const_mul _
      rw [MeasureTheory.integral_add h_inner2 h_sqrt_G3]
      have h_sqrt_G2 : Integrable (fun u : ι → ℝ =>
          Real.sqrt t * G2f u) := hG2f_int.const_mul _
      rw [MeasureTheory.integral_add hG1_int h_sqrt_G2]
      rw [MeasureTheory.integral_const_mul (Real.sqrt t),
          MeasureTheory.integral_const_mul (Real.sqrt t),
          MeasureTheory.integral_const_mul t]
    -- t · N = ∫ G1 + √t · I2 + √t · I3 + t · I4.
    have h_t_N : t * rescaledNumerator V t (fun w => φ w * ψ w)
        = (∫ u, G1 u) + Real.sqrt t * I2 + Real.sqrt t * I3 + t * I4 := by
      rw [rescaledNumerator_eq_gaussian_form V (fun w => φ w * ψ w) H t,
          ← MeasureTheory.integral_const_mul]
      have h_eq_lambda : (fun u : ι → ℝ =>
            t * (φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u) *
                gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u))))
          = fun u => t * (φ ((Real.sqrt t)⁻¹ • u) *
              ψ ((Real.sqrt t)⁻¹ • u)) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)) := by
        funext u; ring
      rw [h_eq_lambda, h_int_eq, hI2_eq, hI3_eq, hI4_eq]
    -- m · D = ∫ m · gW · exp.
    have h_int_gW_exp : Integrable (fun u : ι → ℝ =>
        gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) :=
      integrable_rescaled_weight V hV.toPotentialApprox.V_continuous H
        hV.toPotentialApprox.coercive_const_pos
        hV.toPotentialApprox.coercive_bound ht_pos
    have h_int_m_gW_exp : Integrable (fun u : ι → ℝ =>
        m * (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))) :=
      h_int_gW_exp.const_mul m
    have h_m_D : m * rescaledPartition V t
        = ∫ u, m * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) := by
      rw [rescaledPartition_eq_gaussian_form V H t]
      rw [MeasureTheory.integral_const_mul]
    -- I1 = ∫ G1 - m · D (centered form).
    have hI1_eq : I1 = (∫ u, G1 u) - m * rescaledPartition V t := by
      rw [h_m_D, hI1_def, hG1_def]
      rw [show (fun u : ι → ℝ => (dot a u * dot b u - m) * gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))
              = fun u => dot a u * dot b u * gaussianWeight H u *
                  Real.exp (-(rescaledPerturbation V H t u))
                - m * (gaussianWeight H u *
                    Real.exp (-(rescaledPerturbation V H t u))) from by
            funext u; ring]
      exact MeasureTheory.integral_sub hG1_int h_int_m_gW_exp
    -- Compose.
    rw [h_t_N, hI1_eq]; ring
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
