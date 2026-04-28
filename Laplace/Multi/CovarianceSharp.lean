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
* Stage 3 — centered numerator bound: structurally complete with four
  technical sorries:
  - `abs_integral_corrected_bracket_centered_bilinear_le` (helper 1's K/t
    bound on the corrected-bracket integral; deferred Glocal+Gtail
    bookkeeping ~500-700 LOC);
  - `abs_integral_dot_mul_jet_remainder_sharp_le` (helpers 2/3, cross
    terms, K/(t·√t));
  - `abs_integral_remainder_remainder_sharp_le` (helper 4, quadratic
    remainder, K/t²);
  - `h_decomp` algebraic identity inside
    `rescaledNumerator_centered_pair_sharp`.
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
  sorry

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
