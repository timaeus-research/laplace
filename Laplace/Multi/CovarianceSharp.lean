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
  sorry

end MainTheorem

end Laplace.Multi
