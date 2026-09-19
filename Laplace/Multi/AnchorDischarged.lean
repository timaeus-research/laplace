/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ProjectiveClosure

/-!
# The anchoring theorems with the anchor discharged

`OnePointAnchoring.one_point_anchoring_contradiction` and
`Anchoring.anchored_proportionality_remove_scalar` carry a hypothesis
`hanchor_low`: a positive polynomial lower bound on the reference moment
`∫ φ₀ e^{-tL₁}` of an anchoring observable. `ProjectiveClosure` proves
that bound (`anchor_lower_bound_eventually`) whenever `φ₀` is a
nonnegative bump equal to `1` near a `C²` zero of `L₁`. This file restates
both theorems in that form, so that no polynomial lower bound need be
supplied by a caller.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **Anchored gauge removal, anchor discharged.** An anchoring observable
`φ₀`, nonnegative, continuous, compactly supported, equal to `1` near a `C²`
zero `p₀` of `L₁` and supported where `L₁ = L₂`, forces the common gauge to
one: the moment difference of every boundedly-referenced observable is
beyond all orders. -/
theorem anchored_proportionality_remove_scalar' {L₁ L₂ φ₀ : (ι → ℝ) → ℝ}
    (hL1c : Continuous L₁) (hL1 : ∀ w, 0 ≤ L₁ w)
    {p₀ : ι → ℝ} (hp₀ : L₁ p₀ = 0) (hC1 : ContDiffAt ℝ 2 L₁ p₀)
    (hφ₀c : Continuous φ₀) (hφ₀s : HasCompactSupport φ₀) (hφ₀0 : ∀ w, 0 ≤ φ₀ w)
    (hφ₀1 : ∀ᶠ w in 𝓝 p₀, φ₀ w = 1)
    {V : Set (ι → ℝ)} (hEq : Set.EqOn L₁ L₂ V) (hsupp : tsupport φ₀ ⊆ V)
    {C I₁ I₂ : ℝ → ℝ}
    (hprop₀ : SuperPoly fun t ↦ (∫ w, φ₀ w * Real.exp (-(t * L₂ w))) -
      C t * ∫ w, φ₀ w * Real.exp (-(t * L₁ w)))
    (hprop : SuperPoly fun t ↦ I₂ t - C t * I₁ t)
    (hbounded : I₁ =O[atTop] fun _ : ℝ ↦ (1 : ℝ)) :
    SuperPoly fun t ↦ I₂ t - I₁ t := by
  obtain ⟨κ, hκ, hlow⟩ := anchor_lower_bound_eventually hL1c hL1 hp₀ hC1 hφ₀c hφ₀s hφ₀0 hφ₀1
  exact anchored_proportionality_remove_scalar hκ hlow
    (Eventually.of_forall fun t ↦ anchor_moment_eq hEq hsupp t) hprop₀ hprop hbounded

/-- **One-point anchoring contradiction, anchor discharged.** The analytic
package of the pencil–sector theorem together with a common-gauge
proportionality anchored at a nonnegative bump equal to `1` near a `C²` zero
of `L₁`, supported where the losses agree, is impossible. -/
theorem one_point_anchoring_contradiction' (L₁ L₂ ψ : (ι → ℝ) → ℝ)
    {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {r : ℝ≥0∞} (m : ℕ)
    (hg : HasFPowerSeriesOnBall (fun w ↦ L₂ w - L₁ w) p 0 r)
    (hlow : ∀ k, k < m → ∀ x : ι → ℝ, (p k) (fun _ ↦ x) = 0)
    {x₀ : ι → ℝ} (hx₀ : (p m) (fun _ ↦ x₀) ≠ 0) (hx₀n : ‖x₀‖ = 3 / 2)
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hsum : ∀ w : ι → ℝ, ‖w‖ ≤ R → L₁ w + L₂ w ≤ C0 * ‖w‖ ^ 2)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ R → ψ w = 1)
    {C : ℝ → ℝ} {φ₀ : (ι → ℝ) → ℝ} {V : Set (ι → ℝ)}
    (hEq : Set.EqOn L₁ L₂ V) (hsupp : tsupport φ₀ ⊆ V)
    {p₀ : ι → ℝ} (hp₀ : L₁ p₀ = 0) (hC1 : ContDiffAt ℝ 2 L₁ p₀)
    (hφ₀c : Continuous φ₀) (hφ₀s : HasCompactSupport φ₀) (hφ₀0 : ∀ w, 0 ≤ φ₀ w)
    (hφ₀1 : ∀ᶠ w in 𝓝 p₀, φ₀ w = 1)
    (hprop₀ : SuperPoly fun t : ℝ ↦
      (∫ w : ι → ℝ, φ₀ w * Real.exp (-(t * L₂ w))) -
        C t * ∫ w : ι → ℝ, φ₀ w * Real.exp (-(t * L₁ w)))
    (hprop : SuperPoly fun t : ℝ ↦
      (∫ w : ι → ℝ, ((L₂ w - L₁ w) * ψ w) *
          Real.exp (-(t * L₂ w))) -
        C t * ∫ w : ι → ℝ, ((L₂ w - L₁ w) * ψ w) *
          Real.exp (-(t * L₁ w))) :
    False := by
  obtain ⟨κ, hκ, hanchor_low⟩ :=
    anchor_lower_bound_eventually hL1c hL1 hp₀ hC1 hφ₀c hφ₀s hφ₀0 hφ₀1
  exact one_point_anchoring_contradiction L₁ L₂ ψ m hg hlow hx₀ hx₀n hL1c hL2c hL1 hL2
    hC0 hR hsum hψc hψs hψ0 hψ1 hEq hsupp hκ hanchor_low hprop₀ hprop

end Laplace
