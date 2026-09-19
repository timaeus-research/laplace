/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LocalUniform

/-!
# Uniform agreement of the gradients of the Boltzmann weights

`LocalUniform` gives, for smooth nonnegative losses with exact smooth-test
agreement, `sup_K |e^{-tL₂} - e^{-tL₁}| = O(t^{-N})` for every `N` on every
compact `K`. Here the same is proved for the gradients: with
`h_t = e^{-tL₂} - e^{-tL₁}`,
`sup_K ‖D h_t‖ = O(t^{-N})` for every `N`
(`eventually_uniform_norm_fderiv_exp_sub_le`), and pointwise
`D h_t(x) v = o(t^{-∞})` (`superPoly_fderiv_exp_sub_at`).

The mechanism is a second interpolation. The Hessian of a weight is
`D²(e^{-tL}) = D(e^{-tL}) ⊗ (-t DL) + e^{-tL} (-t D²L)`, of norm at most
`t²(‖DL‖² + ‖D²L‖)` for `t ≥ 1`
(`norm_fderiv_fderiv_expWeight_le`), so `‖D²h_t‖ ≤ B t²` on the unit
thickening of `K` (`exists_hessian_bound_on`). A deterministic
interpolation lemma (`norm_fderiv_le_of_bounds`) then says: if `|h| ≤ A`
and `‖D²h‖ ≤ M` on the closed unit ball about `x`, then
`‖Dh(x)‖ ≤ 2A/s + M s` for every `0 < s ≤ 1`, by the affine-error mean
value inequality on the closed ball of radius `s` (Taylor to first order
along `x + s v` for unit `v`). Choosing `s = t^{-(N+3)}` and feeding the
uniform weight bound at exponent `2N + 3` gives the theorem.

Only the first derivative is treated; the induction to all orders needs
polynomial-in-`t` bounds for all derivatives of the weights and is left
for a later tide.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-! ### Second derivatives of the weights -/

omit [Fintype ι] in
/-- The weight times a scaled vector: `‖e^{-tL} • (-(t • v))‖ ≤ t ‖v‖`, in any
normed space. -/
theorem norm_expWeight_smul_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : (ι → ℝ) → ℝ} (hL : ∀ w, 0 ≤ L w) {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) (v : F) :
    ‖Real.exp (-(t * L x)) • (-(t • v))‖ ≤ t * ‖v‖ := by
  rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg ht]
  calc Real.exp (-(t * L x)) * (t * ‖v‖) ≤ 1 * (t * ‖v‖) :=
        mul_le_mul_of_nonneg_right (expWeight_le_one hL ht x) (by positivity)
    _ = t * ‖v‖ := one_mul _

/-- The derivative field of the weight, as a function. -/
theorem fderiv_expWeight_eq {L : (ι → ℝ) → ℝ} (hL : ContDiff ℝ ∞ L) (t : ℝ) :
    fderiv ℝ (fun w ↦ Real.exp (-(t * L w))) =
      fun y ↦ Real.exp (-(t * L y)) • (-(t • fderiv ℝ L y)) := by
  funext y
  exact (hasFDerivAt_expWeight (hL.differentiable (by simp) y) t).fderiv

/-- The derivative field of the weight is differentiable, with the product-rule
derivative. -/
theorem hasFDerivAt_fderiv_expWeight {L : (ι → ℝ) → ℝ} (hL : ContDiff ℝ ∞ L) (t : ℝ)
    (y : ι → ℝ) :
    HasFDerivAt (fderiv ℝ (fun w ↦ Real.exp (-(t * L w))))
      (Real.exp (-(t * L y)) • (-(t • fderiv ℝ (fderiv ℝ L) y)) +
        (Real.exp (-(t * L y)) • (-(t • fderiv ℝ L y))).smulRight (-(t • fderiv ℝ L y))) y := by
  rw [fderiv_expWeight_eq hL t]
  have hc : HasFDerivAt (fun w ↦ Real.exp (-(t * L w)))
      (Real.exp (-(t * L y)) • (-(t • fderiv ℝ L y))) y :=
    hasFDerivAt_expWeight (hL.differentiable (by simp) y) t
  have hDL : DifferentiableAt ℝ (fderiv ℝ L) y :=
    ((contDiff_infty_iff_fderiv.mp hL).2.differentiable (by simp)) y
  have hf : HasFDerivAt (fun y ↦ -(t • fderiv ℝ L y)) (-(t • fderiv ℝ (fderiv ℝ L) y)) y :=
    (hDL.hasFDerivAt.const_smul t).neg
  exact hc.smul hf

/-- **Hessian bound for a weight**: `‖D²(e^{-tL})(y)‖ ≤ t² (‖DL(y)‖² + ‖D²L(y)‖)`
for `t ≥ 1`. -/
theorem norm_fderiv_fderiv_expWeight_le {L : (ι → ℝ) → ℝ} (hL : ContDiff ℝ ∞ L)
    (hL0 : ∀ w, 0 ≤ L w) {t : ℝ} (ht : 1 ≤ t) (y : ι → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L w)))) y‖ ≤
      t ^ 2 * (‖fderiv ℝ L y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L) y‖) := by
  rw [(hasFDerivAt_fderiv_expWeight hL t y).fderiv]
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hA : ‖Real.exp (-(t * L y)) • (-(t • fderiv ℝ (fderiv ℝ L) y))‖ ≤
      t * ‖fderiv ℝ (fderiv ℝ L) y‖ := norm_expWeight_smul_le hL0 ht0 y _
  have hB : ‖(Real.exp (-(t * L y)) • (-(t • fderiv ℝ L y))).smulRight
      (-(t • fderiv ℝ L y))‖ ≤ (t * ‖fderiv ℝ L y‖) * (t * ‖fderiv ℝ L y‖) := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have h1 := norm_expWeight_smul_le hL0 ht0 y (fderiv ℝ L y)
    have h2 : ‖-(t • fderiv ℝ L y)‖ = t * ‖fderiv ℝ L y‖ := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hnn : 0 ≤ ‖fderiv ℝ (fderiv ℝ L) y‖ := norm_nonneg _
  calc ‖Real.exp (-(t * L y)) • (-(t • fderiv ℝ (fderiv ℝ L) y)) +
        (Real.exp (-(t * L y)) • (-(t • fderiv ℝ L y))).smulRight (-(t • fderiv ℝ L y))‖
      ≤ ‖Real.exp (-(t * L y)) • (-(t • fderiv ℝ (fderiv ℝ L) y))‖ +
        ‖(Real.exp (-(t * L y)) • (-(t • fderiv ℝ L y))).smulRight
          (-(t • fderiv ℝ L y))‖ := norm_add_le _ _
    _ ≤ t * ‖fderiv ℝ (fderiv ℝ L) y‖ + (t * ‖fderiv ℝ L y‖) * (t * ‖fderiv ℝ L y‖) :=
        add_le_add hA hB
    _ ≤ t ^ 2 * (‖fderiv ℝ L y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L) y‖) := by
        have h3 : t * ‖fderiv ℝ (fderiv ℝ L) y‖ ≤ t ^ 2 * ‖fderiv ℝ (fderiv ℝ L) y‖ := by
          have : t ≤ t ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this hnn
        nlinarith [h3]

/-- The derivative field of the weight difference, as a function. -/
theorem fderiv_weightDiff_eq {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂) (t : ℝ) :
    fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) =
      fun y ↦ fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w))) y -
        fderiv ℝ (fun w ↦ Real.exp (-(t * L₁ w))) y := by
  funext y
  have hh : HasFDerivAt (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w)))
      (fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w))) y -
        fderiv ℝ (fun w ↦ Real.exp (-(t * L₁ w))) y) y :=
    ((h2.differentiable (by simp) y).const_mul t).neg.exp.hasFDerivAt.sub
      ((h1.differentiable (by simp) y).const_mul t).neg.exp.hasFDerivAt
  exact hh.fderiv

/-- The derivative field of the weight difference is differentiable. -/
theorem hasFDerivAt_fderiv_weightDiff {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂) (t : ℝ) (y : ι → ℝ) :
    HasFDerivAt (fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))))
      (fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)))) y -
        fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L₁ w)))) y) y := by
  rw [fderiv_weightDiff_eq h1 h2 t]
  have hh2 := hasFDerivAt_fderiv_expWeight h2 t y
  have hh1 := hasFDerivAt_fderiv_expWeight h1 t y
  have := hh2.sub hh1
  rwa [hh2.fderiv, hh1.fderiv]

/-- **Hessian bound for the difference on a compact**: `‖D²h_t‖ ≤ B t²` for `t ≥ 1`. -/
theorem exists_hessian_bound_on {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w) {S : Set (ι → ℝ)} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 1 ≤ t → ∀ y ∈ S,
      ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w)))) y‖ ≤
        B * t ^ 2 := by
  have hc : Continuous fun y ↦ (‖fderiv ℝ L₁ y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L₁) y‖) +
      (‖fderiv ℝ L₂ y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L₂) y‖) := by
    have c1 := (h1.continuous_fderiv (by simp)).norm.pow 2
    have c2 := ((contDiff_infty_iff_fderiv.mp h1).2.continuous_fderiv (by simp)).norm
    have c3 := (h2.continuous_fderiv (by simp)).norm.pow 2
    have c4 := ((contDiff_infty_iff_fderiv.mp h2).2.continuous_fderiv (by simp)).norm
    exact (c1.add c2).add (c3.add c4)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht y hy ↦ ?_⟩
  have hBy := hB y hy
  rw [Real.norm_eq_abs] at hBy
  have hsum : (‖fderiv ℝ L₁ y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L₁) y‖) +
      (‖fderiv ℝ L₂ y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L₂) y‖) ≤ max B 0 :=
    (le_abs_self _).trans (hBy.trans (le_max_left _ _))
  rw [(hasFDerivAt_fderiv_weightDiff h1 h2 t y).fderiv]
  have e1 := norm_fderiv_fderiv_expWeight_le h1 hL1 ht y
  have e2 := norm_fderiv_fderiv_expWeight_le h2 hL2 ht y
  have ht2 : 0 ≤ t ^ 2 := by positivity
  calc ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)))) y -
        fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L₁ w)))) y‖
      ≤ ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)))) y‖ +
        ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L₁ w)))) y‖ := norm_sub_le _ _
    _ ≤ t ^ 2 * (‖fderiv ℝ L₂ y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L₂) y‖) +
        t ^ 2 * (‖fderiv ℝ L₁ y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L₁) y‖) := add_le_add e2 e1
    _ = t ^ 2 * ((‖fderiv ℝ L₁ y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L₁) y‖) +
        (‖fderiv ℝ L₂ y‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ L₂) y‖)) := by ring
    _ ≤ t ^ 2 * max B 0 := mul_le_mul_of_nonneg_left hsum ht2
    _ = max B 0 * t ^ 2 := mul_comm _ _

/-! ### The interpolation lemma -/

/-- **Gradient interpolation.** If `|h| ≤ A` and `‖D²h‖ ≤ M` on the closed unit
ball about `x`, then `‖Dh(x)‖ ≤ 2A/s + M s` for every `0 < s ≤ 1`. -/
theorem norm_fderiv_le_of_bounds {h : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hd : ∀ y ∈ Metric.closedBall x 1, DifferentiableAt ℝ h y)
    (hd2 : ∀ y ∈ Metric.closedBall x 1, DifferentiableAt ℝ (fderiv ℝ h) y)
    {A M : ℝ} (hA0 : 0 ≤ A) (hM0 : 0 ≤ M)
    (hA : ∀ y ∈ Metric.closedBall x 1, |h y| ≤ A)
    (hM : ∀ y ∈ Metric.closedBall x 1, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ‖fderiv ℝ h x‖ ≤ 2 * A / s + M * s := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv ↦ ?_
  have hx1 : x ∈ Metric.closedBall x 1 := Metric.mem_closedBall_self zero_le_one
  have hsub : Metric.closedBall x s ⊆ Metric.closedBall x 1 :=
    Metric.closedBall_subset_closedBall hs1
  -- Lipschitz bound for `Dh` on the small closed ball
  have hlip : ∀ z ∈ Metric.closedBall x s, ‖fderiv ℝ h z - fderiv ℝ h x‖ ≤ M * s := by
    intro z hz
    have hz1 : z ∈ Metric.closedBall x 1 := hsub hz
    have := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le hd2 hM hx1 hz1
    have hdz : ‖z - x‖ ≤ s := by
      have := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdz hM0)
  -- the point `x + s v` lies on the small sphere
  have hy : x + s • v ∈ Metric.closedBall x s := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hv,
      Real.norm_eq_abs, abs_of_pos hs, mul_one]
  have hy1 : x + s • v ∈ Metric.closedBall x 1 := hsub hy
  -- Taylor with affine error on the small closed ball
  have hT := (convex_closedBall x s).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz ↦ hd z (hsub hz)) hlip (Metric.mem_closedBall_self hs.le) hy
  rw [add_sub_cancel_left, map_smul, norm_smul, hv, Real.norm_of_nonneg hs.le,
    mul_one, smul_eq_mul, Real.norm_eq_abs] at hT
  -- `hT : |h (x + s v) - h x - s * Dh x v| ≤ M * s * s`
  have hA1 := hA _ hy1
  have hA2 := hA x hx1
  have hbound : s * |fderiv ℝ h x v| ≤ 2 * A + M * s * s := by
    have htri : |s * fderiv ℝ h x v| ≤ |h (x + s • v)| + |h x| +
        |h (x + s • v) - h x - s * fderiv ℝ h x v| := by
      have h4 : |s * fderiv ℝ h x v| ≤
          |h (x + s • v) - h x| + |h (x + s • v) - h x - s * fderiv ℝ h x v| := by
        have := abs_sub (h (x + s • v) - h x) (h (x + s • v) - h x - s * fderiv ℝ h x v)
        rwa [sub_sub_cancel] at this
      have h5 := abs_sub (h (x + s • v)) (h x)
      linarith
    rw [abs_mul, abs_of_pos hs] at htri
    linarith
  rw [Real.norm_eq_abs]
  rw [div_add' _ _ _ hs.ne', le_div_iff₀ hs]
  nlinarith [hbound]

/-! ### Uniform agreement of the gradients -/

/-- **Uniform agreement of the gradients beyond all orders.** For smooth
nonnegative losses with exact smooth-test agreement and compact `K`: for every
`N` there is `C` with `‖D(e^{-tL₂} - e^{-tL₁})(x)‖ ≤ C t^{-N}` for all `x ∈ K`,
eventually in `t`. -/
theorem eventually_uniform_norm_fderiv_exp_sub_le {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ᶠ t in atTop, ∀ x ∈ K,
      ‖fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x‖ ≤
        C * t ^ (-(N : ℝ)) := by
  set K' := Metric.cthickening 1 K with hK'_def
  have hK' : IsCompact K' := hK.cthickening
  obtain ⟨B, hB0, hB⟩ := exists_hessian_bound_on h1 h2 hL1 hL2 hK'
  intro N
  obtain ⟨C₁, hC₁⟩ := eventually_uniform_abs_exp_sub_le h1 h2 hL1 hL2 hexact hK' (2 * N + 3)
  set C₁' := max C₁ 0 with hC₁'_def
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  refine ⟨2 * C₁' + B, ?_⟩
  filter_upwards [hC₁, eventually_ge_atTop (1 : ℝ)] with t hAt ht
  intro x hx
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have htne : t ≠ 0 := htpos.ne'
  have hball : Metric.closedBall x 1 ⊆ K' := fun y hy ↦
    Metric.mem_cthickening_of_dist_le y x 1 K hx (Metric.mem_closedBall.mp hy)
  -- the inputs of the interpolation lemma
  set s : ℝ := (t ^ (N + 3))⁻¹ with hs_def
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht)
  have hA : ∀ y ∈ Metric.closedBall x 1,
      |Real.exp (-(t * L₂ y)) - Real.exp (-(t * L₁ y))| ≤ C₁' * (t ^ (2 * N + 3))⁻¹ := by
    intro y hy
    have h := hAt y (hball hy)
    have hconv : t ^ (-((2 * N + 3 : ℕ) : ℝ)) = (t ^ (2 * N + 3))⁻¹ := by
      rw [Real.rpow_neg htpos.le, Real.rpow_natCast]
    rw [hconv] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hM : ∀ y ∈ Metric.closedBall x 1,
      ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w)))) y‖ ≤
        B * t ^ 2 := fun y hy ↦ hB t ht y (hball hy)
  have hd : ∀ y ∈ Metric.closedBall x 1, DifferentiableAt ℝ
      (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) y := fun y _ ↦
    ((h2.differentiable (by simp) y).const_mul t).neg.exp.sub
      ((h1.differentiable (by simp) y).const_mul t).neg.exp
  have hd2 : ∀ y ∈ Metric.closedBall x 1, DifferentiableAt ℝ
      (fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w)))) y := fun y _ ↦
    (hasFDerivAt_fderiv_weightDiff h1 h2 t y).differentiableAt
  have hinterp := norm_fderiv_le_of_bounds hd hd2 (by positivity) (by positivity) hA hM hs hs1
  -- the exponent arithmetic
  have e1 : 2 * (C₁' * (t ^ (2 * N + 3))⁻¹) / s = 2 * C₁' * (t ^ N)⁻¹ := by
    rw [hs_def]
    field_simp
    ring
  have e2 : B * t ^ 2 * s = B * (t ^ (N + 1))⁻¹ := by
    rw [hs_def]
    field_simp
    ring
  have e3 : (t ^ (N + 1))⁻¹ ≤ (t ^ N)⁻¹ :=
    inv_anti₀ (pow_pos htpos N) (pow_le_pow_right₀ ht (Nat.le_succ N))
  have hconv : t ^ (-(N : ℝ)) = (t ^ N)⁻¹ := by
    rw [Real.rpow_neg htpos.le, Real.rpow_natCast]
  calc ‖fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x‖
      ≤ 2 * (C₁' * (t ^ (2 * N + 3))⁻¹) / s + B * t ^ 2 * s := hinterp
    _ = 2 * C₁' * (t ^ N)⁻¹ + B * (t ^ (N + 1))⁻¹ := by rw [e1, e2]
    _ ≤ 2 * C₁' * (t ^ N)⁻¹ + B * (t ^ N)⁻¹ := by gcongr
    _ = (2 * C₁' + B) * (t ^ N)⁻¹ := by ring
    _ = (2 * C₁' + B) * t ^ (-(N : ℝ)) := by rw [hconv]

/-- **Pointwise agreement of the gradients beyond all orders**: for every point
`x` and direction `v`, `D(e^{-tL₂} - e^{-tL₁})(x) v = o(t^{-∞})`. -/
theorem superPoly_fderiv_exp_sub_at {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    (x v : ι → ℝ) :
    SuperPoly fun t ↦
      fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x v := by
  refine superPoly_of_forall_eventually_le fun N ↦ ?_
  obtain ⟨C, hC⟩ := eventually_uniform_norm_fderiv_exp_sub_le h1 h2 hL1 hL2 hexact
    (isCompact_singleton (x := x)) N
  refine ⟨C * ‖v‖, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  have hx := ht x (Set.mem_singleton x)
  have hrpos : 0 ≤ t ^ (-(N : ℝ)) := (Real.rpow_pos_of_pos htpos _).le
  calc |fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x v|
      = ‖fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x v‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * t ^ (-(N : ℝ)) * ‖v‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = C * ‖v‖ * t ^ (-(N : ℝ)) := by ring

end Laplace
