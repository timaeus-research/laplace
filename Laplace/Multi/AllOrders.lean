/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.DerivativeAgreement

/-!
# Uniform agreement of all derivatives of the Boltzmann weights

`LocalUniform` and `DerivativeAgreement` give uniform beyond-all-orders
agreement of the weights `e^{-tL_i}` and of their gradients on compacts,
for smooth nonnegative losses with exact smooth-test agreement. Here the
statement is proved for every order: for every `k`, every compact `K` and
every `N` there is `C` with
`‖D^k(e^{-tL₂} - e^{-tL₁})(x)‖ ≤ C t^{-N}` for all `x ∈ K` eventually
(`eventually_uniform_norm_iteratedFDeriv_exp_sub_le`).

Two ingredients:

* **Polynomial growth of all derivatives of a weight.** By induction with
  the Leibniz bound `norm_iteratedFDeriv_smul_le` applied to
  `D(e^{-tL}) = e^{-tL} • (-t DL)`: on a compact, `‖D^k e^{-tL}‖ ≤ C_k t^k`
  for `t ≥ 1` (`exists_iteratedFDeriv_expWeight_bound_on`).
* **A vector-valued interpolation lemma.** If `‖g‖ ≤ A` on the closed ball of
  radius `s` about `x` and `Dg` is `Ms`-close to `Dg(x)` there, then
  `‖Dg(x)‖ ≤ 2A/s + Ms` (`norm_fderiv_le_of_lipschitz_bounds`). Applied to
  `g = D^k h_t`, whose derivative is `D^{k+1} h_t` up to the currying
  isometry, with `s = t^{-(N+k+3)}`, the Lipschitz input coming from the
  mean value inequality and the growth bound at order `k + 2`, and the
  amplitude input from the induction hypothesis on the unit thickening at
  exponent `2N + k + 3`.
-/

open Asymptotics Filter MeasureTheory
open scoped Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-! ### Grade bookkeeping -/

/-- A natural number is below `∞` in `WithTop ℕ∞`. -/
theorem natCast_lt_infty (n : ℕ) : (n : WithTop ℕ∞) < ∞ := by
  rw [← WithTop.coe_natCast]
  exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)

theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := (natCast_lt_infty n).le

/-! ### Polynomial growth of the derivatives of a weight -/

/-- The weight is smooth. -/
theorem contDiff_expWeight {L : (ι → ℝ) → ℝ} (hL : ContDiff ℝ ∞ L) (t : ℝ) :
    ContDiff ℝ ∞ (fun w ↦ Real.exp (-(t * L w))) :=
  Real.contDiff_exp.comp ((contDiff_const.mul hL).neg)

/-- A common bound for the iterated derivatives of `DL` up to order `k` on a
compact set. -/
theorem exists_iteratedFDeriv_fderiv_bound_on {L : (ι → ℝ) → ℝ} (hL : ContDiff ℝ ∞ L)
    {S : Set (ι → ℝ)} (hS : IsCompact S) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j ≤ k, ∀ y ∈ S, ‖iteratedFDeriv ℝ j (fderiv ℝ L) y‖ ≤ M := by
  have hDL : ContDiff ℝ ∞ (fderiv ℝ L) := (contDiff_infty_iff_fderiv.mp hL).2
  induction k with
  | zero =>
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
      (hDL.continuous_iteratedFDeriv (m := 0) (by exact_mod_cast natCast_le_infty 0)).continuousOn
    refine ⟨max M 0, le_max_right _ _, fun j hj y hy ↦ ?_⟩
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    exact (hM y hy).trans (le_max_left _ _)
  | succ k ih =>
    obtain ⟨M, hM0, hM⟩ := ih
    obtain ⟨M', hM'⟩ := hS.exists_bound_of_continuousOn
      (hDL.continuous_iteratedFDeriv (m := k + 1)
        (by exact_mod_cast natCast_le_infty (k + 1))).continuousOn
    refine ⟨max M (max M' 0), le_max_of_le_left hM0, fun j hj y hy ↦ ?_⟩
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact (hM j (Nat.lt_succ_iff.mp hlt) y hy).trans (le_max_left _ _)
    · have hj : j = k + 1 := le_antisymm hj hge
      subst hj
      exact (hM' y hy).trans ((le_max_left _ _).trans (le_max_right _ _))

/-- **Polynomial growth of all derivatives of a weight.** On a compact `S`, for
every `k` there is `C` with `‖D^j e^{-tL}(y)‖ ≤ C t^j` for all `j ≤ k`,
`t ≥ 1`, `y ∈ S`. -/
theorem exists_iteratedFDeriv_expWeight_bound_on {L : (ι → ℝ) → ℝ} (hL : ContDiff ℝ ∞ L)
    (hL0 : ∀ w, 0 ≤ L w) {S : Set (ι → ℝ)} (hS : IsCompact S) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ y ∈ S, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (fun w ↦ Real.exp (-(t * L w))) y‖ ≤ C * t ^ j := by
  have hDL : ContDiff ℝ ∞ (fderiv ℝ L) := (contDiff_infty_iff_fderiv.mp hL).2
  induction k with
  | zero =>
    refine ⟨1, zero_le_one, fun t ht y _ j hj ↦ ?_⟩
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero,
      mul_one]
    exact expWeight_le_one hL0 (zero_le_one.trans ht) y
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨M, hM0, hM⟩ := exists_iteratedFDeriv_fderiv_bound_on hL hS k
    set S₂ : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) with hS₂
    have hS₂0 : 0 ≤ S₂ := Finset.sum_nonneg fun i _ ↦ by positivity
    refine ⟨max C (S₂ * C * M), le_max_of_le_left hC0, fun t ht y hy j hj ↦ ?_⟩
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact (hC t ht y hy j (Nat.lt_succ_iff.mp hlt)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have hj : j = k + 1 := le_antisymm hj hge
      subst hj
      -- `D^{k+1} w = D^k (Dw)` in norm, and `Dw = w • g` with `g = -(t • DL)`
      rw [← norm_iteratedFDeriv_fderiv, fderiv_expWeight_eq hL t]
      have hf : ContDiff ℝ ∞ (fun w ↦ Real.exp (-(t * L w))) := contDiff_expWeight hL t
      have hg : ContDiff ℝ ∞ (fun y ↦ -(t • fderiv ℝ L y)) := by
        exact ((contDiff_const (c := t)).smul hDL).neg
      have hleib := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hf hg y (n := k)
        (by exact_mod_cast natCast_le_infty k)
      -- each factor
      have hgj : ∀ i ≤ k, ‖iteratedFDeriv ℝ (k - i) (fun y ↦ -(t • fderiv ℝ L y)) y‖ ≤
          t * M := by
        intro i _
        have h1 : (fun y ↦ -(t • fderiv ℝ L y)) = -(t • fderiv ℝ L) := by
          funext y
          simp
        rw [h1, iteratedFDeriv_neg_apply, norm_neg,
          iteratedFDeriv_const_smul_apply
            (hDL.contDiffAt.of_le (by exact_mod_cast natCast_le_infty (k - i))),
          norm_smul, Real.norm_eq_abs,
          abs_of_pos htpos]
        exact mul_le_mul_of_nonneg_left (hM (k - i) (Nat.sub_le _ _) y hy) htpos.le
      have hfi : ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun w ↦ Real.exp (-(t * L w))) y‖ ≤ C * t ^ k := by
        intro i hi
        calc ‖iteratedFDeriv ℝ i (fun w ↦ Real.exp (-(t * L w))) y‖ ≤ C * t ^ i :=
              hC t ht y hy i hi
          _ ≤ C * t ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hi) hC0
      calc ‖iteratedFDeriv ℝ k (fun y ↦ Real.exp (-(t * L y)) • (-(t • fderiv ℝ L y))) y‖
          ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun w ↦ Real.exp (-(t * L w))) y‖ *
              ‖iteratedFDeriv ℝ (k - i) (fun y ↦ -(t • fderiv ℝ L y)) y‖ := hleib
        _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (C * t ^ k) * (t * M) := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            gcongr
            · exact hfi i hi'
            · exact hgj i hi'
        _ = S₂ * C * M * t ^ (k + 1) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            ring
        _ ≤ max C (S₂ * C * M) * t ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The difference of two weights is smooth. -/
theorem contDiff_weightDiff {L₁ L₂ : (ι → ℝ) → ℝ} (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (t : ℝ) :
    ContDiff ℝ ∞ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) :=
  (contDiff_expWeight h2 t).sub (contDiff_expWeight h1 t)

/-- **Polynomial growth of all derivatives of the difference** on a compact. -/
theorem exists_iteratedFDeriv_weightDiff_bound_on {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w) {S : Set (ι → ℝ)} (hS : IsCompact S) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 1 ≤ t → ∀ y ∈ S,
      ‖iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) y‖ ≤
        B * t ^ k := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_iteratedFDeriv_expWeight_bound_on h1 hL1 hS k
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_iteratedFDeriv_expWeight_bound_on h2 hL2 hS k
  refine ⟨C₁ + C₂, by positivity, fun t ht y hy ↦ ?_⟩
  have hsub : (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) =
      (fun w ↦ Real.exp (-(t * L₂ w))) - fun w ↦ Real.exp (-(t * L₁ w)) := by
    funext w
    simp
  rw [hsub, iteratedFDeriv_sub_apply
    ((contDiff_expWeight h2 t).contDiffAt.of_le (by exact_mod_cast natCast_le_infty k))
    ((contDiff_expWeight h1 t).contDiffAt.of_le (by exact_mod_cast natCast_le_infty k))]
  calc ‖iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₂ w))) y -
        iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₁ w))) y‖
      ≤ ‖iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₂ w))) y‖ +
        ‖iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₁ w))) y‖ := norm_sub_le _ _
    _ ≤ C₂ * t ^ k + C₁ * t ^ k := add_le_add (hC₂ t ht y hy k le_rfl) (hC₁ t ht y hy k le_rfl)
    _ = (C₁ + C₂) * t ^ k := by ring

/-! ### Vector-valued interpolation -/

/-- **Interpolation from a Lipschitz derivative**, vector-valued. If `‖g‖ ≤ A` on
the closed ball of radius `s` about `x` and `‖Dg(y) - Dg(x)‖ ≤ M s` there, then
`‖Dg(x)‖ ≤ 2A/s + M s`. -/
theorem norm_fderiv_le_of_lipschitz_bounds {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : (ι → ℝ) → F} {x : ι → ℝ} {s A M : ℝ} (hs : 0 < s) (hA0 : 0 ≤ A) (hM0 : 0 ≤ M)
    (hd : ∀ y ∈ Metric.closedBall x s, DifferentiableAt ℝ g y)
    (hA : ∀ y ∈ Metric.closedBall x s, ‖g y‖ ≤ A)
    (hlip : ∀ y ∈ Metric.closedBall x s, ‖fderiv ℝ g y - fderiv ℝ g x‖ ≤ M * s) :
    ‖fderiv ℝ g x‖ ≤ 2 * A / s + M * s := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv ↦ ?_
  have hx : x ∈ Metric.closedBall x s := Metric.mem_closedBall_self hs.le
  have hy : x + s • v ∈ Metric.closedBall x s := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hv,
      Real.norm_of_nonneg hs.le, mul_one]
  have hT := (convex_closedBall x s).norm_image_sub_le_of_norm_fderiv_le' hd hlip hx hy
  rw [add_sub_cancel_left, map_smul, norm_smul, hv, Real.norm_of_nonneg hs.le, mul_one] at hT
  have hA1 := hA _ hy
  have hA2 := hA x hx
  have h4 : ‖s • fderiv ℝ g x v‖ ≤ ‖g (x + s • v) - g x‖ +
      ‖g (x + s • v) - g x - s • fderiv ℝ g x v‖ := by
    have := norm_sub_le (g (x + s • v) - g x) (g (x + s • v) - g x - s • fderiv ℝ g x v)
    rwa [sub_sub_cancel] at this
  have h5 := norm_sub_le (g (x + s • v)) (g x)
  rw [norm_smul, Real.norm_of_nonneg hs.le] at h4
  have hbound : s * ‖fderiv ℝ g x v‖ ≤ 2 * A + M * s * s := by linarith
  rw [div_add' _ _ _ hs.ne', le_div_iff₀ hs]
  nlinarith [hbound]

/-! ### All orders -/

/-- **Uniform agreement of all derivatives beyond all orders.** For smooth
nonnegative losses with exact smooth-test agreement, every order `k`, every
compact `K` and every `N`: there is `C` with
`‖D^k(e^{-tL₂} - e^{-tL₁})(x)‖ ≤ C t^{-N}` for all `x ∈ K`, eventually in `t`. -/
theorem eventually_uniform_norm_iteratedFDeriv_exp_sub_le {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    (k : ℕ) {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ᶠ t in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x‖ ≤
        C * t ^ (-(N : ℝ)) := by
  induction k generalizing K with
  | zero =>
    intro N
    obtain ⟨C, hC⟩ := eventually_uniform_abs_exp_sub_le h1 h2 hL1 hL2 hexact hK N
    refine ⟨C, hC.mono fun t ht x hx ↦ ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact ht x hx
  | succ k ih =>
    intro N
    set K' := Metric.cthickening 1 K with hK'_def
    have hK' : IsCompact K' := hK.cthickening
    obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_weightDiff_bound_on h1 h2 hL1 hL2 hK' (k + 2)
    obtain ⟨C₁, hC₁⟩ := ih hK' (2 * N + k + 3)
    set C₁' := max C₁ 0 with hC₁'_def
    have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
    refine ⟨2 * C₁' + B, ?_⟩
    filter_upwards [hC₁, eventually_ge_atTop (1 : ℝ)] with t hAt ht
    intro x hx
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht
    have htne : t ≠ 0 := htpos.ne'
    set h : (ι → ℝ) → ℝ := fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w)) with hh_def
    have hhs : ContDiff ℝ ∞ h := contDiff_weightDiff h1 h2 t
    have hball : Metric.closedBall x 1 ⊆ K' := fun y hy ↦
      Metric.mem_cthickening_of_dist_le y x 1 K hx (Metric.mem_closedBall.mp hy)
    set s : ℝ := (t ^ (N + k + 3))⁻¹ with hs_def
    have hs : 0 < s := by positivity
    have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht)
    have hsub : Metric.closedBall x s ⊆ Metric.closedBall x 1 :=
      Metric.closedBall_subset_closedBall hs1
    -- the currying isometry identifies `D (D^k h)` with `D^{k+1} h`
    set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ (ι → ℝ)) ℝ with he
    have hDg : ∀ y, fderiv ℝ (iteratedFDeriv ℝ k h) y = e (iteratedFDeriv ℝ (k + 1) h y) := by
      intro y
      have := congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ) (f := h) (n := k)) y
      rw [Function.comp_apply] at this
      rw [this, LinearIsometryEquiv.apply_symm_apply]
    -- amplitude bound from the induction hypothesis
    have hA : ∀ y ∈ Metric.closedBall x s, ‖iteratedFDeriv ℝ k h y‖ ≤
        C₁' * (t ^ (2 * N + k + 3))⁻¹ := by
      intro y hy
      have hconv : t ^ (-((2 * N + k + 3 : ℕ) : ℝ)) = (t ^ (2 * N + k + 3))⁻¹ := by
        rw [Real.rpow_neg htpos.le, Real.rpow_natCast]
      have := hAt y (hball (hsub hy))
      rw [hconv] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    -- Lipschitz bound for `D (D^k h)` from the mean value inequality on `D^{k+1} h`
    have hlip : ∀ y ∈ Metric.closedBall x s,
        ‖fderiv ℝ (iteratedFDeriv ℝ k h) y - fderiv ℝ (iteratedFDeriv ℝ k h) x‖ ≤
          B * t ^ (k + 2) * s := by
      intro y hy
      have hdiff : ∀ z ∈ Metric.closedBall x 1, DifferentiableAt ℝ (iteratedFDeriv ℝ (k + 1) h) z :=
        fun z _ ↦ (hhs.differentiable_iteratedFDeriv (m := k + 1)
          (by exact_mod_cast natCast_lt_infty (k + 1))) z
      have hbound : ∀ z ∈ Metric.closedBall x 1,
          ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) h) z‖ ≤ B * t ^ (k + 2) := by
        intro z hz
        rw [norm_fderiv_iteratedFDeriv]
        exact hB t ht z (hball hz)
      have hmv := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
        (Metric.mem_closedBall_self zero_le_one) (hsub hy)
      have hdist : ‖y - x‖ ≤ s := by
        have := Metric.mem_closedBall.mp hy
        rwa [dist_eq_norm] at this
      rw [hDg y, hDg x, ← map_sub, LinearIsometryEquiv.norm_map]
      exact hmv.trans (mul_le_mul_of_nonneg_left hdist (by positivity))
    have hd : ∀ y ∈ Metric.closedBall x s, DifferentiableAt ℝ (iteratedFDeriv ℝ k h) y :=
      fun y _ ↦ (hhs.differentiable_iteratedFDeriv (m := k)
        (by exact_mod_cast natCast_lt_infty k)) y
    have hinterp := norm_fderiv_le_of_lipschitz_bounds hs (by positivity) (by positivity) hd hA hlip
    rw [norm_fderiv_iteratedFDeriv] at hinterp
    -- exponent arithmetic
    have e1 : 2 * (C₁' * (t ^ (2 * N + k + 3))⁻¹) / s = 2 * C₁' * (t ^ N)⁻¹ := by
      rw [hs_def]
      field_simp
      ring
    have e2 : B * t ^ (k + 2) * s = B * (t ^ (N + 1))⁻¹ := by
      rw [hs_def]
      field_simp
      ring
    have e3 : (t ^ (N + 1))⁻¹ ≤ (t ^ N)⁻¹ :=
      inv_anti₀ (pow_pos htpos N) (pow_le_pow_right₀ ht (Nat.le_succ N))
    have hconv : t ^ (-(N : ℝ)) = (t ^ N)⁻¹ := by
      rw [Real.rpow_neg htpos.le, Real.rpow_natCast]
    calc ‖iteratedFDeriv ℝ (k + 1) h x‖
        ≤ 2 * (C₁' * (t ^ (2 * N + k + 3))⁻¹) / s + B * t ^ (k + 2) * s := hinterp
      _ = 2 * C₁' * (t ^ N)⁻¹ + B * (t ^ (N + 1))⁻¹ := by rw [e1, e2]
      _ ≤ 2 * C₁' * (t ^ N)⁻¹ + B * (t ^ N)⁻¹ := by gcongr
      _ = (2 * C₁' + B) * (t ^ N)⁻¹ := by ring
      _ = (2 * C₁' + B) * t ^ (-(N : ℝ)) := by rw [hconv]

/-- **Pointwise agreement of all derivatives beyond all orders.** -/
theorem superPoly_iteratedFDeriv_exp_sub_at {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    (k : ℕ) (x : ι → ℝ) (v : Fin k → (ι → ℝ)) :
    SuperPoly fun t ↦
      iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x v := by
  refine superPoly_of_forall_eventually_le fun N ↦ ?_
  obtain ⟨C, hC⟩ := eventually_uniform_norm_iteratedFDeriv_exp_sub_le h1 h2 hL1 hL2 hexact k
    (isCompact_singleton (x := x)) N
  refine ⟨C * ∏ i, ‖v i‖, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  have hx := ht x (Set.mem_singleton x)
  have hprod : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg fun i _ ↦ norm_nonneg _
  calc |iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x v|
      = ‖iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x v‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ k (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x‖ *
        ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C * t ^ (-(N : ℝ)) * ∏ i, ‖v i‖ := mul_le_mul_of_nonneg_right hx hprod
    _ = C * (∏ i, ‖v i‖) * t ^ (-(N : ℝ)) := by ring

end Laplace
