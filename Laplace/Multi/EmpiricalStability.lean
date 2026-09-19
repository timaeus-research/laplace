/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TotalVariation

/-!
# Stability of Laplace moments under a uniform perturbation of the loss

A first foothold for the empirical direction of the germbij note. If two
losses are uniformly `δ`-close on the support of an observable, their
Laplace moments at temperature `t` differ by at most `t δ ‖φ‖₁`
(`abs_integral_sub_le_of_uniform_close`), and the normalized expectations
differ by `O(t δ)` as well once the partition values are bounded below
(`abs_normalized_sub_le_of_uniform_close`). The pointwise input is the `1`-Lipschitz bound
`|e^{-x} - e^{-y}| ≤ |x - y|` on the nonnegative half-line
(`abs_exp_neg_sub_exp_neg_le`).

Read with `K = K_n` the empirical loss and `L` the population loss, with
`sup |K_n - L| = δ_n` on a compact: the empirical moments at temperature
`t` track the population ones to `O(t δ_n)`, so the `t → ∞` expansions of
the two families can only be compared for `t ≪ 1/δ_n`. The two limits do
not commute; this is the precise form of the note's remark that finitely
many orders of the empirical expansions determine the population data only
to the accuracy of the empirical fluctuation.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **Moment stability.** For nonnegative losses `K, L` with `|K - L| ≤ δ` on
the support of a continuous compactly supported `φ`, and `t ≥ 0`:
`|∫ φ e^{-tK} - ∫ φ e^{-tL}| ≤ t δ ∫ |φ|`. -/
theorem abs_integral_sub_le_of_uniform_close {K L φ : (ι → ℝ) → ℝ}
    (hKc : Continuous K) (hLc : Continuous L)
    (hK : ∀ w, 0 ≤ K w) (hL : ∀ w, 0 ≤ L w)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {δ : ℝ} (hclose : ∀ w ∈ tsupport φ, |K w - L w| ≤ δ) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ w, φ w * Real.exp (-(t * K w))) - ∫ w, φ w * Real.exp (-(t * L w))| ≤
      t * δ * ∫ w, |φ w| := by
  have hint1 := integrable_mul_exp_neg_of_compactSupport hφc hφs hKc t
  have hint2 := integrable_mul_exp_neg_of_compactSupport hφc hφs hLc t
  have hintabs : Integrable fun w ↦ |φ w| := hφc.abs.integrable_of_hasCompactSupport hφs.abs
  rw [← integral_sub hint1 hint2]
  calc |∫ w, φ w * Real.exp (-(t * K w)) - φ w * Real.exp (-(t * L w))|
      ≤ ∫ w, |φ w * Real.exp (-(t * K w)) - φ w * Real.exp (-(t * L w))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, t * δ * |φ w| := by
        refine integral_mono (hint1.sub hint2).abs (hintabs.const_mul _) fun w ↦ ?_
        by_cases hw : w ∈ tsupport φ
        · rw [← mul_sub, abs_mul]
          have hlip := abs_exp_neg_sub_exp_neg_le (mul_nonneg ht (hK w)) (mul_nonneg ht (hL w))
          have h2 : |t * K w - t * L w| = t * |K w - L w| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg ht]
          rw [h2] at hlip
          calc |φ w| * |Real.exp (-(t * K w)) - Real.exp (-(t * L w))|
              ≤ |φ w| * (t * |K w - L w|) :=
                mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
            _ ≤ |φ w| * (t * δ) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hclose w hw) ht) (abs_nonneg _)
            _ = t * δ * |φ w| := by ring
        · rw [image_eq_zero_of_notMem_tsupport hw]
          simp
    _ = t * δ * ∫ w, |φ w| := integral_const_mul _ _

/-- **Normalized stability.** With a common window `χ` and both partition
values at least `z > 0`, the normalized expectations differ by
`t δ ‖φ‖₁ (1 + ‖χ‖₁/z) / z`. -/
theorem abs_normalized_sub_le_of_uniform_close {K L φ χ : (ι → ℝ) → ℝ}
    (hKc : Continuous K) (hLc : Continuous L)
    (hK : ∀ w, 0 ≤ K w) (hL : ∀ w, 0 ≤ L w)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {δ : ℝ} (hcloseφ : ∀ w ∈ tsupport φ, |K w - L w| ≤ δ)
    (hcloseχ : ∀ w ∈ tsupport χ, |K w - L w| ≤ δ) {t : ℝ} (ht : 0 ≤ t)
    {z : ℝ} (hz : 0 < z)
    (hZK : z ≤ ∫ w, χ w * Real.exp (-(t * K w)))
    (hZL : z ≤ ∫ w, χ w * Real.exp (-(t * L w))) :
    |(∫ w, φ w * Real.exp (-(t * K w))) / (∫ w, χ w * Real.exp (-(t * K w))) -
      (∫ w, φ w * Real.exp (-(t * L w))) / (∫ w, χ w * Real.exp (-(t * L w)))| ≤
        t * δ * (∫ w, |φ w|) * (1 + (∫ w, |χ w|) / z) / z := by
  set IK := ∫ w, φ w * Real.exp (-(t * K w)) with hIK
  set IL := ∫ w, φ w * Real.exp (-(t * L w)) with hIL
  set ZK := ∫ w, χ w * Real.exp (-(t * K w)) with hZK'
  set ZL := ∫ w, χ w * Real.exp (-(t * L w)) with hZL'
  have hZKpos : 0 < ZK := lt_of_lt_of_le hz hZK
  have hZLpos : 0 < ZL := lt_of_lt_of_le hz hZL
  have hI := abs_integral_sub_le_of_uniform_close hKc hLc hK hL hφc hφs hcloseφ ht
  have hZ := abs_integral_sub_le_of_uniform_close hKc hLc hK hL hχc hχs hcloseχ ht
  -- `|I_L| ≤ ∫ |φ|` for `t ≥ 0`
  have hILle : |IL| ≤ ∫ w, |φ w| := by
    have := isBigO_iff.mp (laplace_moment_bounded hφc hφs hLc hL)
    -- use the pointwise bound directly instead
    calc |IL| ≤ ∫ w, |φ w * Real.exp (-(t * L w))| := abs_integral_le_integral_abs
      _ ≤ ∫ w, |φ w| := by
          refine integral_mono (integrable_mul_exp_neg_of_compactSupport hφc hφs hLc t).abs
            (hφc.abs.integrable_of_hasCompactSupport hφs.abs) fun w ↦ ?_
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have : Real.exp (-(t * L w)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            exact neg_nonpos.mpr (mul_nonneg ht (hL w))
          calc |φ w| * Real.exp (-(t * L w)) ≤ |φ w| * 1 :=
                mul_le_mul_of_nonneg_left this (abs_nonneg _)
            _ = |φ w| := mul_one _
  have hφnn : 0 ≤ ∫ w, |φ w| := integral_nonneg fun w ↦ abs_nonneg _
  have hχnn : 0 ≤ ∫ w, |χ w| := integral_nonneg fun w ↦ abs_nonneg _
  have htδ : 0 ≤ t * δ := by
    rcases (tsupport φ).eq_empty_or_nonempty with hφe | ⟨w, hw⟩
    · -- `φ = 0`: both sides of the target vanish; but we still need this sign fact,
      -- so fall back to the window
      rcases (tsupport χ).eq_empty_or_nonempty with hχe | ⟨w, hw⟩
      · -- both empty: `ZK = 0 < z ≤ ZK` is impossible
        exfalso
        have hχ0 : ∀ w, χ w = 0 := fun w ↦
          image_eq_zero_of_notMem_tsupport (by rw [hχe]; exact Set.notMem_empty w)
        have : ZK = 0 := by simp [hZK', hχ0]
        linarith
      · exact mul_nonneg ht ((abs_nonneg _).trans (hcloseχ w hw))
    · exact mul_nonneg ht ((abs_nonneg _).trans (hcloseφ w hw))
  -- the identity
  have hid : IK / ZK - IL / ZL = (IK - IL) / ZK + IL * (ZL - ZK) / (ZK * ZL) := by
    field_simp
    ring
  rw [hid]
  have hZinv : ZK⁻¹ ≤ z⁻¹ := inv_anti₀ hz hZK
  have hZLinv : ZL⁻¹ ≤ z⁻¹ := inv_anti₀ hz hZL
  calc |(IK - IL) / ZK + IL * (ZL - ZK) / (ZK * ZL)|
      ≤ |(IK - IL) / ZK| + |IL * (ZL - ZK) / (ZK * ZL)| := abs_add_le _ _
    _ = |IK - IL| * ZK⁻¹ + |IL| * |ZL - ZK| * (ZK⁻¹ * ZL⁻¹) := by
        rw [abs_div, abs_of_pos hZKpos, abs_div, abs_mul, abs_of_pos (mul_pos hZKpos hZLpos),
          div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    _ ≤ (t * δ * ∫ w, |φ w|) * z⁻¹ +
        (∫ w, |φ w|) * (t * δ * ∫ w, |χ w|) * (z⁻¹ * z⁻¹) := by
        gcongr
        rw [abs_sub_comm]
        exact hZ
    _ = t * δ * (∫ w, |φ w|) * (1 + (∫ w, |χ w|) / z) / z := by
        field_simp

end Laplace
