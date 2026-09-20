/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AbelianTransferLog

/-!
# Instances of the Abelian transfer

Concrete singular losses whose sublevel volumes are elementary, fed through
the transfer theorems of `AbelianTransfer` and `AbelianTransferLog`.

* `sublevelMass_pow_even`: for `K(x) = x^{2k}` on `[-1, 1]` the sublevel mass
  is exactly `2 ε^{1/(2k)}` for `0 < ε ≤ 1`.
* `boltzmannMass_pow_even_transfer`: hence `∫_{-1}^{1} e^{-t x^{2k}} dx =
  Θ(t^{-1/(2k)})`, the real log canonical threshold `λ = 1/(2k)` with
  multiplicity one, with no resolution of singularities and no Gamma
  function.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Laplace

/-- The unit interval carries a finite measure. -/
instance : IsFiniteMeasure (volume.restrict (Icc (-1 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne

/-- **Sublevel mass of an even power on `[-1, 1]`**: `μ{x^{2k} ≤ ε} = 2 ε^{1/(2k)}`
for `0 < ε ≤ 1`. -/
theorem sublevelMass_pow_even {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    sublevelMass (volume.restrict (Icc (-1 : ℝ) 1)) (fun x ↦ x ^ (2 * k)) ε =
      2 * ε ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
  set a : ℝ := ε ^ (((2 * k : ℕ) : ℝ)⁻¹) with ha_def
  have hn : 2 * k ≠ 0 := by omega
  have ha0 : 0 < a := Real.rpow_pos_of_pos hε _
  have ha1 : a ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
  have hapow : a ^ (2 * k) = ε := Real.rpow_inv_natCast_pow hε.le hn
  have hset : {x : ℝ | x ^ (2 * k) ≤ ε} = Icc (-a) a := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc]
    rw [← abs_le, ← hapow, ← Even.pow_abs (even_two_mul k),
      pow_le_pow_iff_left₀ (abs_nonneg x) ha0.le hn]
  unfold sublevelMass
  rw [measureReal_restrict_apply (measurableSet_le (by fun_prop) measurable_const), hset,
    inter_eq_left.mpr (Icc_subset_Icc (by linarith) ha1), Real.volume_real_Icc_of_le (by linarith)]
  ring

/-- **The even-power instance**: `∫_{-1}^{1} e^{-t x^{2k}} dx = Θ(t^{-1/(2k)})`. -/
theorem boltzmannMass_pow_even_transfer {k : ℕ} (hk : 0 < k) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      C₁ * t ^ (-(((2 * k : ℕ) : ℝ)⁻¹)) ≤
          boltzmannMass (volume.restrict (Icc (-1 : ℝ) 1)) (fun x ↦ x ^ (2 * k)) t ∧
      boltzmannMass (volume.restrict (Icc (-1 : ℝ) 1)) (fun x ↦ x ^ (2 * k)) t ≤
          C₂ * t ^ (-(((2 * k : ℕ) : ℝ)⁻¹)) := by
  have hlam : (0 : ℝ) < ((2 * k : ℕ) : ℝ)⁻¹ := by positivity
  refine boltzmannMass_power_transfer _ _ (by fun_prop)
    (fun x ↦ Even.pow_nonneg (even_two_mul k) x) hlam one_pos two_pos two_pos
    (fun ε hε hε1 ↦ ?_) (fun ε hε hε1 ↦ ?_)
  · rw [sublevelMass_pow_even hk hε hε1]
  · rw [sublevelMass_pow_even hk hε hε1]

end Laplace
