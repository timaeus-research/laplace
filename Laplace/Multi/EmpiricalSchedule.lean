/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.EmpiricalStability

/-!
# Temperature schedules for empirical Laplace expansions

`EmpiricalStability` bounds the gap between the normalized expectations of an
empirical loss `K_n` and of the population loss `L` at temperature `t` by
`t δ_n ‖φ‖₁ (1 + ‖χ‖₁/z)/z`, where `δ_n = sup |K_n - L|` on the supports and
`z` is a common lower bound for the two partition values. The coefficients of
the `t → ∞` expansion of `⟨φ⟩_t` in powers of `q = t^{-1/2}` are read off from
the rescaled quantities `t^{k/2} ⟨φ⟩_t`; along a sample-size-dependent
schedule `t = t_n` the empirical rescaled quantity tracks the population one
iff the rescaled gap tends to zero. This file records the two forms of that
statement.

* `abs_rpow_mul_normalized_sub_le`: the rescaled gap bound at one temperature.
* `tendsto_rpow_mul_normalized_sub_of_schedule`: the abstract schedule
  criterion — `t_n^r · (gap bound) → 0` forces `t_n^r (⟨φ⟩^{K_n}_{t_n} -
  ⟨φ⟩^{L}_{t_n}) → 0`.
* `tendsto_rpow_mul_normalized_sub_of_polynomial_partition`: with the
  partition values bounded below by `κ t^{-λ}` (the Laplace decay rate of the
  window), the criterion reads `δ_n · t_n^{r + 1 + 2λ} → 0`.

With `r = k/2` the population coefficient of order `q^k` is consistently
tracked by the empirical expansion along any schedule with
`t_n ≪ δ_n^{-1/(k/2 + 1 + 2λ)}`; for `δ_n ∼ n^{-1/2}` this is
`t_n ≪ n^{1/(k + 2 + 4λ)}`. Higher orders need slower schedules, and the two
limits `n → ∞`, `t → ∞` do not commute: this is the quantitative form of the
germbij note's remark that finitely many empirical orders determine the
population data only to the accuracy of the empirical fluctuation.
-/

open Asymptotics Filter MeasureTheory
open scoped Topology

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- The rescaled gap bound at one temperature. -/
theorem abs_rpow_mul_normalized_sub_le {K L φ χ : (ι → ℝ) → ℝ}
    (hKc : Continuous K) (hLc : Continuous L)
    (hK : ∀ w, 0 ≤ K w) (hL : ∀ w, 0 ≤ L w)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {δ : ℝ} (hcloseφ : ∀ w ∈ tsupport φ, |K w - L w| ≤ δ)
    (hcloseχ : ∀ w ∈ tsupport χ, |K w - L w| ≤ δ) {t : ℝ} (ht : 0 ≤ t)
    {z : ℝ} (hz : 0 < z)
    (hZK : z ≤ ∫ w, χ w * Real.exp (-(t * K w)))
    (hZL : z ≤ ∫ w, χ w * Real.exp (-(t * L w))) (r : ℝ) :
    |t ^ r * ((∫ w, φ w * Real.exp (-(t * K w))) / (∫ w, χ w * Real.exp (-(t * K w))) -
      (∫ w, φ w * Real.exp (-(t * L w))) / (∫ w, χ w * Real.exp (-(t * L w))))| ≤
        (∫ w, |φ w|) * (t ^ r * (t * δ * (1 + (∫ w, |χ w|) / z) / z)) := by
  have h := abs_normalized_sub_le_of_uniform_close hKc hLc hK hL hφc hφs hχc hχs hcloseφ
    hcloseχ ht hz hZK hZL
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht r)]
  calc t ^ r * |_| ≤ t ^ r * (t * δ * (∫ w, |φ w|) * (1 + (∫ w, |χ w|) / z) / z) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ht r)
    _ = (∫ w, |φ w|) * (t ^ r * (t * δ * (1 + (∫ w, |χ w|) / z) / z)) := by ring

/-- **Abstract schedule criterion.** Along a schedule `t_n` with uniform
closeness `δ_n` and partition lower bounds `z_n`, if the rescaled gap bound
`t_n^r · t_n δ_n (1 + ‖χ‖₁/z_n)/z_n` tends to zero then so does the rescaled
difference of normalized expectations. -/
theorem tendsto_rpow_mul_normalized_sub_of_schedule {K : ℕ → (ι → ℝ) → ℝ}
    {L φ χ : (ι → ℝ) → ℝ}
    (hKc : ∀ n, Continuous (K n)) (hLc : Continuous L)
    (hK : ∀ n w, 0 ≤ K n w) (hL : ∀ w, 0 ≤ L w)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {δ t z : ℕ → ℝ}
    (hcloseφ : ∀ n, ∀ w ∈ tsupport φ, |K n w - L w| ≤ δ n)
    (hcloseχ : ∀ n, ∀ w ∈ tsupport χ, |K n w - L w| ≤ δ n)
    (ht : ∀ n, 0 ≤ t n) (hz : ∀ n, 0 < z n)
    (hZK : ∀ n, z n ≤ ∫ w, χ w * Real.exp (-(t n * K n w)))
    (hZL : ∀ n, z n ≤ ∫ w, χ w * Real.exp (-(t n * L w))) (r : ℝ)
    (hsched : Tendsto (fun n ↦ t n ^ r * (t n * δ n * (1 + (∫ w, |χ w|) / z n) / z n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ t n ^ r *
      ((∫ w, φ w * Real.exp (-(t n * K n w))) / (∫ w, χ w * Real.exp (-(t n * K n w))) -
        (∫ w, φ w * Real.exp (-(t n * L w))) / (∫ w, χ w * Real.exp (-(t n * L w)))))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun n ↦
    (∫ w, |φ w|) * (t n ^ r * (t n * δ n * (1 + (∫ w, |χ w|) / z n) / z n))) (fun n ↦ ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_rpow_mul_normalized_sub_le (hKc n) hLc (hK n) hL hφc hφs hχc hχs (hcloseφ n)
      (hcloseχ n) (ht n) (hz n) (hZK n) (hZL n) r
  · simpa using hsched.const_mul (∫ w, |φ w|)

/-- **Polynomial partition decay.** If the partition values are bounded below
by `κ t^{-λ}` with `κ > 0`, `λ ≥ 0`, and `t_n ≥ 1`, the schedule criterion is
`δ_n · t_n^{r + 1 + 2λ} → 0`. -/
theorem tendsto_rpow_mul_normalized_sub_of_polynomial_partition {K : ℕ → (ι → ℝ) → ℝ}
    {L φ χ : (ι → ℝ) → ℝ}
    (hKc : ∀ n, Continuous (K n)) (hLc : Continuous L)
    (hK : ∀ n w, 0 ≤ K n w) (hL : ∀ w, 0 ≤ L w)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {δ t : ℕ → ℝ} {κ lam : ℝ} (hκ : 0 < κ) (hlam : 0 ≤ lam)
    (hcloseφ : ∀ n, ∀ w ∈ tsupport φ, |K n w - L w| ≤ δ n)
    (hcloseχ : ∀ n, ∀ w ∈ tsupport χ, |K n w - L w| ≤ δ n)
    (hδ : ∀ n, 0 ≤ δ n) (ht : ∀ n, 1 ≤ t n)
    (hZK : ∀ n, κ * t n ^ (-lam) ≤ ∫ w, χ w * Real.exp (-(t n * K n w)))
    (hZL : ∀ n, κ * t n ^ (-lam) ≤ ∫ w, χ w * Real.exp (-(t n * L w))) (r : ℝ)
    (hsched : Tendsto (fun n ↦ δ n * t n ^ (r + 1 + 2 * lam)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ t n ^ r *
      ((∫ w, φ w * Real.exp (-(t n * K n w))) / (∫ w, χ w * Real.exp (-(t n * K n w))) -
        (∫ w, φ w * Real.exp (-(t n * L w))) / (∫ w, χ w * Real.exp (-(t n * L w)))))
      atTop (𝓝 0) := by
  set M : ℝ := ∫ w, |χ w| with hM_def
  have hM : 0 ≤ M := integral_nonneg fun w ↦ abs_nonneg _
  have hz : ∀ n, 0 < κ * t n ^ (-lam) := fun n ↦
    mul_pos hκ (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (ht n)) _)
  refine squeeze_zero_norm (a := fun n ↦
    (∫ w, |φ w|) * ((1 + M / κ) / κ) * (δ n * t n ^ (r + 1 + 2 * lam))) (fun n ↦ ?_) ?_
  · rw [Real.norm_eq_abs]
    refine (abs_rpow_mul_normalized_sub_le (hKc n) hLc (hK n) hL hφc hφs hχc hχs (hcloseφ n)
      (hcloseχ n) (zero_le_one.trans (ht n)) (hz n) (hZK n) (hZL n) r).trans ?_
    have htpos : 0 < t n := lt_of_lt_of_le one_pos (ht n)
    set u : ℝ := t n ^ lam with hu_def
    have hu1 : 1 ≤ u := Real.one_le_rpow (ht n) hlam
    have hupos : 0 < u := lt_of_lt_of_le one_pos hu1
    have hneg : t n ^ (-lam) = u⁻¹ := Real.rpow_neg htpos.le lam
    have hpow : t n ^ (r + 1 + 2 * lam) = t n ^ r * t n * (u * u) := by
      rw [show r + 1 + 2 * lam = r + 1 + lam + lam by ring, Real.rpow_add htpos,
        Real.rpow_add htpos, Real.rpow_add htpos, Real.rpow_one]
      ring
    have hA : 0 ≤ ∫ w, |φ w| := integral_nonneg fun w ↦ abs_nonneg _
    have htr : 0 ≤ t n ^ r := Real.rpow_nonneg htpos.le r
    -- the key comparison `1 + M u/κ ≤ (1 + M/κ) u`
    have hkey : 1 + M * u / κ ≤ (1 + M / κ) * u := by
      have : (1 + M / κ) * u - (1 + M * u / κ) = u - 1 := by ring
      linarith
    rw [hneg, hpow]
    have hlhs : (∫ w, |φ w|) * (t n ^ r * (t n * δ n * (1 + M / (κ * u⁻¹)) / (κ * u⁻¹)))
        = ((∫ w, |φ w|) * t n ^ r * t n * δ n * u / κ) * (1 + M * u / κ) := by
      field_simp
    have hrhs : (∫ w, |φ w|) * ((1 + M / κ) / κ) * (δ n * (t n ^ r * t n * (u * u)))
        = ((∫ w, |φ w|) * t n ^ r * t n * δ n * u / κ) * ((1 + M / κ) * u) := by
      field_simp
    rw [hlhs, hrhs]
    refine mul_le_mul_of_nonneg_left hkey ?_
    have : 0 ≤ (∫ w, |φ w|) * t n ^ r * t n * δ n * u :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA htr) htpos.le) (hδ n)) hupos.le
    exact div_nonneg this hκ.le
  · simpa using hsched.const_mul ((∫ w, |φ w|) * ((1 + M / κ) / κ))

end Laplace
