/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BurnInAverage

/-!
# The lag weight in closed form and the long-run variance (E4/E5)

Tide 111's lag weight `F_n(z) = (n + 2∑_{j<n}(n−(j+1))z^{j+1})/n²` governs the variance of the
average of `n` consecutive
post-burn-in draws. Here:
* `∑_{j<n}(n−(j+1))z^{j+1} = nz/(1−z) − z(1−z^n)/(1−z)²` and **`F_n(z) = (1+z)/(n(1−z)) −
2z(1−z^n)/(n²(1−z)²)`**
  (`sum_range_sub_succ_mul_pow`, `lagWeight_eq`): the integrated-autocorrelation bound of tide 111
  is the first term;
* **`n·F_n(z) → (1+z)/(1−z)`** (`lagWeight_mul_tendsto`), the integrated autocorrelation time, with
the exact deficit
  `2z(1−z^n)/(n(1−z)²) ≥ 0` (`lagWeight_mul_le`): the fixed-`n` average never beats the long-run
  rate;
* **`n·W_{η,n} → L_η`** (`Leta_eq_lagWeight_limit`, `avgLimit_mul_tendsto_Leta`,
`avgLimit_mul_le_Leta`): the limiting scaled variance
  `W_{η,n} = ½∑ᵢ(1−ηλᵢ/2)⁻²F_n((1−ηλᵢ)²)` of the `n`-draw average, multiplied by `n`, increases to
  tide 103's stationary long-run
  variance `L_η = ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)`. This is an `n → ∞` statement about the limiting
  coefficients, not a simultaneous
  `n(t)` limit.
-/

open Filter Topology

namespace Laplace.Multi

/-- The lag sum in closed form, `z ≠ 1`. -/
theorem sum_range_sub_succ_mul_pow {z : ℝ} (hz : z ≠ 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z ^ (j + 1) =
      n * z / (1 - z) - z * (1 - z ^ n) / (1 - z) ^ 2 := by
  have h1z : (1 : ℝ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have e : ∑ j ∈ Finset.range n, (((n + 1 : ℕ) : ℝ) - (j + 1)) * z ^ (j + 1) =
        ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z ^ (j + 1) +
          ∑ j ∈ Finset.range n, z ^ (j + 1) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    have hg : ∑ j ∈ Finset.range n, z ^ (j + 1) = z * (1 - z ^ n) / (1 - z) := by
      have hgeom := geom_sum_eq hz n
      rw [← neg_sub (1 : ℝ) (z ^ n), ← neg_sub (1 : ℝ) z, neg_div_neg_eq] at hgeom
      rw [mul_div_assoc, ← hgeom, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, ih, hg]
    push_cast
    field_simp
    ring

/-- **The exact lag weight**: `F_n(z) = (1+z)/(n(1−z)) − 2z(1−z^n)/(n²(1−z)²)` for `n ≥ 1`, `z ≠
1`. -/
theorem lagWeight_eq {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : z ≠ 1) :
    lagWeight n z = (1 + z) / (n * (1 - z)) - 2 * z * (1 - z ^ n) / (n ^ 2 * (1 - z) ^ 2) := by
  unfold lagWeight
  rw [sum_range_sub_succ_mul_pow hz n]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  have h1z : (1 : ℝ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  field_simp
  ring

/-- `n·F_n(z) = (1+z)/(1−z) − 2z(1−z^n)/(n(1−z)²)`. -/
theorem mul_lagWeight_eq {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : z ≠ 1) :
    (n : ℝ) * lagWeight n z = (1 + z) / (1 - z) - 2 * z * (1 - z ^ n) / (n * (1 - z) ^ 2) := by
  rw [lagWeight_eq hn hz]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  have h1z : (1 : ℝ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  field_simp

/-- `n·F_n(z) ≤ (1+z)/(1−z)` for `0 ≤ z < 1`: the fixed-`n` average never beats the long-run rate.
-/
theorem lagWeight_mul_le {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (n : ℝ) * lagWeight n z ≤ (1 + z) / (1 - z) := by
  rw [mul_lagWeight_eq hn (ne_of_lt hz1)]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hzn : z ^ n ≤ 1 := pow_le_one₀ hz0 hz1.le
  have : 0 ≤ 2 * z * (1 - z ^ n) / (n * (1 - z) ^ 2) :=
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  linarith

/-- The exact deficit `(1+z)/(1−z) − n·F_n(z) = 2z(1−z^n)/(n(1−z)²)` is at most `2z/(n(1−z)²)`. -/
theorem lagWeight_mul_deficit_le {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (1 + z) / (1 - z) - (n : ℝ) * lagWeight n z ≤ 2 * z / (n * (1 - z) ^ 2) := by
  rw [mul_lagWeight_eq hn (ne_of_lt hz1), sub_sub_cancel]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1z : 0 < 1 - z := sub_pos.2 hz1
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_of_le_one_right (by positivity) (by linarith [pow_nonneg hz0 n])

/-- Bernoulli: `z^n(1 + n(1−z)) ≤ 1` for `0 ≤ z ≤ 1`. -/
theorem pow_mul_one_add_le_one {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    z ^ n * (1 + n * (1 - z)) ≤ 1 := by
  have hw : (-2 : ℝ) ≤ 1 - z := by linarith
  calc z ^ n * (1 + n * (1 - z)) ≤ z ^ n * (1 + (1 - z)) ^ n :=
        mul_le_mul_of_nonneg_left (one_add_mul_le_pow hw n) (pow_nonneg hz0 n)
    _ = (z * (1 + (1 - z))) ^ n := by rw [mul_pow]
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

/-- `n ↦ n·F_n(z)` is nondecreasing: `n·W_{η,n}` increases to the long-run variance. -/
theorem mul_lagWeight_succ_le {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (n : ℝ) * lagWeight n z ≤ ((n + 1 : ℕ) : ℝ) * lagWeight (n + 1) z := by
  rw [mul_lagWeight_eq hn (ne_of_lt hz1), mul_lagWeight_eq (by omega) (ne_of_lt hz1)]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1z : 0 < 1 - z := sub_pos.2 hz1
  have key := pow_mul_one_add_le_one hz0 hz1.le n
  have hkey' : (n : ℝ) * (1 - z ^ n * z) ≤ (n + 1) * (1 - z ^ n) := by nlinarith [key]
  have hc : (0 : ℝ) ≤ 2 * z * (1 - z) ^ 2 := by positivity
  push_cast
  rw [sub_le_sub_iff_left, div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by
      positivity),
    pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left hkey' hc]

/-- **`n·F_n(z) → (1+z)/(1−z)`**: the lag weight recovers the integrated autocorrelation time. -/
theorem lagWeight_mul_tendsto {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * lagWeight n z) atTop (𝓝 ((1 + z) / (1 - z))) := by
  have hzn : Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hz0 hz1
  have hnum : Tendsto (fun n : ℕ => 2 * z * (1 - z ^ n) / (1 - z) ^ 2) atTop
      (𝓝 (2 * z * (1 - 0) / (1 - z) ^ 2)) :=
    ((tendsto_const_nhds (x := 2 * z)).mul (tendsto_const_nhds.sub hzn)).div_const _
  have hlim : Tendsto (fun n : ℕ => (1 + z) / (1 - z) - 2 * z * (1 - z ^ n) / (1 - z) ^ 2 / n) atTop
      (𝓝 ((1 + z) / (1 - z) - 0)) :=
    tendsto_const_nhds.sub (hnum.div_atTop tendsto_natCast_atTop_atTop)
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  have h1z : (1 : ℝ) - z ≠ 0 := (sub_pos.2 hz1).ne'
  rw [mul_lagWeight_eq hn (ne_of_lt hz1)]
  field_simp

section Spectrum

variable {d : ℕ} {lam : Fin d → ℝ} {η : ℝ}

theorem alpha_sq_lt_one (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) (i : Fin d)
    :
    (1 - η * lam i) ^ 2 < 1 := by
  have hx := mul_pos hη (hlam i)
  nlinarith [mul_pos hx (by linarith [hηl i] : (0 : ℝ) < 2 - η * lam i)]

/-- The long-run variance in lag-weight form: `½∑ᵢaᵢ⁻²(1+αᵢ²)/(1−αᵢ²) = L_η` (`1 − αᵢ² = 2ηλᵢaᵢ`).
-/
theorem Leta_eq_lagWeight_limit (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) :
    1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * ((1 + (1 - η * lam i) ^ 2) / (1 - (1 - η * lam i)
        ^ 2)) = ∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx := (mul_pos hη (hlam i)).ne'
  have hk : 1 - η * lam i / 2 ≠ 0 := by linarith [hηl i]
  have hk2 : 2 - η * lam i ≠ 0 := by linarith [hηl i]
  have e : 1 - (1 - η * lam i) ^ 2 = η * lam i * (2 - η * lam i) := by ring
  rw [e]
  field_simp
  ring

/-- **The `n`-draw average recovers the long-run variance**: `n·W_{η,n} → L_η`. -/
theorem avgLimit_mul_tendsto_Leta (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * lagWeight n ((1 -
        η * lam i) ^ 2))) atTop
      (𝓝 (∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3))) := by
  rw [← Leta_eq_lagWeight_limit hlam hη hηl]
  have h : Tendsto (fun n : ℕ => 1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * ((n : ℝ) * lagWeight
      n ((1 - η * lam i) ^ 2))) atTop
      (𝓝 (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * ((1 + (1 - η * lam i) ^ 2) / (1 - (1 - η *
          lam i) ^ 2)))) :=
    (tendsto_finsetSum Finset.univ fun i _ => tendsto_const_nhds.mul
      (lagWeight_mul_tendsto (sq_nonneg _) (alpha_sq_lt_one hlam hη hηl i))).const_mul (1 / 2)
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `L_η − n·W_{η,n} ≤ D_η/n` with `D_η = ∑ᵢaᵢ⁻²αᵢ²/(1−αᵢ²)²`: the fixed-window variance is `L_η/n
+ O(n⁻²)`. -/
theorem Leta_sub_avgLimit_mul_le (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {n
    : ℕ}
    (hn : 1 ≤ n) :
    ∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) - (n : ℝ) * (1 / 2 *
        ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * lagWeight n ((1 - η * lam i) ^ 2)) ≤
      (1 / (n : ℝ)) * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * ((1 - η * lam i) ^ 2 / (1 - (1 - η * lam
          i) ^ 2) ^ 2) := by
  rw [← Leta_eq_lagWeight_limit hlam hη hηl]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hW : 0 ≤ (1 / (1 - η * lam i / 2)) ^ 2 := sq_nonneg _
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hz1 := alpha_sq_lt_one hlam hη hηl i
  have hdef := lagWeight_mul_deficit_le hn (sq_nonneg (1 - η * lam i)) hz1
  have h1z : 0 < 1 - (1 - η * lam i) ^ 2 := by linarith
  calc 1 / 2 * ((1 / (1 - η * lam i / 2)) ^ 2 * ((1 + (1 - η * lam i) ^ 2) / (1 - (1 - η * lam i) ^
      2))) - (n : ℝ) * (1 / 2 * ((1 / (1 - η * lam i / 2)) ^ 2 * lagWeight n ((1 - η * lam i) ^ 2)))
      = 1 / 2 * ((1 / (1 - η * lam i / 2)) ^ 2 * (((1 + (1 - η * lam i) ^ 2) / (1 - (1 - η * lam i)
          ^ 2)) - (n : ℝ) * lagWeight n ((1 - η * lam i) ^ 2))) := by ring
    _ ≤ 1 / 2 * ((1 / (1 - η * lam i / 2)) ^ 2 * (2 * (1 - η * lam i) ^ 2 / (n * (1 - (1 - η * lam
        i) ^ 2) ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdef hW) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ = 1 / (n : ℝ) * ((1 / (1 - η * lam i / 2)) ^ 2 * ((1 - η * lam i) ^ 2 / (1 - (1 - η * lam i)
        ^ 2) ^ 2)) := by
      field_simp

/-- `n·W_{η,n} ≤ L_η` for every `n ≥ 1`. -/
theorem avgLimit_mul_le_Leta (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {n : ℕ}
    (hn : 1 ≤ n) :
    (n : ℝ) * (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * lagWeight n ((1 - η * lam i) ^ 2)) ≤ ∑
        i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) := by
  rw [← Leta_eq_lagWeight_limit hlam hη hηl]
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hW : 0 ≤ (1 / (1 - η * lam i / 2)) ^ 2 := sq_nonneg _
  have hle := lagWeight_mul_le hn (sq_nonneg (1 - η * lam i)) (alpha_sq_lt_one hlam hη hηl i)
  calc (n : ℝ) * (1 / 2 * ((1 / (1 - η * lam i / 2)) ^ 2 * lagWeight n ((1 - η * lam i) ^ 2)))
      = 1 / 2 * ((1 / (1 - η * lam i / 2)) ^ 2 * ((n : ℝ) * lagWeight n ((1 - η * lam i) ^ 2))) :=
          by ring
    _ ≤ 1 / 2 * ((1 / (1 - η * lam i / 2)) ^ 2 * ((1 + (1 - η * lam i) ^ 2) / (1 - (1 - η * lam i)
        ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hW) (by norm_num : (0 : ℝ) ≤ 1 / 2)

end Spectrum

end Laplace.Multi
