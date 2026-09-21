/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.LocalisedLLC

/-!
# The ULA-corrected localised LLC (E3)

E3 of the Sanity on Sampling note measures `4.23, 2.55, 0.83` for the localised LLC against the
predicted `½ t tr(H(tH + γI)⁻¹) = 4.20, 2.50, 0.80` and attributes "the residual" to "the 5% ULA
inflation of the stiff directions at `lr pmax = 0.1`". Here the ULA law `Σ_ULA = (P − (h/2)P²)⁻¹`
for the localised precision `P = tH + γI` is put in the eigenbasis `U` of `H`:

* `orthoOf_transpose_ulaCov_localised_mul`: `Uᵀ Σ_ULA U = diag(1/(aᵢ(1 − h aᵢ/2)))`, `aᵢ = tλᵢ + γ`;
* `trace_ulaCov_localised`: `tr Σ_ULA = ∑ᵢ 1/(aᵢ(1 − h aᵢ/2))` (E3's "ULA-corrected form");
* `ula_localised_llc`: `(t/2) tr(H Σ_ULA) = ½ ∑ᵢ (tλᵢ/(tλᵢ + γ))/(1 − h(tλᵢ + γ)/2)` — the
  ULA-corrected localised LLC, `ula_llc` at `γ = 0` and `localisedLLC` at `h → 0`;
* `localisedLLC_le_ula_localised_llc`, `ula_localised_llc_le`: the ULA-corrected value exceeds the
  exact localised LLC by a factor between `1` and `1/(1 − h pmax/2)` (`20/19` at `h pmax = 1/10`:
  the "5% ULA inflation"); the per-direction excess `(h aᵢ/2)/(1 − h aᵢ/2)` is increasing in `aᵢ`
  (`ula_excess_mono`), largest on the stiffest direction.

The numerical check reproduces the note's *measured* values `4.26, 2.56, 0.83` from the
ULA-corrected formula.
-/

open Matrix Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Uᵀ (P − (h/2)P²) U = diag(aᵢ − (h/2)aᵢ²)` for `P = tH + γI`, `aᵢ = tλᵢ + γ`. -/
theorem orthoOf_transpose_ulaDenom_mul {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (t γ h : ℝ) :
    (orthoOf hH)ᵀ * ((t • H + γ • (1 : Matrix ι ι ℝ)) -
        (h / 2) • ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ)))) *
      orthoOf hH =
      diagonal (fun i =>
        (t * hH.eigenvalues i + γ) - h / 2 * (t * hH.eigenvalues i + γ) ^ 2) := by
  have hM := orthoOf_transpose_localised_mul hH t γ
  have hUU' : orthoOf hH * (orthoOf hH)ᵀ = 1 := orthoOf_mul_transpose hH
  have hMM : (orthoOf hH)ᵀ * ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ))) *
      orthoOf hH =
      diagonal (fun i => t * hH.eigenvalues i + γ) *
        diagonal (fun i => t * hH.eigenvalues i + γ) := by
    rw [← hM]
    have : (orthoOf hH)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ)) * orthoOf hH *
        ((orthoOf hH)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ)) * orthoOf hH) =
        (orthoOf hH)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ)) *
          (orthoOf hH * (orthoOf hH)ᵀ) * (t • H + γ • (1 : Matrix ι ι ℝ)) * orthoOf hH := by
      simp only [Matrix.mul_assoc]
    rw [this, hUU', Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hM, hMM,
    diagonal_mul_diagonal, ← diagonal_smul, diagonal_sub]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The ULA covariance of the localised precision in the eigenbasis of `H`**:
`Uᵀ Σ_ULA U = diag(1/(aᵢ(1 − h aᵢ/2)))`, `aᵢ = tλᵢ + γ`, for `0 < h aᵢ < 2`. -/
theorem orthoOf_transpose_ulaCov_localised_mul {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ h : ℝ}
    (ht : 0 < t) (hγ : 0 ≤ γ) (hstab : ∀ i, h * (t * hH.1.eigenvalues i + γ) < 2) :
    (orthoOf hH.1)ᵀ * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h * orthoOf hH.1 =
      diagonal (fun i => 1 / ((t * hH.1.eigenvalues i + γ) *
        (1 - h * (t * hH.1.eigenvalues i + γ) / 2))) := by
  set a : ι → ℝ := fun i => t * hH.1.eigenvalues i + γ with ha
  have ha0 : ∀ i, 0 < a i := fun i => by
    have := hH.eigenvalues_pos i
    simp only [ha]
    positivity
  have hq : ∀ i, 0 < 1 - h * a i / 2 := fun i => by
    have := hstab i
    simp only [ha] at this ⊢
    linarith
  have hden : ∀ i, a i - h / 2 * a i ^ 2 ≠ 0 := fun i => by
    have : a i - h / 2 * a i ^ 2 = a i * (1 - h * a i / 2) := by ring
    rw [this]
    exact mul_ne_zero (ha0 i).ne' (hq i).ne'
  have hconj := orthoOf_transpose_ulaDenom_mul hH.1 t γ h
  have hUU : (orthoOf hH.1)ᵀ * orthoOf hH.1 = 1 := orthoOf_transpose_mul hH.1
  have hUU' : orthoOf hH.1 * (orthoOf hH.1)ᵀ = 1 := orthoOf_mul_transpose hH.1
  have hinv : ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h =
      orthoOf hH.1 * diagonal (fun i => 1 / (a i - h / 2 * a i ^ 2)) * (orthoOf hH.1)ᵀ := by
    unfold ulaCov
    apply Matrix.inv_eq_left_inv
    have hre : orthoOf hH.1 * diagonal (fun i => 1 / (a i - h / 2 * a i ^ 2)) * (orthoOf hH.1)ᵀ *
        ((t • H + γ • (1 : Matrix ι ι ℝ)) -
          (h / 2) • ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ)))) =
        orthoOf hH.1 * diagonal (fun i => 1 / (a i - h / 2 * a i ^ 2)) *
          ((orthoOf hH.1)ᵀ * ((t • H + γ • (1 : Matrix ι ι ℝ)) -
            (h / 2) • ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ)))) *
              orthoOf hH.1) * (orthoOf hH.1)ᵀ := by
      simp only [Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [hre, hconj, Matrix.mul_assoc (orthoOf hH.1), diagonal_mul_diagonal]
    have hd : (fun i => 1 / (a i - h / 2 * a i ^ 2) *
        ((t * hH.1.eigenvalues i + γ) - h / 2 * (t * hH.1.eigenvalues i + γ) ^ 2)) =
        fun _ => (1 : ℝ) := funext fun i => one_div_mul_cancel (hden i)
    rw [hd, diagonal_one, Matrix.mul_one, hUU']
  rw [hinv]
  simp only [← Matrix.mul_assoc]
  rw [hUU, Matrix.one_mul, Matrix.mul_assoc, hUU, Matrix.mul_one]
  congr 1
  funext i
  have : a i - h / 2 * a i ^ 2 = a i * (1 - h * a i / 2) := by ring
  rw [this]

/-- **E3's "ULA-corrected form" of the localised covariance trace**:
`tr Σ_ULA = ∑ᵢ 1/((tλᵢ + γ)(1 − h(tλᵢ + γ)/2))`. -/
theorem trace_ulaCov_localised {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ h : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) (hstab : ∀ i, h * (t * hH.1.eigenvalues i + γ) < 2) :
    (ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h).trace =
      ∑ i, 1 / ((t * hH.1.eigenvalues i + γ) * (1 - h * (t * hH.1.eigenvalues i + γ) / 2)) := by
  have hUU' : orthoOf hH.1 * (orthoOf hH.1)ᵀ = 1 := orthoOf_mul_transpose hH.1
  have h1 : (ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h).trace =
      ((orthoOf hH.1)ᵀ * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h * orthoOf hH.1).trace := by
    rw [Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
  rw [h1, orthoOf_transpose_ulaCov_localised_mul hH ht hγ hstab, trace_diagonal]

/-- **The ULA-corrected localised LLC**:
`(t/2) tr(H Σ_ULA) = ½ ∑ᵢ (tλᵢ/(tλᵢ + γ))/(1 − h(tλᵢ + γ)/2)`. -/
theorem ula_localised_llc {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ h : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (hstab : ∀ i, h * (t * hH.1.eigenvalues i + γ) < 2) :
    t / 2 * (H * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h).trace =
      1 / 2 * ∑ i, (t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ)) /
        (1 - h * (t * hH.1.eigenvalues i + γ) / 2) := by
  have hUU' : orthoOf hH.1 * (orthoOf hH.1)ᵀ = 1 := orthoOf_mul_transpose hH.1
  have h1 : (H * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h).trace =
      (((orthoOf hH.1)ᵀ * H * orthoOf hH.1) *
        ((orthoOf hH.1)ᵀ * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h * orthoOf hH.1)).trace := by
    have : ((orthoOf hH.1)ᵀ * H * orthoOf hH.1) *
        ((orthoOf hH.1)ᵀ * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h * orthoOf hH.1) =
        (orthoOf hH.1)ᵀ * (H * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h) * orthoOf hH.1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (orthoOf hH.1) (orthoOf hH.1)ᵀ, hUU', Matrix.one_mul]
    rw [this, Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
  rw [h1, orthoOf_transpose_mul_mul hH.1, orthoOf_transpose_ulaCov_localised_mul hH ht hγ hstab,
    diagonal_mul_diagonal, trace_diagonal, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := hH.eigenvalues_pos i
  have hq : 1 - h * (t * hH.1.eigenvalues i + γ) / 2 ≠ 0 := by have := hstab i; linarith
  have ha : t * hH.1.eigenvalues i + γ ≠ 0 := by positivity
  field_simp

/-- The per-direction ULA excess `(h a/2)/(1 − h a/2)` is increasing in `a` on `0 ≤ h a < 2`:
the inflation is largest on the stiffest direction. -/
theorem ula_excess_mono {h a a' : ℝ} (hh : 0 < h) (haa' : a ≤ a') (hstab : h * a' < 2) :
    (h * a / 2) / (1 - h * a / 2) ≤ (h * a' / 2) / (1 - h * a' / 2) := by
  have h1 : 0 < 1 - h * a' / 2 := by linarith
  have h2 : 0 < 1 - h * a / 2 := by nlinarith [mul_le_mul_of_nonneg_left haa' hh.le]
  rw [div_le_div_iff₀ h2 h1]
  nlinarith [mul_le_mul_of_nonneg_left haa' hh.le]

/-- **The ULA-corrected localised LLC is at least the exact one.** -/
theorem localisedLLC_le_ula_localised_llc {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ h : ℝ}
    (ht : 0 < t) (hγ : 0 ≤ γ) (hh : 0 < h) (hstab : ∀ i, h * (t * hH.1.eigenvalues i + γ) < 2) :
    localisedLLC hH t γ ≤ t / 2 * (H * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h).trace := by
  rw [ula_localised_llc hH ht hγ hstab, localisedLLC]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
  have hp := hH.eigenvalues_pos i
  have hq : 0 < 1 - h * (t * hH.1.eigenvalues i + γ) / 2 := by have := hstab i; linarith
  have hq1 : 1 - h * (t * hH.1.eigenvalues i + γ) / 2 ≤ 1 := by
    have : 0 ≤ h * (t * hH.1.eigenvalues i + γ) := by positivity
    linarith
  exact le_div_self (by positivity) hq hq1

/-- **The ULA inflation of the localised LLC is at most `1/(1 − h pmax/2)`**: with
`tλᵢ + γ ≤ pmax` and `h pmax < 2`, `(t/2) tr(H Σ_ULA) ≤ localisedLLC/(1 − h pmax/2)`
(`20/19` at `h pmax = 1/10`, the note's "5% ULA inflation"). -/
theorem ula_localised_llc_le {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ h pmax : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) (hh : 0 < h) (hpmax : ∀ i, t * hH.1.eigenvalues i + γ ≤ pmax)
    (hstab : h * pmax < 2) :
    t / 2 * (H * ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h).trace ≤
      localisedLLC hH t γ / (1 - h * pmax / 2) := by
  have hstab' : ∀ i, h * (t * hH.1.eigenvalues i + γ) < 2 := fun i =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hpmax i) hh.le) hstab
  have hq : 0 < 1 - h * pmax / 2 := by linarith
  rw [ula_localised_llc hH ht hγ hstab', localisedLLC, le_div_iff₀ hq, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hp := hH.eigenvalues_pos i
  have hqi : 0 < 1 - h * (t * hH.1.eigenvalues i + γ) / 2 := by have := hstab' i; linarith
  have hle : 1 - h * pmax / 2 ≤ 1 - h * (t * hH.1.eigenvalues i + γ) / 2 := by
    linarith [mul_le_mul_of_nonneg_left (hpmax i) hh.le]
  have hterm : 0 ≤ t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) := by positivity
  have hkey : t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) /
      (1 - h * (t * hH.1.eigenvalues i + γ) / 2) * (1 - h * pmax / 2) ≤
      t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hqi]
    exact mul_le_mul_of_nonneg_left hle hterm
  calc 1 / 2 * (t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) /
        (1 - h * (t * hH.1.eigenvalues i + γ) / 2)) * (1 - h * pmax / 2)
      = 1 / 2 * (t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) /
        (1 - h * (t * hH.1.eigenvalues i + γ) / 2) * (1 - h * pmax / 2)) := by ring
    _ ≤ 1 / 2 * (t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ)) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)

/-- **E3's left panel**: the ULA-corrected covariance trace exceeds `tr (tH + γI)⁻¹` by a factor
between `1` and `1/(1 − h pmax/2)`. -/
theorem trace_ulaCov_localised_bounds {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ h pmax : ℝ}
    (ht : 0 < t) (hγ : 0 ≤ γ) (hh : 0 < h) (hpmax : ∀ i, t * hH.1.eigenvalues i + γ ≤ pmax)
    (hstab : h * pmax < 2) :
    (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹.trace ≤
        (ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h).trace ∧
      (ulaCov (t • H + γ • (1 : Matrix ι ι ℝ)) h).trace ≤
        (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹.trace / (1 - h * pmax / 2) := by
  have hstab' : ∀ i, h * (t * hH.1.eigenvalues i + γ) < 2 := fun i =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hpmax i) hh.le) hstab
  have hq : 0 < 1 - h * pmax / 2 := by linarith
  rw [trace_ulaCov_localised hH ht hγ hstab', trace_localised_inv hH ht hγ]
  constructor
  · refine Finset.sum_le_sum fun i _ => ?_
    have hp := hH.eigenvalues_pos i
    have ha : 0 < t * hH.1.eigenvalues i + γ := by positivity
    have hqi : 0 < 1 - h * (t * hH.1.eigenvalues i + γ) / 2 := by have := hstab' i; linarith
    have hqi1 : 1 - h * (t * hH.1.eigenvalues i + γ) / 2 ≤ 1 := by
      have : 0 ≤ h * (t * hH.1.eigenvalues i + γ) := by positivity
      linarith
    exact one_div_le_one_div_of_le (by positivity) (mul_le_of_le_one_right ha.le hqi1)
  · rw [le_div_iff₀ hq, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hp := hH.eigenvalues_pos i
    have ha : 0 < t * hH.1.eigenvalues i + γ := by positivity
    have hqi : 0 < 1 - h * (t * hH.1.eigenvalues i + γ) / 2 := by have := hstab' i; linarith
    have hle : 1 - h * pmax / 2 ≤ 1 - h * (t * hH.1.eigenvalues i + γ) / 2 := by
      linarith [mul_le_mul_of_nonneg_left (hpmax i) hh.le]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) ha]
    nlinarith [mul_le_mul_of_nonneg_left hle ha.le]

end Laplace.Sampler
