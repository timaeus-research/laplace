/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.ULA

/-!
# E5's "1.17 = (1 + 4/3)/2" and the E1 inflation ratio

E1's quoted numbers are already in the seabed (`ula_inflation_e1`, `ula_llc_isotropic`,
`ula_llc_e1` in `StepSizeTradeoff`). This file adds the two remaining pieces:

* `ulaCov_conj_diag_ratio`: the ULA eigenbasis variance over the Laplace value `1/pᵢ` is exactly
  `1/(1 − hpᵢ/2)` (E1's "inflated by exactly `1/(1 − lr·pmax/2)`"), as a ratio of the two laws;
* `ula_llc_two`, `ula_llc_stiff_flat_bound`: E5's "SGLD at `lr·pmax = 0.5` gives
  `1.17 = (1 + 4/3)/2`, the ULA law applied to the stiff direction only": for eigenvalues `p`, `p/κ`
  with `hp = 1/2` and `κ ≥ 2500` the ULA-corrected LLC is `7/6 + 1/(2(4κ − 1))`, within `10⁻⁴` of
  `7/6` (`1.17` is rounded, not exactly `(1 + 4/3)/2`).

The E5 sentence is about SGLD on the non-Gaussian Rosenbrock target; `ula_llc` is the Gaussian law,
so `ula_llc_stiff_flat_bound` certifies the arithmetic of the explanation, not the sampler result.
-/

open Matrix

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **E1, first finding**: the ULA eigenbasis variance over the Laplace value `1/pᵢ` is
`1/(1 − hpᵢ/2)`. -/
theorem ulaCov_conj_diag_ratio {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h : ℝ) (hh : 0 < h)
    (hev : ∀ i, 0 < hP.eigenvalues i ∧ h * hP.eigenvalues i < 2) (i : ι) :
    ((orthoOf hP)ᵀ * ulaCov P h * orthoOf hP) i i / (1 / hP.eigenvalues i) =
      1 / (1 - h * hP.eigenvalues i / 2) := by
  rw [ulaCov_conj_apply hP h hh hev i i, if_pos rfl]
  have hp := (hev i).1
  have hne : 1 - h * hP.eigenvalues i / 2 ≠ 0 := by have := (hev i).2; linarith
  field_simp

/-- The ULA-corrected LLC in two dimensions with eigenvalues `p` and `p/κ`. -/
theorem ula_llc_two {H : Matrix (Fin 2) (Fin 2) ℝ} (t h : ℝ) (hP : (t • H).PosDef) (hh : 0 < h)
    {p κ : ℝ} (hp0 : hP.1.eigenvalues 0 = p) (hp1 : hP.1.eigenvalues 1 = p / κ)
    (hhp : h * p < 2) (hhpκ : h * (p / κ) < 2) :
    t / 2 * (H * ulaCov (t • H) h).trace =
      1 / 2 * (1 / (1 - h * p / 2) + 1 / (1 - h * (p / κ) / 2)) := by
  rw [ula_llc t h hP hh (fun i => by fin_cases i <;> simp [hp0, hp1, hhp, hhpκ]),
    Fin.sum_univ_two, hp0, hp1]

/-- **The arithmetic behind E5's "1.17 = (1 + 4/3)/2"** (a two-eigenvalue Gaussian proxy, not a
statement about SGLD on Rosenbrock): for `hp = 1/2` on the stiff direction and `κ ≥ 2500`,
`½(1/(1 − hp/2) + 1/(1 − h(p/κ)/2)) = 7/6 + 1/(2(4κ − 1))` is within `10⁻⁴` of `7/6`. -/
theorem ula_llc_stiff_flat_bound {h p κ : ℝ} (hhp : h * p = 1 / 2) (hκ : 2500 ≤ κ) :
    |1 / 2 * (1 / (1 - h * p / 2) + 1 / (1 - h * (p / κ) / 2)) - 7 / 6| ≤ 1 / 10000 := by
  have hκ0 : 0 < κ := by linarith
  have hflat : h * (p / κ) = 1 / (2 * κ) := by
    rw [← mul_div_assoc, hhp]
    field_simp
  rw [hhp, hflat]
  have hden : 1 - 1 / (2 * κ) / 2 = 1 - 1 / (4 * κ) := by ring
  rw [hden]
  have h4κ : 0 < 1 - 1 / (4 * κ) := by
    have : 1 / (4 * κ) ≤ 1 / 10000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hlo : 1 ≤ 1 / (1 - 1 / (4 * κ)) := by
    rw [le_div_iff₀ h4κ]
    have : 0 < 1 / (4 * κ) := by positivity
    linarith
  have hhi : 1 / (1 - 1 / (4 * κ)) ≤ 10000 / 9999 := by
    rw [div_le_div_iff₀ h4κ (by norm_num)]
    have : 1 / (4 * κ) ≤ 1 / 10000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

end Laplace.Sampler
