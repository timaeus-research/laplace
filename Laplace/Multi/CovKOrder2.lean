/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GibbsIBP

/-!
# eq:covK to second order for the anharmonic oscillator

The seabed certifies eq:covK, `t²Cov[ℓ, ψ] → C`, with an `O(1/t)` rate (E2's "relative error
`∝ 1/t`"). This file identifies the coefficient of that `1/t`. The moment recursion of
`Laplace.Multi.GibbsIBP` at `k = 2` turns the seabed's *even* second-order coefficients into the
third moment's (`thirdMoment_order2_rate`: `t²⟨x³⟩ = −5α/(2λ³) + B₃/t + O(t⁻²)`,
`B₃ = −15α³/(2λ⁶) + 25αγ/(4λ⁵)`), and with the pair covariances expanded,

* `covK_sq_order2_rate`: `t²Cov[ℓ, x²] = 1/λ + C'_sq/t + O(t⁻²)`, `C'_sq = 5α²/(2λ⁴) − γ/λ³`;
* `covK_lin_order2_rate`: `t²Cov[ℓ, x] = −α/(2λ²) + C'_lin/t + O(t⁻²)`,
  `C'_lin = −5α³/(4λ⁵) + 4αγ/(3λ⁴)`;
* `covK_order2_rate`: for the probe `ψ = (B/2)x² + bx`,
  `t²Cov[ℓ, ψ] = B/(2λ) − bα/(2λ²) + (B C'_sq/2 + b C'_lin)/t + O(t⁻²)`.

`C'_sq = 2B₂` and `C'_lin = 2B₁` (the second-order coefficients of `t⟨x²⟩` and `t⟨x⟩`), as the
derivative identity `Cov_t[ℓ, ψ] = −∂ₜ⟨ψ⟩_t` predicts.
-/

open Real MeasureTheory Filter Topology
open scoped Nat

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential cubicScale quarticScale evenMomentCoeff)

/-! ### Coefficients -/

section Coeffs

variable {lam alpha gamma : ℝ}

theorem evenMomentCoeff_two_eq (hlam : 0 < lam) :
    evenMomentCoeff lam alpha gamma 2 = 25 * alpha ^ 2 / (2 * lam ^ 3) - 4 * gamma / lam ^ 2 := by
  rw [Laplace.OneD.evenMomentCoeff_two]
  unfold cubicScale quarticScale
  have hs : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  have hs0 : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
  rw [div_pow, mul_pow, mul_pow, hs]
  field_simp
  ring

/-- The third moment's second-order coefficient: `t²⟨x³⟩ = −5α/(2λ³) + B₃/t + O(t⁻²)`. -/
noncomputable def thirdCoeff2 (lam alpha gamma : ℝ) : ℝ :=
  -15 * alpha ^ 3 / (2 * lam ^ 6) + 25 * alpha * gamma / (4 * lam ^ 5)

/-- eq:covK's second-order coefficient for the probe `x²`. -/
noncomputable def covKCoeff2Sq (lam alpha gamma : ℝ) : ℝ :=
  5 * alpha ^ 2 / (2 * lam ^ 4) - gamma / lam ^ 3

/-- eq:covK's second-order coefficient for the probe `x`. -/
noncomputable def covKCoeff2Lin (lam alpha gamma : ℝ) : ℝ :=
  -5 * alpha ^ 3 / (4 * lam ^ 5) + 4 * alpha * gamma / (3 * lam ^ 4)

theorem covKCoeff2Sq_eq_two_mul (lam alpha gamma : ℝ) :
    covKCoeff2Sq lam alpha gamma = 2 * (5 * alpha ^ 2 / (4 * lam ^ 4) - gamma / (2 * lam ^ 3)) := by
  unfold covKCoeff2Sq; ring

theorem covKCoeff2Lin_eq_two_mul (lam alpha gamma : ℝ) :
    covKCoeff2Lin lam alpha gamma = 2 * meanCoeff2 lam alpha gamma := by
  unfold covKCoeff2Lin meanCoeff2; ring

end Coeffs

/-! ### Moments -/

section Moments

variable {lam alpha gamma : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `|t²⟨x⁴⟩ − 3/λ² − (25α²/(2λ⁵) − 4γ/λ⁴)/t| ≤ K/t²`. -/
theorem fourthMoment_order2_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) - 3 / lam ^ 2 -
        (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.evenMoment_anharmonic_order2_rate hlam hgamma hdisc 2
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have h' := h ht
  simp only [show (2 * 2 : ℕ) = 4 from rfl, show (4 - 1 : ℕ) = 3 from rfl] at h'
  have h3 : (((3 : ℕ)‼ : ℕ) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [h3, evenMomentCoeff_two_eq hlam] at h'
  have e : (25 * alpha ^ 2 / (2 * lam ^ 3) - 4 * gamma / lam ^ 2) / (lam ^ 2 * t) =
      (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t := by
    field_simp
  rw [e] at h'
  exact h'

/-- `|t³⟨x⁵⟩ + 35α/(2λ⁴)| ≤ K/t`. -/
theorem fifthMoment_bound :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) + 35 * alpha / (2 * lam ^ 4)| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.oddMoment_anharmonic_rate hlam hgamma hdisc 2
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have h' := h ht
  simp only [show (2 * 2 + 1 : ℕ) = 5 from rfl, show (2 + 1 : ℕ) = 3 from rfl,
    show (2 + 2 : ℕ) = 4 from rfl, show (2 * 2 + 3 : ℕ) = 7 from rfl] at h'
  have h7 : (((7 : ℕ)‼ : ℕ) : ℝ) = 105 := by norm_num [Nat.doubleFactorial]
  rw [h7] at h'
  have e : alpha * 105 / (6 * lam ^ 4) = 35 * alpha / (2 * lam ^ 4) := by ring
  rw [e] at h'
  exact h'

/-- **The third moment to second order**: `|t²⟨x³⟩ + 5α/(2λ³) − B₃/t| ≤ K/t²` with
`B₃ = −15α³/(2λ⁶) + 25αγ/(4λ⁵)`, from the moment recursion at `k = 2`. -/
theorem thirdMoment_order2_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) + 5 * alpha / (2 * lam ^ 3) - thirdCoeff2 lam alpha gamma / t| ≤
        K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := mean_anharmonic_order2_rate hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_order2_rate hlam hgamma hdisc
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_bound hlam hgamma hdisc
  refine ⟨(2 * K₁ + |alpha| / 2 * K₄ + gamma / 6 * K₅) / lam, T₁ + T₄ + T₅, by positivity,
    by linarith, fun {t} ht => ?_⟩
  have hT₁t : T₁ ≤ t := by linarith
  have hT₄t : T₄ ≤ t := by linarith
  have hT₅t : T₅ ≤ t := by linarith
  have ht1 : 1 ≤ t := hT₁.trans hT₁t
  have ht0 : 0 < t := by linarith
  have hibp := ibp_anharmonic hlam hgamma hdisc ht0 2
  have e : (fun x : ℝ => x ^ 2 * anharmonicDeriv lam alpha gamma x) =
      fun x => lam * x ^ 3 + alpha / 2 * x ^ 4 + gamma / 6 * x ^ 5 := by
    funext x
    unfold anharmonicDeriv
    ring
  rw [e, gibbs_lin3 (integrable_pow_exp' hlam hgamma hdisc ht0 3)
    (integrable_pow_exp' hlam hgamma hdisc ht0 4) (integrable_pow_exp' hlam hgamma hdisc ht0 5)]
    at hibp
  simp only [show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat] at hibp
  have e₁ := h₁ hT₁t
  have e₄ := h₄ hT₄t
  have e₅ := h₅ hT₅t
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x) with hM₁
  set M₃ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3) with hM₃
  set M₄ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4) with hM₄
  set M₅ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 5) with hM₅
  have hM₃e : t ^ 2 * M₃ =
      (2 * (t * M₁) - alpha / 2 * (t ^ 2 * M₄) - gamma / 6 * (t ^ 2 * M₅)) / lam := by
    rw [eq_div_iff hlam.ne']
    linear_combination (-t) * hibp
  have key : t ^ 2 * M₃ + 5 * alpha / (2 * lam ^ 3) - thirdCoeff2 lam alpha gamma / t =
      (2 * (t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t) -
        alpha / 2 * (t ^ 2 * M₄ - 3 / lam ^ 2 -
          (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t) -
        gamma / 6 * ((t ^ 3 * M₅ + 35 * alpha / (2 * lam ^ 4)) / t)) / lam := by
    rw [hM₃e]
    unfold thirdCoeff2 meanCoeff2
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hlam, div_right_comm, div_le_div_iff_of_pos_right hlam]
  calc |2 * (t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t) -
        alpha / 2 * (t ^ 2 * M₄ - 3 / lam ^ 2 -
          (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t) -
        gamma / 6 * ((t ^ 3 * M₅ + 35 * alpha / (2 * lam ^ 4)) / t)|
      ≤ |2 * (t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t)| +
        |alpha / 2 * (t ^ 2 * M₄ - 3 / lam ^ 2 -
          (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t)| +
        |gamma / 6 * ((t ^ 3 * M₅ + 35 * alpha / (2 * lam ^ 4)) / t)| := by
          refine (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = 2 * |t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t| +
        |alpha| / 2 * |t ^ 2 * M₄ - 3 / lam ^ 2 -
          (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t| +
        gamma / 6 * (|t ^ 3 * M₅ + 35 * alpha / (2 * lam ^ 4)| / t) := by
          rw [abs_mul, abs_two, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_mul, abs_of_pos (by positivity : (0 : ℝ) < gamma / 6), abs_div, abs_of_pos ht0]
    _ ≤ 2 * (K₁ / t ^ 2) + |alpha| / 2 * (K₄ / t ^ 2) + gamma / 6 * (K₅ / t / t) := by gcongr
    _ = (2 * K₁ + |alpha| / 2 * K₄ + gamma / 6 * K₅) / t ^ 2 := by
          field_simp

end Moments

/-! ### The Stein–covariance reduction -/

section Stein

variable {lam alpha gamma : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- `⟨x ℓ'⟩ = 1/t` (the Stein identity at `k = 1`). -/
theorem gibbs_mul_deriv_eq {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => x * anharmonicDeriv lam alpha gamma x) = 1 / t := by
  have h := ibp_anharmonic hlam hgamma hdisc ht 1
  simp only [Nat.cast_one, one_mul, show (1 - 1 : ℕ) = 0 from rfl, pow_zero, pow_one] at h
  rw [gibbsExpectation_one' (partition_pos' hlam hgamma hdisc ht)] at h
  field_simp
  linarith [h]

/-- **The Stein–covariance reduction for `x²`**:
`t²Cov[ℓ, x²] = t⟨x²⟩ − (α/12)t²Cov[x³, x²] − (γ/24)t²Cov[x⁴, x²]`. -/
theorem covK_sq_stein {t : ℝ} (ht : 0 < t) :
    t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) =
      t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2) -
        alpha / 12 * (t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) (fun x => x ^ 2)) -
        gamma / 24 * (t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) (fun x => x ^ 2)) := by
  have h3 := ibp_anharmonic hlam hgamma hdisc ht 3
  simp only [show (3 - 1 : ℕ) = 2 from rfl, Nat.cast_ofNat] at h3
  have h1 := gibbs_mul_deriv_eq hlam hgamma hdisc ht
  have hℓ : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (anharmonicPotential lam alpha gamma) =
      1 / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x * anharmonicDeriv lam alpha gamma x) +
        (-alpha / 12) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        (-gamma / 24) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) := by
    have hi1 : Integrable (fun x => x * anharmonicDeriv lam alpha gamma x *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
      (integrable_pow_mul_deriv_exp hlam hgamma hdisc ht 1).congr
        (Eventually.of_forall fun x => by simp only [pow_one])
    rw [← gibbs_lin3 hi1 (integrable_pow_exp' hlam hgamma hdisc ht 3)
      (integrable_pow_exp' hlam hgamma hdisc ht 4)]
    congr 1
    funext x
    unfold anharmonicPotential anharmonicDeriv
    ring
  have hℓ2 : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => anharmonicPotential lam alpha gamma x * x ^ 2) =
      1 / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3 * anharmonicDeriv lam alpha gamma x) +
        (-alpha / 12) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) +
        (-gamma / 24) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 6) := by
    rw [← gibbs_lin3 (integrable_pow_mul_deriv_exp hlam hgamma hdisc ht 3)
      (integrable_pow_exp' hlam hgamma hdisc ht 5) (integrable_pow_exp' hlam hgamma hdisc ht 6)]
    congr 1
    funext x
    unfold anharmonicPotential anharmonicDeriv
    ring
  rw [Laplace.OneD.gibbsCov_pow_pow, Laplace.OneD.gibbsCov_pow_pow]
  simp only [show (3 + 2 : ℕ) = 5 from rfl, show (4 + 2 : ℕ) = 6 from rfl]
  simp only [_root_.Laplace.gibbsCov]
  rw [hℓ2, hℓ, h1]
  set M₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2) with hM₂
  set X := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3 * anharmonicDeriv lam alpha gamma x) with hX
  have hX' : X = 3 * M₂ / t := by
    field_simp
    linarith [h3]
  rw [hX']
  field_simp
  ring

/-- **The Stein–covariance reduction for `x`**:
`t²Cov[ℓ, x] = ½t⟨x⟩ − (α/12)t²Cov[x³, x] − (γ/24)t²Cov[x⁴, x]`. -/
theorem covK_lin_stein {t : ℝ} (ht : 0 < t) :
    t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => x) =
      1 / 2 * (t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x)) -
        alpha / 12 * (t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) (fun x => x)) -
        gamma / 24 * (t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) (fun x => x)) := by
  have h2 := ibp_anharmonic hlam hgamma hdisc ht 2
  simp only [show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat] at h2
  have h1 := gibbs_mul_deriv_eq hlam hgamma hdisc ht
  have hℓ : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (anharmonicPotential lam alpha gamma) =
      1 / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x * anharmonicDeriv lam alpha gamma x) +
        (-alpha / 12) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 3) +
        (-gamma / 24) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) := by
    have hi1 : Integrable (fun x => x * anharmonicDeriv lam alpha gamma x *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) :=
      (integrable_pow_mul_deriv_exp hlam hgamma hdisc ht 1).congr
        (Eventually.of_forall fun x => by simp only [pow_one])
    rw [← gibbs_lin3 hi1 (integrable_pow_exp' hlam hgamma hdisc ht 3)
      (integrable_pow_exp' hlam hgamma hdisc ht 4)]
    congr 1
    funext x
    unfold anharmonicPotential anharmonicDeriv
    ring
  have hℓ1 : _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x => anharmonicPotential lam alpha gamma x * x) =
      1 / 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 2 * anharmonicDeriv lam alpha gamma x) +
        (-alpha / 12) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 4) +
        (-gamma / 24) * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x => x ^ 5) := by
    rw [← gibbs_lin3 (integrable_pow_mul_deriv_exp hlam hgamma hdisc ht 2)
      (integrable_pow_exp' hlam hgamma hdisc ht 4) (integrable_pow_exp' hlam hgamma hdisc ht 5)]
    congr 1
    funext x
    unfold anharmonicPotential anharmonicDeriv
    ring
  rw [Laplace.OneD.gibbsCov_pow_id, Laplace.OneD.gibbsCov_pow_id]
  simp only [show (3 + 1 : ℕ) = 4 from rfl, show (4 + 1 : ℕ) = 5 from rfl]
  simp only [_root_.Laplace.gibbsCov]
  rw [hℓ1, hℓ, h1]
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x) with hM₁
  set X := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2 * anharmonicDeriv lam alpha gamma x) with hX
  have hX' : X = 2 * M₁ / t := by
    field_simp
    linarith [h2]
  rw [hX']
  field_simp
  ring

end Stein

/-! ### Pair covariances to order `1/t` -/

section Pairs

variable {lam alpha gamma : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- Leading-order inputs, normalised: `|t⟨x²⟩ − 1/λ| ≤ K/t`, `|t²⟨x⁴⟩ − 3/λ²| ≤ K/t`,
`|t³⟨x⁶⟩ − 15/λ³| ≤ K/t`. -/
theorem secondMoment_lead :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2) - 1 / lam| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.evenMoment_anharmonic_rate hlam hgamma hdisc 1
  exact ⟨K, T, hK, hT, fun {t} ht => by simpa [Nat.doubleFactorial] using h ht⟩

theorem fourthMoment_lead :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 4) - 3 / lam ^ 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.evenMoment_anharmonic_rate hlam hgamma hdisc 2
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have h' := h ht
  simp only [show (2 * 2 : ℕ) = 4 from rfl, show (4 - 1 : ℕ) = 3 from rfl] at h'
  have h3 : (((3 : ℕ)‼ : ℕ) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rwa [h3] at h'

theorem sixthMoment_lead :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 6) - 15 / lam ^ 3| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.evenMoment_anharmonic_rate hlam hgamma hdisc 3
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have h' := h ht
  simp only [show (2 * 3 : ℕ) = 6 from rfl, show (6 - 1 : ℕ) = 5 from rfl] at h'
  have h5 : (((5 : ℕ)‼ : ℕ) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
  rwa [h5] at h'

theorem thirdMoment_lead :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 3) - -(5 * alpha / (2 * lam ^ 3))| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := Laplace.OneD.thirdMoment_anharmonic_rate_sharp hlam hgamma hdisc
  exact ⟨K, T, hK, hT, fun {t} ht => by rw [sub_neg_eq_add]; exact h ht⟩

theorem fifthMoment_lead :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 3 * _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 5) - -(35 * alpha / (2 * lam ^ 4))| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := fifthMoment_bound hlam hgamma hdisc
  exact ⟨K, T, hK, hT, fun {t} ht => by rw [sub_neg_eq_add]; exact h ht⟩

omit hlam hgamma hdisc in
/-- `|(X − Y)/t − (a − b)/t| ≤ (K + K')/t²` from the two rates. -/
theorem sub_div_rate {X Y a b K K' t : ℝ} (ht : 0 < t) (hX : |X - a| ≤ K / t)
    (hY : |Y - b| ≤ K' / t) : |(X - Y) / t - (a - b) / t| ≤ (K + K') / t ^ 2 := by
  have e : (X - Y) / t - (a - b) / t = ((X - a) - (Y - b)) / t := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos ht]
  calc |(X - a) - (Y - b)| / t ≤ (|X - a| + |Y - b|) / t := by gcongr; exact abs_sub _ _
    _ ≤ (K / t + K' / t) / t := by gcongr
    _ = (K + K') / t ^ 2 := by
        field_simp

/-- `|t²Cov[x³, x²] − (−15α/λ⁴)/t| ≤ K/t²`. -/
theorem pairCov32_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 3) (fun x => x ^ 2) - (-(15 * alpha / lam ^ 4)) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := thirdMoment_lead hlam hgamma hdisc
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := secondMoment_lead hlam hgamma hdisc
  refine ⟨K₅ + (K₃ * |1 / lam| + K₂ * |-(5 * alpha / (2 * lam ^ 3))| + K₃ * K₂), T₅ + T₃ + T₂,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hprod := Laplace.OneD.rate_mul ht1 hK₃ hK₂ (h₃ (by linarith)) (h₂ (by linarith))
  rw [Laplace.OneD.gibbsCov_pow_pow]
  simp only [show (3 + 2 : ℕ) = 5 from rfl]
  set M₅ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 5)
  set M₃ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3)
  set M₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2)
  have e : t ^ 2 * (M₅ - M₃ * M₂) = (t ^ 3 * M₅ - (t ^ 2 * M₃) * (t * M₂)) / t := by
    field_simp
  have e' : -(15 * alpha / lam ^ 4) = -(35 * alpha / (2 * lam ^ 4)) -
      -(5 * alpha / (2 * lam ^ 3)) * (1 / lam) := by
    field_simp
    ring
  rw [e, e']
  exact sub_div_rate ht0 (h₅ (by linarith)) hprod

/-- `|t²Cov[x⁴, x²] − (12/λ³)/t| ≤ K/t²`. -/
theorem pairCov42_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 4) (fun x => x ^ 2) - (12 / lam ^ 3) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₆, T₆, hK₆, hT₆, h₆⟩ := sixthMoment_lead hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_lead hlam hgamma hdisc
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := secondMoment_lead hlam hgamma hdisc
  refine ⟨K₆ + (K₄ * |1 / lam| + K₂ * |3 / lam ^ 2| + K₄ * K₂), T₆ + T₄ + T₂,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hprod := Laplace.OneD.rate_mul ht1 hK₄ hK₂ (h₄ (by linarith)) (h₂ (by linarith))
  rw [Laplace.OneD.gibbsCov_pow_pow]
  simp only [show (4 + 2 : ℕ) = 6 from rfl]
  set M₆ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 6)
  set M₄ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4)
  set M₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2)
  have e : t ^ 2 * (M₆ - M₄ * M₂) = (t ^ 3 * M₆ - (t ^ 2 * M₄) * (t * M₂)) / t := by
    field_simp
  have e' : (12 / lam ^ 3 : ℝ) = 15 / lam ^ 3 - 3 / lam ^ 2 * (1 / lam) := by
    field_simp
    ring
  rw [e, e']
  exact sub_div_rate ht0 (h₆ (by linarith)) hprod

/-- `|t²Cov[x³, x] − 3/λ² − (45α²/(4λ⁵) − 4γ/λ⁴)/t| ≤ K/t²`. -/
theorem pairCov31_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 3) (fun x => x) - 3 / lam ^ 2 -
        (45 * alpha ^ 2 / (4 * lam ^ 5) - 4 * gamma / lam ^ 4) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_order2_rate hlam hgamma hdisc
  obtain ⟨K₃, T₃, hK₃, hT₃, h₃⟩ := thirdMoment_lead hlam hgamma hdisc
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := Laplace.OneD.mean_anharmonic_O2_rate hlam hgamma hdisc
  refine ⟨K₄ + (K₃ * |-alpha / (2 * lam ^ 2)| + K₁ * |-(5 * alpha / (2 * lam ^ 3))| + K₃ * K₁),
    T₄ + T₃ + T₁, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hprod := Laplace.OneD.rate_mul ht1 hK₃ hK₁ (h₃ (by linarith)) (h₁ (by linarith))
  have e₄ := h₄ (t := t) (by linarith)
  rw [Laplace.OneD.gibbsCov_pow_id]
  simp only [show (3 + 1 : ℕ) = 4 from rfl]
  set M₄ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4)
  set M₃ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3)
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x)
  have e : t ^ 2 * (M₄ - M₃ * M₁) - 3 / lam ^ 2 -
      (45 * alpha ^ 2 / (4 * lam ^ 5) - 4 * gamma / lam ^ 4) / t =
      (t ^ 2 * M₄ - 3 / lam ^ 2 - (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t) -
        ((t ^ 2 * M₃) * (t * M₁) -
          -(5 * alpha / (2 * lam ^ 3)) * (-alpha / (2 * lam ^ 2))) / t := by
    field_simp
    ring
  rw [e]
  calc |_| ≤ |t ^ 2 * M₄ - 3 / lam ^ 2 -
          (25 * alpha ^ 2 / (2 * lam ^ 5) - 4 * gamma / lam ^ 4) / t| +
        |((t ^ 2 * M₃) * (t * M₁) -
          -(5 * alpha / (2 * lam ^ 3)) * (-alpha / (2 * lam ^ 2))) / t| :=
          abs_sub _ _
    _ ≤ K₄ / t ^ 2 + ((K₃ * |-alpha / (2 * lam ^ 2)| + K₁ * |-(5 * alpha / (2 * lam ^ 3))| +
          K₃ * K₁) / t) / t := by
          gcongr
          rw [abs_div, abs_of_pos ht0]
          gcongr
    _ = (K₄ + (K₃ * |-alpha / (2 * lam ^ 2)| + K₁ * |-(5 * alpha / (2 * lam ^ 3))| +
          K₃ * K₁)) / t ^ 2 := by
          field_simp

/-- `|t²Cov[x⁴, x] − (−16α/λ⁴)/t| ≤ K/t²`. -/
theorem pairCov41_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 4) (fun x => x) - (-(16 * alpha / lam ^ 4)) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₅, T₅, hK₅, hT₅, h₅⟩ := fifthMoment_lead hlam hgamma hdisc
  obtain ⟨K₄, T₄, hK₄, hT₄, h₄⟩ := fourthMoment_lead hlam hgamma hdisc
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := Laplace.OneD.mean_anharmonic_O2_rate hlam hgamma hdisc
  refine ⟨K₅ + (K₄ * |-alpha / (2 * lam ^ 2)| + K₁ * |3 / lam ^ 2| + K₄ * K₁), T₅ + T₄ + T₁,
    by positivity, by linarith, fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hprod := Laplace.OneD.rate_mul ht1 hK₄ hK₁ (h₄ (by linarith)) (h₁ (by linarith))
  rw [Laplace.OneD.gibbsCov_pow_id]
  simp only [show (4 + 1 : ℕ) = 5 from rfl]
  set M₅ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 5)
  set M₄ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4)
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x)
  have e : t ^ 2 * (M₅ - M₄ * M₁) = (t ^ 3 * M₅ - (t ^ 2 * M₄) * (t * M₁)) / t := by
    field_simp
  have e' : -(16 * alpha / lam ^ 4) = -(35 * alpha / (2 * lam ^ 4)) -
      3 / lam ^ 2 * (-alpha / (2 * lam ^ 2)) := by
    field_simp
    ring
  rw [e, e']
  exact sub_div_rate ht0 (h₅ (by linarith)) hprod

end Pairs

/-! ### eq:covK to second order -/

section Main

variable {lam alpha gamma : ℝ}
variable (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
include hlam hgamma hdisc

/-- **eq:covK to second order, quadratic probe**: `|t²Cov[ℓ, x²] − 1/λ − C'_sq/t| ≤ K/t²`,
`C'_sq = 5α²/(2λ⁴) − γ/λ³ = 2B₂`. -/
theorem covK_sq_order2_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ 2) - 1 / lam -
        covKCoeff2Sq lam alpha gamma / t| ≤ K / t ^ 2 := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ :=
    Laplace.OneD.secondMoment_anharmonic_order3_rate hlam hgamma hdisc
  obtain ⟨K₃₂, T₃₂, hK₃₂, hT₃₂, h₃₂⟩ := pairCov32_rate hlam hgamma hdisc
  obtain ⟨K₄₂, T₄₂, hK₄₂, hT₄₂, h₄₂⟩ := pairCov42_rate hlam hgamma hdisc
  refine ⟨K₂ + |alpha| / 12 * K₃₂ + gamma / 24 * K₄₂, T₂ + T₃₂ + T₄₂, by positivity,
    by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e₂ := h₂ (t := t) (by linarith)
  rw [secondMoment_coeff_eq hlam] at e₂
  have e₃₂ := h₃₂ (t := t) (by linarith)
  have e₄₂ := h₄₂ (t := t) (by linarith)
  rw [covK_sq_stein hlam hgamma hdisc ht0]
  set M₂ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 2)
  set P₃₂ := _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3) (fun x => x ^ 2)
  set P₄₂ := _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4) (fun x => x ^ 2)
  have key : t * M₂ - alpha / 12 * (t ^ 2 * P₃₂) - gamma / 24 * (t ^ 2 * P₄₂) - 1 / lam -
      covKCoeff2Sq lam alpha gamma / t =
      (t * M₂ - 1 / lam - (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)) -
        alpha / 12 * (t ^ 2 * P₃₂ - (-(15 * alpha / lam ^ 4)) / t) -
        gamma / 24 * (t ^ 2 * P₄₂ - (12 / lam ^ 3) / t) := by
    unfold covKCoeff2Sq
    field_simp
    ring
  rw [key]
  calc |_| ≤ |t * M₂ - 1 / lam -
          (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)| +
        |alpha / 12 * (t ^ 2 * P₃₂ - (-(15 * alpha / lam ^ 4)) / t)| +
        |gamma / 24 * (t ^ 2 * P₄₂ - (12 / lam ^ 3) / t)| :=
          (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = |t * M₂ - 1 / lam - (5 * alpha ^ 2 / (4 * lam ^ 3) - gamma / (2 * lam ^ 2)) / (lam * t)| +
        |alpha| / 12 * |t ^ 2 * P₃₂ - (-(15 * alpha / lam ^ 4)) / t| +
        gamma / 24 * |t ^ 2 * P₄₂ - (12 / lam ^ 3) / t| := by
          rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12), abs_mul,
            abs_of_pos (by positivity : (0 : ℝ) < gamma / 24)]
    _ ≤ K₂ / t ^ 2 + |alpha| / 12 * (K₃₂ / t ^ 2) + gamma / 24 * (K₄₂ / t ^ 2) := by gcongr
    _ = (K₂ + |alpha| / 12 * K₃₂ + gamma / 24 * K₄₂) / t ^ 2 := by ring

/-- **eq:covK to second order, linear probe**: `|t²Cov[ℓ, x] + α/(2λ²) − C'_lin/t| ≤ K/t²`,
`C'_lin = −5α³/(4λ⁵) + 4αγ/(3λ⁴) = 2B₁`. -/
theorem covK_lin_order2_rate :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => x) + alpha / (2 * lam ^ 2) -
        covKCoeff2Lin lam alpha gamma / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := mean_anharmonic_order2_rate hlam hgamma hdisc
  obtain ⟨K₃₁, T₃₁, hK₃₁, hT₃₁, h₃₁⟩ := pairCov31_rate hlam hgamma hdisc
  obtain ⟨K₄₁, T₄₁, hK₄₁, hT₄₁, h₄₁⟩ := pairCov41_rate hlam hgamma hdisc
  refine ⟨1 / 2 * K₁ + |alpha| / 12 * K₃₁ + gamma / 24 * K₄₁, T₁ + T₃₁ + T₄₁, by positivity,
    by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e₁ := h₁ (t := t) (by linarith)
  have e₃₁ := h₃₁ (t := t) (by linarith)
  have e₄₁ := h₄₁ (t := t) (by linarith)
  rw [covK_lin_stein hlam hgamma hdisc ht0]
  set M₁ := _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x => x)
  set P₃₁ := _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 3) (fun x => x)
  set P₄₁ := _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
    (fun x => x ^ 4) (fun x => x)
  have key : 1 / 2 * (t * M₁) - alpha / 12 * (t ^ 2 * P₃₁) - gamma / 24 * (t ^ 2 * P₄₁) +
      alpha / (2 * lam ^ 2) - covKCoeff2Lin lam alpha gamma / t =
      1 / 2 * (t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t) -
        alpha / 12 * (t ^ 2 * P₃₁ - 3 / lam ^ 2 -
          (45 * alpha ^ 2 / (4 * lam ^ 5) - 4 * gamma / lam ^ 4) / t) -
        gamma / 24 * (t ^ 2 * P₄₁ - (-(16 * alpha / lam ^ 4)) / t) := by
    unfold covKCoeff2Lin meanCoeff2
    field_simp
    ring
  rw [key]
  calc |_| ≤ |1 / 2 * (t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t)| +
        |alpha / 12 * (t ^ 2 * P₃₁ - 3 / lam ^ 2 -
          (45 * alpha ^ 2 / (4 * lam ^ 5) - 4 * gamma / lam ^ 4) / t)| +
        |gamma / 24 * (t ^ 2 * P₄₁ - (-(16 * alpha / lam ^ 4)) / t)| :=
          (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = 1 / 2 * |t * M₁ + alpha / (2 * lam ^ 2) - meanCoeff2 lam alpha gamma / t| +
        |alpha| / 12 * |t ^ 2 * P₃₁ - 3 / lam ^ 2 -
          (45 * alpha ^ 2 / (4 * lam ^ 5) - 4 * gamma / lam ^ 4) / t| +
        gamma / 24 * |t ^ 2 * P₄₁ - (-(16 * alpha / lam ^ 4)) / t| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_mul, abs_div,
            abs_of_pos (by norm_num : (0 : ℝ) < 12), abs_mul,
            abs_of_pos (by positivity : (0 : ℝ) < gamma / 24)]
    _ ≤ 1 / 2 * (K₁ / t ^ 2) + |alpha| / 12 * (K₃₁ / t ^ 2) + gamma / 24 * (K₄₁ / t ^ 2) := by
          gcongr
    _ = (1 / 2 * K₁ + |alpha| / 12 * K₃₁ + gamma / 24 * K₄₁) / t ^ 2 := by ring

/-- **eq:covK to second order for the probe `ψ = (B/2)x² + bx`**:
`|t²Cov[ℓ, ψ] − (B/(2λ) − bα/(2λ²)) − (B C'_sq/2 + b C'_lin)/t| ≤ K/t²`. -/
theorem covK_order2_rate (B b : ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => B / 2 * x ^ 2 + b * x) -
        (B / (2 * lam) - b * alpha / (2 * lam ^ 2)) -
        (B / 2 * covKCoeff2Sq lam alpha gamma + b * covKCoeff2Lin lam alpha gamma) / t| ≤
        K / t ^ 2 := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := covK_sq_order2_rate hlam hgamma hdisc
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ := covK_lin_order2_rate hlam hgamma hdisc
  refine ⟨|B| / 2 * K₂ + |b| * K₁, T₁ + T₂, by positivity, by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have e2 := h₂ (t := t) (by linarith)
  have e1 := h₁ (t := t) (by linarith)
  set L := anharmonicPotential lam alpha gamma with hL
  have hm : ∀ k : ℕ, Integrable (fun x => x ^ k * Real.exp (-(t * L x))) := fun k =>
    integrable_pow_exp' hlam hgamma hdisc ht0 k
  have hLm : ∀ k : ℕ, Integrable (fun x => L x * x ^ k * Real.exp (-(t * L x))) := fun k =>
    (((hm (k + 2)).const_mul (lam / 2)).add (((hm (k + 3)).const_mul (alpha / 6)).add
      ((hm (k + 4)).const_mul (gamma / 24)))).congr (Eventually.of_forall fun x => by
        simp only [Pi.add_apply, hL, anharmonicPotential, pow_add]
        ring)
  have i1 : Integrable (fun x => B / 2 * x ^ 2 * Real.exp (-(t * L x))) :=
    ((hm 2).const_mul (B / 2)).congr (Eventually.of_forall fun x => by ring)
  have i2 : Integrable (fun x => b * x * Real.exp (-(t * L x))) :=
    ((hm 1).const_mul b).congr (Eventually.of_forall fun x => by simp only [pow_one]; ring)
  have i1L : Integrable (fun x => L x * (B / 2 * x ^ 2) * Real.exp (-(t * L x))) :=
    ((hLm 2).const_mul (B / 2)).congr (Eventually.of_forall fun x => by ring)
  have i2L : Integrable (fun x => L x * (b * x) * Real.exp (-(t * L x))) :=
    ((hLm 1).const_mul b).congr (Eventually.of_forall fun x => by simp only [pow_one]; ring)
  rw [Laplace.gibbsCov_add_right L t L _ _ i1 i2 i1L i2L, Laplace.gibbsCov_smul_right,
    Laplace.gibbsCov_smul_right]
  set X := _root_.Laplace.gibbsCov L t L (fun x => x ^ 2) with hX
  set Y := _root_.Laplace.gibbsCov L t L (fun x => x) with hY
  have key : t ^ 2 * (B / 2 * X + b * Y) - (B / (2 * lam) - b * alpha / (2 * lam ^ 2)) -
      (B / 2 * covKCoeff2Sq lam alpha gamma + b * covKCoeff2Lin lam alpha gamma) / t =
      B / 2 * (t ^ 2 * X - 1 / lam - covKCoeff2Sq lam alpha gamma / t) +
        b * (t ^ 2 * Y + alpha / (2 * lam ^ 2) - covKCoeff2Lin lam alpha gamma / t) := by
    field_simp
    ring
  rw [key]
  calc |B / 2 * (t ^ 2 * X - 1 / lam - covKCoeff2Sq lam alpha gamma / t) +
        b * (t ^ 2 * Y + alpha / (2 * lam ^ 2) - covKCoeff2Lin lam alpha gamma / t)|
      ≤ |B / 2 * (t ^ 2 * X - 1 / lam - covKCoeff2Sq lam alpha gamma / t)| +
        |b * (t ^ 2 * Y + alpha / (2 * lam ^ 2) - covKCoeff2Lin lam alpha gamma / t)| :=
          abs_add_le _ _
    _ = |B| / 2 * |t ^ 2 * X - 1 / lam - covKCoeff2Sq lam alpha gamma / t| +
        |b| * |t ^ 2 * Y + alpha / (2 * lam ^ 2) - covKCoeff2Lin lam alpha gamma / t| := by
          rw [abs_mul, abs_div, abs_two, abs_mul]
    _ ≤ |B| / 2 * (K₂ / t ^ 2) + |b| * (K₁ / t ^ 2) := by gcongr
    _ = (|B| / 2 * K₂ + |b| * K₁) / t ^ 2 := by ring

end Main

end Laplace.Multi
