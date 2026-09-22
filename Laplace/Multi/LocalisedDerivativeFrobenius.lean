/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedFrobenius

/-!
# Frobenius discrepancies of the localised covariance's derivative

On E2's exact localised measure, with `C(t)` the centred covariance, `S(t) = (tH + gI)⁻¹`,
`vᵢ` the `O(S²)` variance coefficients, `wᵢ = vᵢ + g/λᵢ²`, `V = Q diag(vᵢ) Qᵀ`, `W = V + gH⁻²`:

* `‖−∂ₜC(t) − H⁻¹/t²‖_F² = 4‖V‖_F²/t⁶ + O(t⁻⁷)`;
* `−∂ₜS(t) = Q diag(λᵢ/(tλᵢ + g)²) Qᵀ` exactly, and `‖∂ₜ(C − S)‖_F² = 4‖W‖_F²/t⁶ + O(t⁻⁷)` — the
  derivative reading of `‖C − S‖_F² = ‖W‖_F²/t⁴ + O(t⁻⁵)`, established from the derivative
  expansions (`LocalisedCentredDerivative`), not by differentiating a remainder;
* the relative form `t² ‖−∂ₜC − H⁻¹/t²‖_F²/‖H⁻¹/t²‖_F² → 4∑vᵢ²/∑λᵢ⁻²` and the two-sided bounds.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section Rates

/-- The `t³` wrapper of `frobenius_conj_rate`. -/
theorem frobenius_conj_rate_cubic {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1)
    (f : Fin d → ℝ → ℝ) (w : Fin d → ℝ)
    (h : ∀ i, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |t ^ 3 * f i t - w i| ≤ K / t) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 6 * ∑ j, ∑ k, (∑ i, Q j i * Q k i * f i t) ^ 2 - ∑ i, w i ^ 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h'⟩ := frobenius_conj_rate hQ (fun i t => t * f i t) w fun i => by
    obtain ⟨K, T, hK, hT, h⟩ := h i
    exact ⟨K, T, hK, hT, fun {t} ht => by
      have e : t ^ 2 * (t * f i t) = t ^ 3 * f i t := by ring
      rw [e]
      exact h ht⟩
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have e : t ^ 6 * ∑ j, ∑ k, (∑ i, Q j i * Q k i * f i t) ^ 2 =
      t ^ 4 * ∑ j, ∑ k, (∑ i, Q j i * Q k i * (t * f i t)) ^ 2 := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [show ∑ i, Q j i * Q k i * (t * f i t) = t * ∑ i, Q j i * Q k i * f i t by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  rw [e]
  exact h' ht

/-- `|t²D − 1/λ − 2v/t| ≤ K/t² ⟹ |t³(D − 1/(λt²)) − 2v| ≤ K/t`. -/
theorem deriv_coord_scaled {t D lam v K : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (h : |t ^ 2 * D - 1 / lam - 2 * v / t| ≤ K / t ^ 2) :
    |t ^ 3 * (D - 1 / lam / t ^ 2) - 2 * v| ≤ K / t := by
  have ht' : t ≠ 0 := ht.ne'
  have hl : lam ≠ 0 := hlam.ne'
  have e : t ^ 3 * (D - 1 / lam / t ^ 2) - 2 * v = t * (t ^ 2 * D - 1 / lam - 2 * v / t) := by
    field_simp
  rw [e, abs_mul, abs_of_pos ht]
  calc t * |t ^ 2 * D - 1 / lam - 2 * v / t| ≤ t * (K / t ^ 2) := by gcongr
    _ = K / t := by field_simp

/-- `|t³(λ/(tλ + g)² − 1/(λt²)) + 2g/λ²| ≤ (g²(3λ + 2g)/λ⁴)/t` for `t ≥ 1`: the resolvent's
derivative against the unlocalised `1/(λt²)`. -/
theorem resolvent_deriv_coord_rate {lam g t : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) (ht : 1 ≤ t) :
    |t ^ 3 * (lam / (t * lam + g) ^ 2 - 1 / lam / t ^ 2) + 2 * g / lam ^ 2| ≤
      g ^ 2 * (3 * lam + 2 * g) / lam ^ 4 / t := by
  have ht0 : 0 < t := by linarith
  have hden : 0 < t * lam + g := by positivity
  have e : t ^ 3 * (lam / (t * lam + g) ^ 2 - 1 / lam / t ^ 2) + 2 * g / lam ^ 2 =
      g ^ 2 * (3 * t * lam + 2 * g) / (lam ^ 2 * (t * lam + g) ^ 2) := by
    field_simp
    ring
  rw [e, abs_of_nonneg (by positivity)]
  have h1 : g ^ 2 * (3 * t * lam + 2 * g) / (lam ^ 2 * (t * lam + g) ^ 2) ≤
      g ^ 2 * (3 * t * lam + 2 * g) / (lam ^ 2 * (t * lam) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
    linarith
  have h2 : g ^ 2 * (3 * t * lam + 2 * g) / (lam ^ 2 * (t * lam) ^ 2) ≤
      g ^ 2 * (t * (3 * lam + 2 * g)) / (lam ^ 2 * (t * lam) ^ 2) := by
    gcongr
    nlinarith
  refine h1.trans (h2.trans (le_of_eq ?_))
  field_simp

/-- Combining the two coordinate rates: `|t³(D − λ/(tλ + g)²) − 2(v + g/λ²)| ≤ K'/t`. -/
theorem deriv_coord_resolvent_scaled {t D lam g v K : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) (ht : 1 ≤ t)
    (h : |t ^ 3 * (D - 1 / lam / t ^ 2) - 2 * v| ≤ K / t) :
    |t ^ 3 * (D - lam / (t * lam + g) ^ 2) - 2 * (v + g / lam ^ 2)| ≤
      (K + g ^ 2 * (3 * lam + 2 * g) / lam ^ 4) / t := by
  have e : t ^ 3 * (D - lam / (t * lam + g) ^ 2) - 2 * (v + g / lam ^ 2) =
      (t ^ 3 * (D - 1 / lam / t ^ 2) - 2 * v) -
        (t ^ 3 * (lam / (t * lam + g) ^ 2 - 1 / lam / t ^ 2) + 2 * g / lam ^ 2) := by ring
  rw [e, add_div]
  exact (abs_sub _ _).trans (add_le_add h (resolvent_deriv_coord_rate hlam hg ht))

end Rates

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- **The resolvent's derivative, entrywise**: `d/dt (locS g H t)ⱼₖ = −∑ᵢ QⱼᵢQₖᵢ λᵢ/(tλᵢ + g)²`. -/
theorem hasDerivAt_locS_entry (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j k : Fin d) :
    HasDerivAt (fun s => locS g (Q * diagonal lam * Qᵀ) s j k)
      (-∑ i, Q j i * Q k i * (lam i / (t * lam i + g) ^ 2)) t := by
  have heq : (fun s => locS g (Q * diagonal lam * Qᵀ) s j k) =ᶠ[𝓝 t]
      fun s => ∑ i, Q j i * Q k i * (1 / (s * lam i + g)) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => locS_rot_apply hQ hlam hg hs j k
  have h : HasDerivAt (fun s => ∑ i, Q j i * Q k i * (1 / (s * lam i + g)))
      (∑ i, Q j i * Q k i * (-(lam i) / (t * lam i + g) ^ 2)) t := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hd : t * lam i + g ≠ 0 := by have := hlam i; positivity
    have h1 : HasDerivAt (fun s => s * lam i + g) (lam i) t := by
      simpa using ((hasDerivAt_id t).mul_const (lam i)).add_const g
    simp only [one_div]
    exact (h1.inv hd).const_mul _
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `−∂ₜ S(t)ⱼₖ = (Q diag(λᵢ/(tλᵢ + g)²) Qᵀ)ⱼₖ`. -/
theorem neg_deriv_locS_entry (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j k : Fin d) :
    -deriv (fun s => locS g (Q * diagonal lam * Qᵀ) s j k) t =
      (Q * diagonal (fun i => lam i / (t * lam i + g) ^ 2) * Qᵀ) j k := by
  rw [(hasDerivAt_locS_entry hQ hlam hg ht j k).deriv, neg_neg, conj_diagonal_entry]

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- `−∂ₜCⱼₖ − (H⁻¹)ⱼₖ/t² = ∑ᵢ QⱼᵢQₖᵢ (Dᵢ − 1/(λᵢt²))`. -/
theorem localisedCov_neg_deriv_sub_inv_entry (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) (j k : Fin d) :
    -deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => w j) (fun w => w k)) t -
      (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2 =
      ∑ i, Q j i * Q k i * (locCentredD Q c lam alpha gamma g w₀ t i - 1 / lam i / t ^ 2) := by
  rw [(hasDerivAt_localised_cov_coord hlam hgamma hdisc hQ c w₀ hg ht j k).deriv, neg_neg,
    conj_diagonal_entry, Finset.sum_div, ← Finset.sum_sub_distrib]
  unfold locCentredD
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `−∂ₜCⱼₖ + ∂ₜSⱼₖ = ∑ᵢ QⱼᵢQₖᵢ (Dᵢ − λᵢ/(tλᵢ + g)²)`. -/
theorem localisedCov_neg_deriv_add_deriv_locS_entry (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (j k : Fin d) :
    -deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => w j) (fun w => w k)) t +
      deriv (fun s => locS g (Q * diagonal lam * Qᵀ) s j k) t =
      ∑ i, Q j i * Q k i *
        (locCentredD Q c lam alpha gamma g w₀ t i - lam i / (t * lam i + g) ^ 2) := by
  rw [(hasDerivAt_localised_cov_coord hlam hgamma hdisc hQ c w₀ hg ht j k).deriv, neg_neg,
    (hasDerivAt_locS_entry hQ hlam hg ht j k).deriv, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  unfold locCentredD
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **A: the derivative's Frobenius discrepancy from the unlocalised Laplace derivative**:
`|t⁶ ‖−∂ₜC(t) − H⁻¹/t²‖_F² − 4∑ᵢ vᵢ²| ≤ K/t`, i.e. `‖−∂ₜC − H⁻¹/t²‖_F² = 4‖V‖_F²/t⁶ + O(t⁻⁷)`. -/
theorem localisedCov_neg_deriv_frobenius_inv_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 6 * ∑ j, ∑ k,
          (-deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
            (fun w => w j) (fun w => w k)) t -
          (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2 -
        4 * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := frobenius_conj_rate_cubic hQ
    (fun i t => locCentredD Q c lam alpha gamma g w₀ t i - 1 / lam i / t ^ 2)
    (fun i => 2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) fun i => by
      obtain ⟨K, T, hK, hT, h⟩ := localisedVar_neg_deriv_order2_rate hlam hgamma hdisc hQ c w₀ hg i
      exact ⟨K, T, hK, hT, fun {t} ht => deriv_coord_scaled (hlam i) (by linarith) (h ht)⟩
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  simp only [localisedCov_neg_deriv_sub_inv_entry hlam hgamma hdisc hQ c w₀ hg ht0]
  have e : (4 : ℝ) * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2 =
      ∑ i, (2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact h ht

/-- **B: the derivative reading of `‖C − S‖_F² = ‖W‖_F²/t⁴ + O(t⁻⁵)`**:
`|t⁶ ‖−∂ₜC(t) + ∂ₜS(t)‖_F² − 4∑ᵢ (vᵢ + g/λᵢ²)²| ≤ K/t`, i.e. `‖∂ₜ(C − S)‖_F² = 4‖W‖_F²/t⁶ + O(t⁻⁷)`,
from the derivative expansions (not by differentiating the remainder). -/
theorem localisedCov_neg_deriv_frobenius_locS_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 6 * ∑ j, ∑ k,
          (-deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
            (fun w => w j) (fun w => w k)) t +
          deriv (fun s => locS g (Q * diagonal lam * Qᵀ) s j k) t) ^ 2 -
        4 * ∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := frobenius_conj_rate_cubic hQ
    (fun i t => locCentredD Q c lam alpha gamma g w₀ t i - lam i / (t * lam i + g) ^ 2)
    (fun i => 2 * covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) fun i => by
      obtain ⟨K, T, hK, hT, h⟩ := localisedVar_neg_deriv_order2_rate hlam hgamma hdisc hQ c w₀ hg i
      refine ⟨K + g ^ 2 * (3 * lam i + 2 * g) / lam i ^ 4, T, by have := hlam i; positivity, hT,
        fun {t} ht => ?_⟩
      exact deriv_coord_resolvent_scaled (hlam i) hg (hT.trans ht)
        (deriv_coord_scaled (hlam i) (by linarith) (h ht))
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  simp only [localisedCov_neg_deriv_add_deriv_locS_entry hlam hgamma hdisc hQ c w₀ hg ht0]
  have e : (4 : ℝ) * ∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2 =
      ∑ i, (2 * covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact h ht

omit hlam hgamma hdisc in
/-- `‖H⁻¹/t²‖_F² = (∑ᵢ λᵢ⁻²)/t⁴` exactly. -/
theorem inv_div_sq_frobenius (hQ : Qᵀ * Q = 1) (t : ℝ) :
    ∑ j, ∑ k, ((Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2 =
      (∑ i, 1 / lam i ^ 2) / t ^ 4 := by
  have h : ∀ j k, ((Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2 =
      (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k ^ 2 / t ^ 4 := fun j k => by
    rw [div_pow]
    ring
  simp only [h, ← Finset.sum_div, frobenius_conj_diagonal_frob hQ]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [div_pow, one_pow]

/-- **C: the relative form**: `|t² ‖−∂ₜC − H⁻¹/t²‖_F²/‖H⁻¹/t²‖_F² − 4∑ᵢvᵢ²/∑ᵢλᵢ⁻²| ≤ K/t` in
positive dimension. -/
theorem localisedCov_neg_deriv_frobenius_relative_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hd : 0 < d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * ((∑ j, ∑ k,
          (-deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
            (fun w => w j) (fun w => w k)) t -
          (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2) /
          ∑ j, ∑ k, ((Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2) -
        (4 * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) /
          ∑ i, 1 / lam i ^ 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ :=
    localisedCov_neg_deriv_frobenius_inv_rate hlam hgamma hdisc hQ c w₀ hg
  have hL : 0 < ∑ i, 1 / lam i ^ 2 := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    exact Finset.sum_pos (fun i _ => by have := hlam i; positivity) Finset.univ_nonempty
  refine ⟨K / ∑ i, 1 / lam i ^ 2, T, by positivity, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [inv_div_sq_frobenius hQ t]
  have e : t ^ 2 * ((∑ j, ∑ k,
      (-deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => w j) (fun w => w k)) t -
      (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2) /
      ((∑ i, 1 / lam i ^ 2) / t ^ 4)) -
      (4 * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) /
        ∑ i, 1 / lam i ^ 2 =
      (t ^ 6 * ∑ j, ∑ k,
        (-deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => w j) (fun w => w k)) t -
        (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2 -
        4 * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) /
        ∑ i, 1 / lam i ^ 2 := by
    field_simp
  rw [e, abs_div, abs_of_pos hL, div_right_comm]
  exact div_le_div_of_nonneg_right (h ht) hL.le

/-- **D: two-sided bounds**: when `∑ᵢ vᵢ² > 0`, eventually
`2∑vᵢ² ≤ t⁶ ‖−∂ₜC(t) − H⁻¹/t²‖_F² ≤ 6∑vᵢ²` — exact order `t⁻³` in Frobenius norm. -/
theorem localisedCov_neg_deriv_frobenius_two_sided (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g)
    (hv : 0 < ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      2 * (∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) ≤
        t ^ 6 * ∑ j, ∑ k,
          (-deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
            (fun w => w j) (fun w => w k)) t -
          (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2 ∧
      t ^ 6 * ∑ j, ∑ k,
          (-deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
            (fun w => w j) (fun w => w k)) t -
          (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t ^ 2) ^ 2 ≤
        6 * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ :=
    localisedCov_neg_deriv_frobenius_inv_rate hlam hgamma hdisc hQ c w₀ hg
  have hA :
      0 < 4 * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2 := by
    positivity
  have h0 : 0 ≤ 2 * K /
      (4 * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) := by
    positivity
  refine ⟨T + 2 * K /
      (4 * ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2),
    by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨h1, h2⟩ := two_sided_of_rate hA ht0 (by linarith) (h (by linarith))
  constructor <;> linarith

end Multi

end Laplace.Multi
