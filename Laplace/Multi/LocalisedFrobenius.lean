/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedTraceProbe

/-!
# Frobenius discrepancies of the localised covariance

On E2's exact localised measure, with `C(t)` the centred covariance, `S(t) = (tH + gI)⁻¹`
the note's Gaussian-prior resolvent, `vᵢ` the `O(S²)` variance coefficients and
`wᵢ = vᵢ + g/λᵢ²`:

* `‖C(t) − S(t)‖_F² = (∑ᵢ wᵢ²)/t⁴ + O(t⁻⁵)` — the note's `O(S²)` remainder, invariantly;
* changing the reference covariance to the unlocalised `H⁻¹/t`:
  `‖C(t) − H⁻¹/t‖_F² = (∑ᵢ vᵢ²)/t⁴ + O(t⁻⁵)` (the explicit resolvent correction `gH⁻²`
  cancels; the localiser dependence inside `vᵢ` remains);
* the relative discrepancy `t² ‖C − S‖_F²/‖S‖_F² → (∑ᵢ wᵢ²)/(∑ᵢ λᵢ⁻²)` at rate `O(1/t)`;
* when `∑ᵢ wᵢ² > 0`, the two-sided bounds `∑wᵢ²/(2t⁴) ≤ ‖C − S‖_F² ≤ 3∑wᵢ²/(2t⁴)`
  eventually.

All from tide 74's per-coordinate second-order variance rates, one scalar square lemma, finite-sum
transport and the orthogonal invariance `‖Q diag(a) Qᵀ‖_F² = ∑ᵢ aᵢ²`.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section Algebra

variable {d : ℕ}

theorem frobenius_eq_trace (X : Matrix (Fin d) (Fin d) ℝ) :
    ∑ j, ∑ k, X j k ^ 2 = Matrix.trace (X * Xᵀ) := by
  rw [← sum_sum_eq_trace]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- `‖Q diag(a) Qᵀ‖_F² = ∑ᵢ aᵢ²` for `QᵀQ = 1`. -/
theorem frobenius_conj_diagonal_frob {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1)
    (a : Fin d → ℝ) :
    ∑ j, ∑ k, (Q * diagonal a * Qᵀ) j k ^ 2 = ∑ i, a i ^ 2 := by
  rw [frobenius_eq_trace, conj_diagonal_transpose, trace_mul_conj_diagonal, conj_conj hQ]
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.diagonal_apply_eq]; ring

end Algebra

section Rates

/-- `|y − w| ≤ K/t ⟹ |y² − w²| ≤ (2|w|K + K²)/t` for `t ≥ 1`. -/
theorem sq_rate {t y w K : ℝ} (ht : 1 ≤ t) (hK : 0 ≤ K) (h : |y - w| ≤ K / t) :
    |y ^ 2 - w ^ 2| ≤ (2 * |w| * K + K ^ 2) / t := by
  have ht0 : 0 < t := by linarith
  have hKt : K / t ≤ K := div_le_self hK ht
  have hy : |y + w| ≤ 2 * |w| + K := by
    calc |y + w| = |(y - w) + 2 * w| := by ring_nf
      _ ≤ |y - w| + |2 * w| := abs_add_le _ _
      _ ≤ K / t + 2 * |w| := by rw [abs_mul, abs_two]; gcongr
      _ ≤ 2 * |w| + K := by linarith
  calc |y ^ 2 - w ^ 2| = |y - w| * |y + w| := by rw [← abs_mul]; ring_nf
    _ ≤ (K / t) * (2 * |w| + K) := mul_le_mul h hy (abs_nonneg _) (by positivity)
    _ = (2 * |w| * K + K ^ 2) / t := by rw [div_mul_eq_mul_div]; ring

/-- `|x − w/t²| ≤ K/t³ ⟹ |t²x − w| ≤ K/t`. -/
theorem order3_to_scaled {t x w K : ℝ} (ht : 0 < t) (h : |x - w / t ^ 2| ≤ K / t ^ 3) :
    |t ^ 2 * x - w| ≤ K / t := by
  have ht' : t ≠ 0 := ht.ne'
  have e : t ^ 2 * x - w = t ^ 2 * (x - w / t ^ 2) := by field_simp
  rw [e, abs_mul, abs_of_pos (by positivity)]
  calc t ^ 2 * |x - w / t ^ 2| ≤ t ^ 2 * (K / t ^ 3) := by gcongr
    _ = K / t := by field_simp

/-- `|t·x − a − v/t| ≤ K/t² ⟹ |t²(x − a/t) − v| ≤ K/t`. -/
theorem order2_to_scaled {t x a v K : ℝ} (ht : 0 < t) (h : |t * x - a - v / t| ≤ K / t ^ 2) :
    |t ^ 2 * (x - a / t) - v| ≤ K / t := by
  have ht' : t ≠ 0 := ht.ne'
  have e : t ^ 2 * (x - a / t) - v = t * (t * x - a - v / t) := by field_simp
  rw [e, abs_mul, abs_of_pos ht]
  calc t * |t * x - a - v / t| ≤ t * (K / t ^ 2) := by gcongr
    _ = K / t := by field_simp

/-- `|a − a₀| ≤ kₐ/t`, `|b − L| ≤ k_b/t`, `L > 0`, `b ≥ L/2` ⟹
`|a/b − a₀/L| ≤ (2kₐ/L + 2|a₀|k_b/L²)/t`. -/
theorem ratio_rate {a b a₀ L ka kb t : ℝ} (hL : 0 < L) (hka : 0 ≤ ka) (hkb : 0 ≤ kb) (ht : 0 < t)
    (hb2 : L / 2 ≤ b) (ha : |a - a₀| ≤ ka / t) (hb : |b - L| ≤ kb / t) :
    |a / b - a₀ / L| ≤ (2 * ka / L + 2 * |a₀| * kb / L ^ 2) / t := by
  have hb0 : 0 < b := by linarith
  have e : a / b - a₀ / L = ((a - a₀) * L - a₀ * (b - L)) / (b * L) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (mul_pos hb0 hL)]
  have hnum : |(a - a₀) * L - a₀ * (b - L)| ≤ ka / t * L + |a₀| * (kb / t) := by
    calc |(a - a₀) * L - a₀ * (b - L)| ≤ |(a - a₀) * L| + |a₀ * (b - L)| := abs_sub _ _
      _ = |a - a₀| * L + |a₀| * |b - L| := by rw [abs_mul, abs_mul, abs_of_pos hL]
      _ ≤ ka / t * L + |a₀| * (kb / t) := by gcongr
  calc |(a - a₀) * L - a₀ * (b - L)| / (b * L) ≤ (ka / t * L + |a₀| * (kb / t)) / (L / 2 * L) := by
        gcongr
    _ = (2 * ka / L + 2 * |a₀| * kb / L ^ 2) / t := by
        field_simp

/-- `|x − A| ≤ K/t` with `A > 0` and `t ≥ 2K/A` gives `A/2 ≤ x ≤ 3A/2`. -/
theorem two_sided_of_rate {x A K t : ℝ} (hA : 0 < A) (ht0 : 0 < t)
    (ht : 2 * K / A ≤ t) (h : |x - A| ≤ K / t) : A / 2 ≤ x ∧ x ≤ 3 * A / 2 := by
  have h1 : 2 * K ≤ A * t := by
    have := (div_le_iff₀ hA).mp ht
    linarith
  have h2 : K / t ≤ A / 2 := by
    rw [div_le_iff₀ ht0]
    linarith
  have h3 := (abs_le.mp (h.trans h2))
  constructor <;> linarith [h3.1, h3.2]

/-- `|t²/(tλ + g)² − 1/λ²| ≤ (g(2λ + g)/λ⁴)/t` for `t ≥ 1`: the resolvent's squared entries. -/
theorem resolvent_sq_coord_rate {lam g t : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) (ht : 1 ≤ t) :
    |t ^ 2 / (t * lam + g) ^ 2 - 1 / lam ^ 2| ≤ g * (2 * lam + g) / lam ^ 4 / t := by
  have ht0 : 0 < t := by linarith
  have hden : 0 < t * lam + g := by positivity
  have e : t ^ 2 / (t * lam + g) ^ 2 - 1 / lam ^ 2 =
      -(g * (2 * t * lam + g)) / (lam ^ 2 * (t * lam + g) ^ 2) := by
    field_simp
    ring
  rw [e, abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
  have h1 : g * (2 * t * lam + g) / (lam ^ 2 * (t * lam + g) ^ 2) ≤
      g * (2 * t * lam + g) / (lam ^ 2 * (t * lam) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
    linarith
  have h2 : g * (2 * t * lam + g) / (lam ^ 2 * (t * lam) ^ 2) ≤
      g * (t * (2 * lam + g)) / (lam ^ 2 * (t * lam) ^ 2) := by
    gcongr
    nlinarith
  refine h1.trans (h2.trans (le_of_eq ?_))
  field_simp

end Rates

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- **Frobenius transport**: per-coordinate rates `|t² fᵢ(t) − wᵢ| ≤ K/t` give
`|t⁴ ∑ⱼₖ (∑ᵢ QⱼᵢQₖᵢ fᵢ(t))² − ∑ᵢ wᵢ²| ≤ K/t` for orthogonal `Q`. -/
theorem frobenius_conj_rate (hQ : Qᵀ * Q = 1) (f : Fin d → ℝ → ℝ) (w : Fin d → ℝ)
    (h : ∀ i, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |t ^ 2 * f i t - w i| ≤ K / t) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * ∑ j, ∑ k, (∑ i, Q j i * Q k i * f i t) ^ 2 - ∑ i, w i ^ 2| ≤ K / t := by
  have hent : ∀ j k, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * ∑ i, Q j i * Q k i * f i t - ∑ i, Q j i * Q k i * w i| ≤ K / t := fun j k => by
    obtain ⟨K, T, hK, hT, h'⟩ := sum_rate_div (fun i => Q j i * Q k i)
      (fun i t => t ^ 2 * f i t - w i) h
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    have key : t ^ 2 * ∑ i, Q j i * Q k i * f i t - ∑ i, Q j i * Q k i * w i =
        ∑ i, Q j i * Q k i * (t ^ 2 * f i t - w i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [key]
    exact h' ht
  have hsq : ∀ p : Fin d × Fin d, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * (∑ i, Q p.1 i * Q p.2 i * f i t) ^ 2 - (∑ i, Q p.1 i * Q p.2 i * w i) ^ 2| ≤
        K / t := fun p => by
    obtain ⟨K, T, hK, hT, h'⟩ := hent p.1 p.2
    refine ⟨2 * |∑ i, Q p.1 i * Q p.2 i * w i| * K + K ^ 2, T, by positivity, hT,
      fun {t} ht => ?_⟩
    have ht1 : 1 ≤ t := hT.trans ht
    have e : t ^ 4 * (∑ i, Q p.1 i * Q p.2 i * f i t) ^ 2 =
        (t ^ 2 * ∑ i, Q p.1 i * Q p.2 i * f i t) ^ 2 := by ring
    rw [e]
    exact sq_rate ht1 hK (h' ht)
  obtain ⟨K, T, hK, hT, h'⟩ := sum_rate_div (fun _ : Fin d × Fin d => (1 : ℝ))
    (fun p t => t ^ 4 * (∑ i, Q p.1 i * Q p.2 i * f i t) ^ 2 -
      (∑ i, Q p.1 i * Q p.2 i * w i) ^ 2) hsq
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have hW : ∀ j k, ∑ i, Q j i * Q k i * w i = (Q * diagonal w * Qᵀ) j k := fun j k =>
    (conj_diagonal_entry Q w j k).symm
  have key : t ^ 4 * ∑ j, ∑ k, (∑ i, Q j i * Q k i * f i t) ^ 2 - ∑ i, w i ^ 2 =
      ∑ p : Fin d × Fin d, (1 : ℝ) * (t ^ 4 * (∑ i, Q p.1 i * Q p.2 i * f i t) ^ 2 -
        (∑ i, Q p.1 i * Q p.2 i * w i) ^ 2) := by
    simp only [one_mul, Finset.sum_sub_distrib, Fintype.sum_prod_type, ← Finset.mul_sum, hW,
      frobenius_conj_diagonal_frob hQ]
  rw [key]
  exact h' ht

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- `C(t) − S(t)` entrywise in the frame: `∑ᵢ QⱼᵢQₖᵢ (Var_loc,ᵢ − 1/(tλᵢ + g))`. -/
theorem localisedCov_sub_locS_entry (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j k : Fin d) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
        (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k =
      ∑ i, Q j i * Q k i *
        (localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
          1 / (t * lam i + g)) := by
  rw [localisedRotatedAnharmonic_cov_coord hQ c w₀ hlam hgamma hdisc hg ht j k,
    locS_rot_apply hQ hlam hg ht j k, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `C(t) − H⁻¹/t` entrywise in the frame: `∑ᵢ QⱼᵢQₖᵢ (Var_loc,ᵢ − 1/(tλᵢ))`. -/
theorem localisedCov_sub_inv_entry (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j k : Fin d) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
        (fun w => w k) - (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t =
      ∑ i, Q j i * Q k i *
        (localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t - 1 / lam i / t) := by
  rw [localisedRotatedAnharmonic_cov_coord hQ c w₀ hlam hgamma hdisc hg ht j k,
    conj_diagonal_entry, Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **A: the Frobenius discrepancy from the Gaussian-prior covariance**:
`|t⁴ ‖C(t) − S(t)‖_F² − ∑ᵢ (vᵢ + g/λᵢ²)²| ≤ K/t`, i.e.
`‖C − S‖_F² = ‖V + gH⁻²‖_F²/t⁴ + O(t⁻⁵)`. -/
theorem localisedCov_frobenius_locS_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * ∑ j, ∑ k,
          (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
            (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k) ^ 2 -
        ∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := frobenius_conj_rate hQ
    (fun i t => localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      1 / (t * lam i + g))
    (fun i => covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) fun i => by
      obtain ⟨K, T, hK, hT, h⟩ := localisedVar_sub_displayed_order2_rate (hlam i) (hgamma i)
        (hdisc i) hg (x₀ := affineFrame Q c w₀ i)
      exact ⟨K, T, hK, hT, fun {t} ht => order3_to_scaled (by linarith) (h ht)⟩
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  simp only [localisedCov_sub_locS_entry hlam hgamma hdisc hQ c w₀ hg ht0]
  exact h ht

/-- **B: changing the reference covariance to the unlocalised `H⁻¹/t`**:
`|t⁴ ‖C(t) − H⁻¹/t‖_F² − ∑ᵢ vᵢ²| ≤ K/t`, i.e. `‖C − H⁻¹/t‖_F² = ‖V‖_F²/t⁴ + O(t⁻⁵)` —
the explicit resolvent correction `gH⁻²` cancels; the localiser dependence inside `vᵢ` remains. -/
theorem localisedCov_frobenius_inv_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * ∑ j, ∑ k,
          (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
            (fun w => w k) - (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k / t) ^ 2 -
        ∑ i, varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := frobenius_conj_rate hQ
    (fun i t => localisedVar (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      1 / lam i / t)
    (fun i => varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) fun i => by
      obtain ⟨K, T, hK, hT, h⟩ := localisedVar_order2_rate (hlam i) (hgamma i) (hdisc i) hg
        (x₀ := affineFrame Q c w₀ i)
      exact ⟨K, T, hK, hT, fun {t} ht => order2_to_scaled (by linarith) (h ht)⟩
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  simp only [localisedCov_sub_inv_entry hlam hgamma hdisc hQ c w₀ hg ht0]
  exact h ht

omit hgamma hdisc in
/-- `‖S(t)‖_F² = ∑ᵢ 1/(tλᵢ + g)²` exactly. -/
theorem locS_frobenius (hQ : Qᵀ * Q = 1) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    ∑ j, ∑ k, locS g (Q * diagonal lam * Qᵀ) t j k ^ 2 = ∑ i, (1 / (t * lam i + g)) ^ 2 := by
  have h : ∀ j k, locS g (Q * diagonal lam * Qᵀ) t j k =
      (Q * diagonal (fun i => 1 / (t * lam i + g)) * Qᵀ) j k := fun j k => by
    rw [locS_rot_apply hQ hlam hg ht j k, conj_diagonal_entry]
  simp only [h, frobenius_conj_diagonal_frob hQ]

omit hgamma hdisc in
/-- `|t² ‖S(t)‖_F² − ∑ᵢ λᵢ⁻²| ≤ K/t`. -/
theorem locS_frobenius_rate (hQ : Qᵀ * Q = 1) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * ∑ j, ∑ k, locS g (Q * diagonal lam * Qᵀ) t j k ^ 2 - ∑ i, 1 / lam i ^ 2| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div (fun _ : Fin d => (1 : ℝ))
    (fun i t => t ^ 2 / (t * lam i + g) ^ 2 - 1 / lam i ^ 2) fun i =>
      ⟨g * (2 * lam i + g) / lam i ^ 4, 1, by have := hlam i; positivity, le_rfl,
        fun {t} ht => resolvent_sq_coord_rate (hlam i) hg ht⟩
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [locS_frobenius hlam hQ hg ht0]
  have key : t ^ 2 * ∑ i, (1 / (t * lam i + g)) ^ 2 - ∑ i, 1 / lam i ^ 2 =
      ∑ i, (1 : ℝ) * (t ^ 2 / (t * lam i + g) ^ 2 - 1 / lam i ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [div_pow, one_pow]; ring
  rw [key]
  exact h ht

/-- **C: the relative Frobenius discrepancy** (the note's `O(S²)` made quantitative):
`|t² ‖C − S‖_F²/‖S‖_F² − (∑ᵢ wᵢ²)/(∑ᵢ λᵢ⁻²)| ≤ K/t` in positive dimension. -/
theorem localisedCov_frobenius_relative_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hd : 0 < d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * ((∑ j, ∑ k,
          (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
            (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k) ^ 2) /
          ∑ j, ∑ k, locS g (Q * diagonal lam * Qᵀ) t j k ^ 2) -
        (∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) /
          ∑ i, 1 / lam i ^ 2| ≤ K / t := by
  obtain ⟨Ka, Ta, hKa, hTa, ha⟩ := localisedCov_frobenius_locS_rate hlam hgamma hdisc hQ c w₀ hg
  obtain ⟨Kb, Tb, hKb, hTb, hb⟩ := locS_frobenius_rate hlam hQ hg
  have hL : 0 < ∑ i, 1 / lam i ^ 2 := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    exact Finset.sum_pos (fun i _ => by have := hlam i; positivity) Finset.univ_nonempty
  set L := ∑ i, 1 / lam i ^ 2 with hLdef
  set A := ∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2 with hAdef
  have h0 : 0 ≤ 2 * Kb / L := by positivity
  refine ⟨2 * Ka / L + 2 * |A| * Kb / L ^ 2, Ta + Tb + 2 * Kb / L, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hta : Ta ≤ t := by linarith
  have htb : Tb ≤ t := by linarith
  have hb' := hb htb
  have hb2 : L / 2 ≤ t ^ 2 * ∑ j, ∑ k, locS g (Q * diagonal lam * Qᵀ) t j k ^ 2 := by
    have h2 : Kb / t ≤ L / 2 := by
      rw [div_le_iff₀ ht0]
      have h3 : 2 * Kb / L ≤ t := by linarith
      rw [div_le_iff₀ hL] at h3
      linarith
    have := (abs_le.mp (hb'.trans h2)).1
    linarith
  have e : t ^ 2 * ((∑ j, ∑ k,
      (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
        (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k) ^ 2) /
      ∑ j, ∑ k, locS g (Q * diagonal lam * Qᵀ) t j k ^ 2) =
      (t ^ 4 * ∑ j, ∑ k,
        (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
          (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k) ^ 2) /
      (t ^ 2 * ∑ j, ∑ k, locS g (Q * diagonal lam * Qᵀ) t j k ^ 2) := by
    rw [show t ^ 4 = t ^ 2 * t ^ 2 by ring, mul_assoc (t ^ 2) (t ^ 2),
      mul_div_mul_left _ _ (pow_ne_zero 2 ht0.ne'), mul_div_assoc]
  rw [e]
  exact ratio_rate hL hKa hKb ht0 hb2 (ha hta) hb'

/-- **The two-sided Frobenius bounds**: when `∑ᵢ wᵢ² > 0`, eventually
`∑wᵢ²/2 ≤ t⁴ ‖C(t) − S(t)‖_F² ≤ 3∑wᵢ²/2` — the discrepancy is of exact order `t⁻²` in
Frobenius norm. -/
theorem localisedCov_frobenius_locS_two_sided (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hw : 0 < ∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      (∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) / 2 ≤
        t ^ 4 * ∑ j, ∑ k,
          (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
            (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k) ^ 2 ∧
      t ^ 4 * ∑ j, ∑ k,
          (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j)
            (fun w => w k) - locS g (Q * diagonal lam * Qᵀ) t j k) ^ 2 ≤
        3 * (∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) / 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := localisedCov_frobenius_locS_rate hlam hgamma hdisc hQ c w₀ hg
  have h0 : 0 ≤ 2 * K / ∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^
      2 :=
    by positivity
  refine ⟨T + 2 * K / ∑ i, covLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2,
    by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  exact two_sided_of_rate hw ht0 (by linarith) (h (by linarith))

end Multi

end Laplace.Multi
