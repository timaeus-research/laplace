/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedDerivativeFrobenius

/-!
# The localised mean's squared discrepancy from the displayed mean, and its derivative

On E2's exact localised measure, with `m(t) = ⟨w⟩_loc`, `m_S(t) = c + Q P(t)` the note's displayed
(E3) mean (`Pᵢ = −αᵢt/(2(tλᵢ + g)²) + aᵢ/(tλᵢ + g)`, `aᵢ = g u₀ᵢ`), `rᵢ` the `t⁻²` coefficients of
`μᵢ − Pᵢ` (`meanLocResidual2`), `c₁ᵢ` the localised leading means and `c'ᵢ` their second-order
coefficients (`meanLocCoeff2`):

* `‖m(t) − m_S(t)‖² = ‖r‖²/t⁴ + O(t⁻⁵)` — eq:mean's `O(S²)` remainder, invariantly;
* exactly `∂ₜ mⱼ = −∑ᵢ Qⱼᵢ Cov_loc[L∘A, uᵢ]`, and `‖∂ₜm + Qc₁/t²‖² = 4‖c'‖²/t⁶ + O(t⁻⁷)`;
* `∂ₜ m_S` in closed form, and `‖∂ₜ(m − m_S)‖² = 4‖r‖²/t⁶ + O(t⁻⁷)` — the derivative reading of
  the first item, from the derivative expansions;
* the two-sided bounds when `‖r‖² > 0`.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section Algebra

variable {d : ℕ}

/-- `∑ⱼ (Qy)ⱼ² = ∑ᵢ yᵢ²` for `QᵀQ = 1`. -/
theorem euclid_conj_eq {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) (y : Fin d → ℝ) :
    ∑ j, (∑ i, Q j i * y i) ^ 2 = ∑ i, y i ^ 2 := by
  have h1 : ∀ j, ∑ i, Q j i * y i = (Q *ᵥ y) j := fun j => by
    simp [Matrix.mulVec, dotProduct]
  have h2 : ∑ j, (Q *ᵥ y) j ^ 2 = (Q *ᵥ y) ⬝ᵥ (Q *ᵥ y) := by simp only [dotProduct, sq]
  have h3 : ∑ i, y i ^ 2 = y ⬝ᵥ y := by simp only [dotProduct, sq]
  simp only [h1]
  rw [h2, h3, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hQ,
    Matrix.vecMul_one]

/-- **Euclidean transport**: per-coordinate rates `|t² fᵢ(t) − wᵢ| ≤ K/t` give
`|t⁴ ∑ⱼ (∑ᵢ Qⱼᵢ fᵢ(t))² − ∑ᵢ wᵢ²| ≤ K/t` for orthogonal `Q`. -/
theorem euclid_conj_rate {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) (f : Fin d → ℝ → ℝ)
    (w : Fin d → ℝ)
    (h : ∀ i, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |t ^ 2 * f i t - w i| ≤ K / t) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * ∑ j, (∑ i, Q j i * f i t) ^ 2 - ∑ i, w i ^ 2| ≤ K / t := by
  have hent : ∀ j, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * ∑ i, Q j i * f i t - ∑ i, Q j i * w i| ≤ K / t := fun j => by
    obtain ⟨K, T, hK, hT, h'⟩ := sum_rate_div (fun i => Q j i) (fun i t => t ^ 2 * f i t - w i) h
    refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
    have key : t ^ 2 * ∑ i, Q j i * f i t - ∑ i, Q j i * w i =
        ∑ i, Q j i * (t ^ 2 * f i t - w i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [key]
    exact h' ht
  have hsq : ∀ j, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * (∑ i, Q j i * f i t) ^ 2 - (∑ i, Q j i * w i) ^ 2| ≤ K / t := fun j => by
    obtain ⟨K, T, hK, hT, h'⟩ := hent j
    refine ⟨2 * |∑ i, Q j i * w i| * K + K ^ 2, T, by positivity, hT, fun {t} ht => ?_⟩
    have e : t ^ 4 * (∑ i, Q j i * f i t) ^ 2 = (t ^ 2 * ∑ i, Q j i * f i t) ^ 2 := by ring
    rw [e]
    exact sq_rate (hT.trans ht) hK (h' ht)
  obtain ⟨K, T, hK, hT, h'⟩ := sum_rate_div (fun _ : Fin d => (1 : ℝ))
    (fun j t => t ^ 4 * (∑ i, Q j i * f i t) ^ 2 - (∑ i, Q j i * w i) ^ 2) hsq
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have key : t ^ 4 * ∑ j, (∑ i, Q j i * f i t) ^ 2 - ∑ i, w i ^ 2 =
      ∑ j, (1 : ℝ) * (t ^ 4 * (∑ i, Q j i * f i t) ^ 2 - (∑ i, Q j i * w i) ^ 2) := by
    simp only [one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, euclid_conj_eq hQ]
  rw [key]
  exact h' ht

/-- The `t³` wrapper of `euclid_conj_rate`. -/
theorem euclid_conj_rate_cubic {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) (f : Fin d → ℝ → ℝ)
    (w : Fin d → ℝ)
    (h : ∀ i, ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → |t ^ 3 * f i t - w i| ≤ K / t) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 6 * ∑ j, (∑ i, Q j i * f i t) ^ 2 - ∑ i, w i ^ 2| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h'⟩ := euclid_conj_rate hQ (fun i t => t * f i t) w fun i => by
    obtain ⟨K, T, hK, hT, h⟩ := h i
    exact ⟨K, T, hK, hT, fun {t} ht => by
      have e : t ^ 2 * (t * f i t) = t ^ 3 * f i t := by ring
      rw [e]
      exact h ht⟩
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have e : t ^ 6 * ∑ j, (∑ i, Q j i * f i t) ^ 2 = t ^ 4 * ∑ j, (∑ i, Q j i * (t * f i t)) ^ 2 := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ∑ i, Q j i * (t * f i t) = t * ∑ i, Q j i * f i t by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  rw [e]
  exact h' ht

end Algebra

section Rates

/-- `|t²X − c₁ − 2c'/t| ≤ K/t² ⟹ |t³(X − c₁/t²) − 2c'| ≤ K/t`. -/
theorem lin_coord_scaled {t X c₁ c' K : ℝ} (ht : 0 < t)
    (h : |t ^ 2 * X - c₁ - 2 * c' / t| ≤ K / t ^ 2) :
    |t ^ 3 * (X - c₁ / t ^ 2) - 2 * c'| ≤ K / t := by
  have ht' : t ≠ 0 := ht.ne'
  have e : t ^ 3 * (X - c₁ / t ^ 2) - 2 * c' = t * (t ^ 2 * X - c₁ - 2 * c' / t) := by
    field_simp
  rw [e, abs_mul, abs_of_pos ht]
  calc t * |t ^ 2 * X - c₁ - 2 * c' / t| ≤ t * (K / t ^ 2) := by gcongr
    _ = K / t := by field_simp

/-- The two coordinate rates combine to the derivative of the difference:
`|t³ ∂ₜ(μ − P) + 2r| ≤ (K + K')/t` with `r = c' − ℓ₂`. -/
theorem mean_deriv_coord_combine {t X P c₁ c' ℓ₂ K K' : ℝ}
    (h1 : |t ^ 3 * (X - c₁ / t ^ 2) - 2 * c'| ≤ K / t)
    (h2 : |t ^ 3 * (P + c₁ / t ^ 2) + 2 * ℓ₂| ≤ K' / t) :
    |t ^ 3 * (-(X + P)) - -2 * (c' - ℓ₂)| ≤ (K + K') / t := by
  have e : t ^ 3 * (-(X + P)) - -2 * (c' - ℓ₂) =
      -((t ^ 3 * (X - c₁ / t ^ 2) - 2 * c') + (t ^ 3 * (P + c₁ / t ^ 2) + 2 * ℓ₂)) := by ring
  rw [e, abs_neg, add_div]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- `d/dt P(t)` for the displayed mean shift `P = −αt/(2(tλ + g)²) + gx₀/(tλ + g)`. -/
theorem hasDerivAt_locLeading {lam alpha g x₀ : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s => locLeading lam alpha g x₀ s)
      (-alpha * (g - t * lam) / (2 * (t * lam + g) ^ 3) - g * x₀ * lam / (t * lam + g) ^ 2) t := by
  have hd : t * lam + g ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s => s * lam + g) lam t := by
    simpa using ((hasDerivAt_id t).mul_const lam).add_const g
  have h2 : HasDerivAt (fun s => -alpha * s / (2 * (s * lam + g) ^ 2))
      (-alpha * (g - t * lam) / (2 * (t * lam + g) ^ 3)) t := by
    have hnum : HasDerivAt (fun s => -alpha * s) (-alpha) t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-alpha)
    have hden := (h1.pow 2).const_mul 2
    norm_num at hden
    refine (hnum.div hden (by change (2 : ℝ) * (t * lam + g) ^ 2 ≠ 0; positivity)).congr_deriv ?_
    field_simp
    ring
  have h3 : HasDerivAt (fun s => g * x₀ / (s * lam + g))
      (-(g * x₀ * lam) / (t * lam + g) ^ 2) t := by
    have h3' := (h1.inv hd).const_mul (g * x₀)
    refine (h3'.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp [Pi.inv_apply, div_eq_mul_inv]
  unfold locLeading
  exact (h2.add h3).congr_deriv (by ring)

/-- **The displayed mean's derivative to second order**:
`|t³(∂ₜP + c₁/t²) + 2ℓ₂| ≤ (9|α|g²/(2λ⁴) + 3g²|gx₀|/λ³)/t` for `t ≥ 1`,
`ℓ₂ = locLeadingCoeff2`. -/
theorem locLeading_deriv_order2 {lam alpha g x₀ t : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g)
    (ht : 1 ≤ t) :
    |t ^ 3 * ((-alpha * (g - t * lam) / (2 * (t * lam + g) ^ 3) -
        g * x₀ * lam / (t * lam + g) ^ 2) +
        (-alpha / (2 * lam ^ 2) + g * x₀ / lam) / t ^ 2) + 2 * locLeadingCoeff2 lam alpha g x₀| ≤
      (9 * |alpha| * g ^ 2 / (2 * lam ^ 4) + 3 * g ^ 2 * |g * x₀| / lam ^ 3) / t := by
  have ht0 : 0 < t := by linarith
  have hden : 0 < t * lam + g := by positivity
  have hs : 0 < t * lam := by positivity
  have e : t ^ 3 * ((-alpha * (g - t * lam) / (2 * (t * lam + g) ^ 3) -
      g * x₀ * lam / (t * lam + g) ^ 2) + (-alpha / (2 * lam ^ 2) + g * x₀ / lam) / t ^ 2) +
      2 * locLeadingCoeff2 lam alpha g x₀ =
      alpha * (g ^ 2 * (9 * (t * lam) ^ 2 + 11 * (t * lam) * g + 4 * g ^ 2)) /
        (2 * lam ^ 3 * (t * lam + g) ^ 3) -
      g * x₀ * (g ^ 2 * (3 * (t * lam) + 2 * g) / (lam ^ 2 * (t * lam + g) ^ 2)) := by
    unfold locLeadingCoeff2
    field_simp
    ring
  rw [e]
  have hA : |alpha * (g ^ 2 * (9 * (t * lam) ^ 2 + 11 * (t * lam) * g + 4 * g ^ 2)) /
      (2 * lam ^ 3 * (t * lam + g) ^ 3)| ≤ 9 * |alpha| * g ^ 2 / (2 * lam ^ 4) / t := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g ^ 2 *
      (9 * (t * lam) ^ 2 + 11 * (t * lam) * g + 4 * g ^ 2)),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * lam ^ 3 * (t * lam + g) ^ 3)]
    have hb : g ^ 2 * (9 * (t * lam) ^ 2 + 11 * (t * lam) * g + 4 * g ^ 2) ≤
        g ^ 2 * (9 * (t * lam + g) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hs.le hg, sq_nonneg g]
    calc |alpha| * (g ^ 2 * (9 * (t * lam) ^ 2 + 11 * (t * lam) * g + 4 * g ^ 2)) /
          (2 * lam ^ 3 * (t * lam + g) ^ 3) ≤
        |alpha| * (g ^ 2 * (9 * (t * lam + g) ^ 2)) / (2 * lam ^ 3 * (t * lam + g) ^ 3) := by
          gcongr
      _ = 9 * |alpha| * g ^ 2 / (2 * lam ^ 3 * (t * lam + g)) := by
          field_simp
      _ ≤ 9 * |alpha| * g ^ 2 / (2 * lam ^ 3 * (t * lam)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          gcongr
          linarith
      _ = 9 * |alpha| * g ^ 2 / (2 * lam ^ 4) / t := by
          field_simp
  have hB : |g * x₀ * (g ^ 2 * (3 * (t * lam) + 2 * g) / (lam ^ 2 * (t * lam + g) ^ 2))| ≤
      3 * g ^ 2 * |g * x₀| / lam ^ 3 / t := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g ^ 2 * (3 * (t * lam) + 2 * g) /
      (lam ^ 2 * (t * lam + g) ^ 2))]
    have hb : g ^ 2 * (3 * (t * lam) + 2 * g) ≤ g ^ 2 * (3 * (t * lam + g)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    calc |g * x₀| * (g ^ 2 * (3 * (t * lam) + 2 * g) / (lam ^ 2 * (t * lam + g) ^ 2)) ≤
        |g * x₀| * (g ^ 2 * (3 * (t * lam + g)) / (lam ^ 2 * (t * lam + g) ^ 2)) := by
          gcongr
      _ = 3 * g ^ 2 * |g * x₀| / (lam ^ 2 * (t * lam + g)) := by
          field_simp
      _ ≤ 3 * g ^ 2 * |g * x₀| / (lam ^ 2 * (t * lam)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          gcongr
          linarith
      _ = 3 * g ^ 2 * |g * x₀| / lam ^ 3 / t := by
          field_simp
  rw [add_div]
  exact (abs_sub _ _).trans (add_le_add hA hB)

end Rates

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- The displayed mean `m_S(t)ⱼ − cⱼ = ∑ᵢ Qⱼᵢ Pᵢ(t)` is differentiable for `t > 0`, with
`∂ₜ(m_S)ⱼ = ∑ᵢ Qⱼᵢ ∂ₜPᵢ`. -/
theorem hasDerivAt_displayed_mean_coord (hQ : Qᵀ * Q = 1) (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g)
    (alpha : Fin d → ℝ) (c w₀ : Fin d → ℝ) {t : ℝ} (ht : 0 < t) (j : Fin d) :
    HasDerivAt (fun s => (meanShiftLoc s g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
        g • (locS g (Q * diagonal lam * Qᵀ) s *ᵥ (w₀ - c))) j)
      (∑ i, Q j i * (-alpha i * (g - t * lam i) / (2 * (t * lam i + g) ^ 3) -
        g * affineFrame Q c w₀ i * lam i / (t * lam i + g) ^ 2)) t := by
  have heq : (fun s => (meanShiftLoc s g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
      g • (locS g (Q * diagonal lam * Qᵀ) s *ᵥ (w₀ - c))) j) =ᶠ[𝓝 t]
      fun s => ∑ i, Q j i * locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) s :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => by
      rw [displayed_mean_rot hQ hlam hg hs alpha c w₀]
      simp [Matrix.mulVec, dotProduct]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  exact HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_locLeading (hlam i) hg ht (alpha := alpha i) (x₀ := affineFrame Q c w₀ i)).const_mul
      (Q j i)

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- `mⱼ − cⱼ − (m_S)ⱼ = ∑ᵢ Qⱼᵢ (μᵢ − Pᵢ)`. -/
theorem localisedMean_sub_displayed_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j : Fin d) :
    gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (fun w => w j) -
        c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
          g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j =
      ∑ i, Q j i * (localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
        locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t) := by
  rw [localisedRotatedAnharmonic_ambient_coord hQ c w₀ hlam hgamma hdisc hg ht j,
    displayed_mean_rot hQ hlam hg ht alpha c w₀]
  simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **A: eq:mean's `O(S²)` remainder in Euclidean norm**:
`|t⁴ ‖m(t) − m_S(t)‖² − ∑ᵢ rᵢ²| ≤ K/t`, i.e. `‖m − m_S‖² = ‖r‖²/t⁴ + O(t⁻⁵)`. -/
theorem localisedMean_euclid_displayed_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 4 * ∑ j,
          (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
            (fun w => w j) - c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
            g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j) ^ 2 -
        ∑ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := euclid_conj_rate hQ
    (fun i t => localisedMean (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) t -
      locLeading (lam i) (alpha i) g (affineFrame Q c w₀ i) t)
    (fun i => meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) fun i => by
      obtain ⟨K, T, hK, hT, h⟩ := localisedMean_sub_locLeading_order2_rate (hlam i) (hgamma i)
        (hdisc i) hg (x₀ := affineFrame Q c w₀ i)
      exact ⟨K, T, hK, hT, fun {t} ht => order3_to_scaled (by linarith) (h ht)⟩
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  simp only [localisedMean_sub_displayed_coord hlam hgamma hdisc hQ c w₀ hg ht0]
  exact h ht

/-- **The mean's exact derivative**: `d/ds ⟨wⱼ⟩_loc(s) = −∑ᵢ Qⱼᵢ Cov_loc,t[L∘A, uᵢ]`. -/
theorem hasDerivAt_localised_mean_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j : Fin d) :
    HasDerivAt (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => w j))
      (-∑ i, Q j i * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) t := by
  have heq : (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
      (fun w => w j)) =ᶠ[𝓝 t]
      fun s => c j + ∑ i, Q j i *
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => affineFrame Q c w i) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => by
      rw [localised_mean_coord hlam hgamma hdisc hQ c w₀ hg hs j]
      rfl
  have h : HasDerivAt (fun s => c j + ∑ i, Q j i *
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => affineFrame Q c w i))
      (∑ i, Q j i * -gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) t := by
    refine HasDerivAt.const_add (c j) (HasDerivAt.fun_sum fun i _ => ?_)
    have hi := hasDerivAt_localised_frame_pow hlam hgamma hdisc hQ c w₀ hg ht i 1
    simp only [pow_one] at hi
    exact hi.const_mul (Q j i)
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [mul_neg, Finset.sum_neg_distrib]

/-- `∂ₜmⱼ + (Qc₁)ⱼ/t² = −∑ᵢ Qⱼᵢ (Cov_loc[L∘A, uᵢ] − c₁ᵢ/t²)`. -/
theorem localisedMean_deriv_add_lead_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) (j : Fin d) :
    deriv (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => w j)) t + (Q *ᵥ locLeadMean lam alpha g (affineFrame Q c w₀)) j / t ^ 2 =
      -∑ i, Q j i * (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
        locLeadMean lam alpha g (affineFrame Q c w₀) i / t ^ 2) := by
  rw [(hasDerivAt_localised_mean_coord hlam hgamma hdisc hQ c w₀ hg ht j).deriv]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_div, mul_sub, Finset.sum_sub_distrib,
    mul_div_assoc]
  ring

/-- **B: the derivative reading of eq:mean**: `|t⁶ ‖∂ₜm(t) + Qc₁/t²‖² − 4∑ᵢ c'ᵢ²| ≤ K/t`, i.e.
`‖∂ₜm + Qc₁/t²‖² = 4‖c'‖²/t⁶ + O(t⁻⁷)`. -/
theorem localisedMean_deriv_euclid_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 6 * ∑ j,
          (deriv (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s)
            s (fun w => w j)) t + (Q *ᵥ locLeadMean lam alpha g (affineFrame Q c w₀)) j / t ^ 2) ^
            2 -
        4 * ∑ i, meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := euclid_conj_rate_cubic hQ
    (fun i t => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
      locLeadMean lam alpha g (affineFrame Q c w₀) i / t ^ 2)
    (fun i => 2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) fun i => by
      obtain ⟨K, T, hK, hT, h⟩ :=
        localisedCovK_frame_lin_order2_rate hlam hgamma hdisc hQ c w₀ hg i
      exact ⟨K, T, hK, hT, fun {t} ht => lin_coord_scaled (by linarith) (h ht)⟩
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  simp only [localisedMean_deriv_add_lead_coord hlam hgamma hdisc hQ c w₀ hg ht0, neg_sq]
  have e : (4 : ℝ) *
      ∑ i, meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2 =
      ∑ i, (2 * meanLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact h ht

/-- `∂ₜ(m − m_S)ⱼ = ∑ᵢ Qⱼᵢ (−(Cov_loc[L∘A, uᵢ] + ∂ₜPᵢ))`. -/
theorem localisedMean_deriv_sub_displayed_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    {t : ℝ} (ht : 0 < t) (j : Fin d) :
    deriv (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => w j)) t -
      deriv (fun s => (meanShiftLoc s g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
        g • (locS g (Q * diagonal lam * Qᵀ) s *ᵥ (w₀ - c))) j) t =
      ∑ i, Q j i * (-(gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) +
        (-alpha i * (g - t * lam i) / (2 * (t * lam i + g) ^ 3) -
          g * affineFrame Q c w₀ i * lam i / (t * lam i + g) ^ 2))) := by
  rw [(hasDerivAt_localised_mean_coord hlam hgamma hdisc hQ c w₀ hg ht j).deriv,
    (hasDerivAt_displayed_mean_coord hQ hlam hg alpha c w₀ ht j).deriv, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **C: the derivative reading of A**: `|t⁶ ‖∂ₜ(m(t) − m_S(t))‖² − 4∑ᵢ rᵢ²| ≤ K/t`, i.e.
`‖∂ₜ(m − m_S)‖² = 4‖r‖²/t⁶ + O(t⁻⁷)`, from the derivative expansions (not by differentiating
the remainder). -/
theorem localisedMean_deriv_euclid_displayed_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 6 * ∑ j,
          (deriv (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s)
            s (fun w => w j)) t -
          deriv (fun s => (meanShiftLoc s g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
            g • (locS g (Q * diagonal lam * Qᵀ) s *ᵥ (w₀ - c))) j) t) ^ 2 -
        4 * ∑ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2| ≤
        K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := euclid_conj_rate_cubic hQ
    (fun i t => -(gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) +
      (-alpha i * (g - t * lam i) / (2 * (t * lam i + g) ^ 3) -
        g * affineFrame Q c w₀ i * lam i / (t * lam i + g) ^ 2)))
    (fun i => -2 * meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i))
    fun i => by
      obtain ⟨K, T, hK, hT, h⟩ :=
        localisedCovK_frame_lin_order2_rate hlam hgamma hdisc hQ c w₀ hg i
      refine ⟨K + (9 * |alpha i| * g ^ 2 / (2 * lam i ^ 4) +
        3 * g ^ 2 * |g * affineFrame Q c w₀ i| / lam i ^ 3), T, by have := hlam i; positivity, hT,
        fun {t} ht => ?_⟩
      exact mean_deriv_coord_combine (lin_coord_scaled (by linarith) (h ht))
        (locLeading_deriv_order2 (hlam i) hg (hT.trans ht))
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  simp only [localisedMean_deriv_sub_displayed_coord hlam hgamma hdisc hQ c w₀ hg ht0]
  have e : (4 : ℝ) *
      ∑ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2 =
      ∑ i, (-2 * meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact h ht

/-- **D: two-sided bounds**: when `‖r‖² > 0`, eventually `‖r‖²/2 ≤ t⁴ ‖m − m_S‖² ≤ 3‖r‖²/2`. -/
theorem localisedMean_euclid_displayed_two_sided (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hr : 0 < ∑ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      (∑ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) / 2 ≤
        t ^ 4 * ∑ j,
          (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
            (fun w => w j) - c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
            g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j) ^ 2 ∧
      t ^ 4 * ∑ j,
          (gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
            (fun w => w j) - c j - (meanShiftLoc t g (Q * diagonal lam * Qᵀ) (rotT Q alpha) +
            g • (locS g (Q * diagonal lam * Qᵀ) t *ᵥ (w₀ - c))) j) ^ 2 ≤
        3 * (∑ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2) / 2 :=
    by
  obtain ⟨K, T, hK, hT, h⟩ := localisedMean_euclid_displayed_rate hlam hgamma hdisc hQ c w₀ hg
  have h0 : 0 ≤ 2 * K /
      ∑ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2 := by
    positivity
  refine ⟨T + 2 * K /
      ∑ i, meanLocResidual2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) ^ 2,
    by linarith, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  exact two_sided_of_rate hr ht0 (by linarith) (h (by linarith))

end Multi

end Laplace.Multi
