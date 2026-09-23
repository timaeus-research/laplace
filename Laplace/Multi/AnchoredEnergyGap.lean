/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AnchoredGaussianGap

/-!
# The anchored Gaussian energy gap: two gaps, one anharmonic coefficient (E3/E2)

E3's anchored Gaussian LLC prediction is the tilted expectation `t·⟨½uᵀHu⟩_{tH+gI,v}`
(`localised_llc`). In the eigenbasis of `H`, with `aᵢ = (Uᵀv)ᵢ`, it is exactly
`𝓔^{anch}_t = ½∑ᵢ tλᵢ/(tλᵢ+g) + (t/2)∑ᵢ λᵢ(aᵢ/(tλᵢ+g))²` (`anchoredGaussianEnergy_eq`): E3's
localised
LLC `½∑tλᵢ/(tλᵢ+g)` plus the anchor's mean-energy term. In the E2 frame (`aᵢ = g·u₀ᵢ`) it expands as
`𝓔^{anch}_t = d/2 + (∑ᵢaᵢ²/(2λᵢ) − g∑ᵢ1/(2λᵢ))/t + O(t⁻²)` (`anchoredGaussianEnergy_rate2`), and
with the
landed second-order energy expansion `t⟨L∘A⟩_loc = d/2 + ∑ᵢe₁ᵢ/t + O(t⁻²)`
(`localisedRotatedAnharmonic_llc_order2_rate`):
**`t⟨L∘A⟩_loc − 𝓔^{anch}_t = C₁′/t + O(t⁻²)`**, `C₁′ = ∑ᵢ(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ)) = ∑ᵢ(e₀ᵢ −
aᵢαᵢ/(2λᵢ²))`
(`localisedEnergy_anchoredGap`) — the same purely anharmonic coefficient as the transform gap of
`AnchoredGaussianGap`: two gaps, one coefficient. Against the *centred* prediction
`½tr(H(tH+gI)⁻¹)` the
energy gap is `C₁/t = (C₁′ + ∑ᵢaᵢ²/(2λᵢ))/t` (`LocalisedEnergyInvariant`), so the anchor's
mean-energy
term accounts for exactly the Gaussian anchor contribution. Obtained from the landed energy theorem
and an independent expansion of the exact Gaussian energy — no `s`-derivative of a transform
remainder.
-/

open Matrix Filter Topology Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Orthogonal invariance of the dot product: `(Uw)·(Uz) = w·z`. -/
theorem dotProduct_orthoOf_mulVec {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (w z : ι → ℝ) :
    (orthoOf hA *ᵥ w) ⬝ᵥ (orthoOf hA *ᵥ z) = w ⬝ᵥ z := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, orthoOf_transpose_mul hA,
    Matrix.one_mulVec]

/-- The anchor's mean energy in the eigenbasis: `mᵀHm = ∑ᵢ λᵢ(aᵢ/(tλᵢ+g))²` for `m = (tH+gI)⁻¹v`,
`aᵢ = (Uᵀv)ᵢ`. -/
theorem tiltMean_quadForm_localised {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g : ℝ} (ht : 0 < t)
    (hg : 0 ≤ g) (v : ι → ℝ) :
    tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v ⬝ᵥ H *ᵥ tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v
        =
      ∑ i, hH.1.eigenvalues i * (((orthoOf hH.1)ᵀ *ᵥ v) i / (t * hH.1.eigenvalues i + g)) ^ 2 := by
  have hm : tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v = orthoOf hH.1 *ᵥ
      (diagonal (fun i => 1 / (t * hH.1.eigenvalues i + g)) *ᵥ ((orthoOf hH.1)ᵀ *ᵥ v)) := by
    unfold tiltMean
    rw [inv_localisedPrecision_eq_conj hH ht hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hHU : H *ᵥ (orthoOf hH.1 *ᵥ
      (diagonal (fun i => 1 / (t * hH.1.eigenvalues i + g)) *ᵥ ((orthoOf hH.1)ᵀ *ᵥ v))) =
      orthoOf hH.1 *ᵥ (diagonal hH.1.eigenvalues *ᵥ
        (diagonal (fun i => 1 / (t * hH.1.eigenvalues i + g)) *ᵥ ((orthoOf hH.1)ᵀ *ᵥ v))) := by
    rw [Matrix.mulVec_mulVec, mul_orthoOf_eq hH.1, ← Matrix.mulVec_mulVec]
  rw [hm, hHU, dotProduct_orthoOf_mulVec hH.1]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **E3's anchored Gaussian energy in the eigenbasis**:
`t·⟨½uᵀHu⟩_{tH+gI,v} = ½∑ᵢ tλᵢ/(tλᵢ+g) + (t/2)∑ᵢ λᵢ(aᵢ/(tλᵢ+g))²`, `aᵢ = (Uᵀv)ᵢ`. -/
theorem anchoredGaussianEnergy_eq {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g : ℝ} (ht : 0 < t)
    (hg : 0 ≤ g) (v : ι → ℝ) :
    t * tiltedExpectation (t • H + g • (1 : Matrix ι ι ℝ)) v (fun u => (1 / 2) * (u ⬝ᵥ H *ᵥ u)) =
      1 / 2 * ∑ i, t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + g) +
        t / 2 * ∑ i, hH.1.eigenvalues i *
          (((orthoOf hH.1)ᵀ *ᵥ v) i / (t * hH.1.eigenvalues i + g)) ^ 2 := by
  have hP := effectivePrecision_posDef hH ht hg
  rw [tiltedExpectation_const_mul, tiltedExpectation_quadForm hP, tiltMean_quadForm_localised hH ht
      hg v]
  have h := localised_llc_matrix_eq_eigen hH ht hg
  unfold localisedLLC at h
  have e : ∑ i, ∑ j, (t • H) i j * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ i j =
      t * ∑ i, ∑ j, H i j * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ i j := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [e] at h
  linear_combination h

end Laplace.Sampler

namespace Laplace.Multi

/-! ### The anchored energy's finite-temperature correction (E2 frame data) -/

/-- `|1/(u+g)² − 1/u²| ≤ 2g/u³ + g²/u⁴` for `u > 0`, `g ≥ 0`. -/
theorem inv_sq_shift_rate {u g : ℝ} (hu : 0 < u) (hg : 0 ≤ g) :
    |1 / (u + g) ^ 2 - 1 / u ^ 2| ≤ 2 * g / u ^ 3 + g ^ 2 / u ^ 4 := by
  have hug : 0 < u + g := by positivity
  have e : 1 / (u + g) ^ 2 - 1 / u ^ 2 = -(g * (2 * u + g) / (u ^ 2 * (u + g) ^ 2)) := by
    field_simp
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  calc g * (2 * u + g) / (u ^ 2 * (u + g) ^ 2) ≤ g * (2 * u + g) / (u ^ 2 * u ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))
    _ = 2 * g / u ^ 3 + g ^ 2 / u ^ 4 := by
        field_simp

/-- **The anchored Gaussian energy's correction**:
`½∑ᵢ tλᵢ/(tλᵢ+g) + (t/2)∑ᵢ λᵢ(aᵢ/(tλᵢ+g))² = d/2 + (∑ᵢaᵢ²/(2λᵢ) − g∑ᵢ1/(2λᵢ))/t + O(t⁻²)`. -/
theorem anchoredGaussianEnergy_rate2 {d : ℕ} {lam : Fin d → ℝ} {g : ℝ} (hlam : ∀ i, 0 < lam i)
    (hg : 0 ≤ g) (a : Fin d → ℝ) {t : ℝ} (ht : 1 ≤ t) :
      |(1 / 2 * ∑ i, t * lam i / (t * lam i + g) + t / 2 * ∑ i, lam i * (a i / (t * lam i + g)) ^ 2)
        - (d : ℝ) / 2 - (∑ i, a i ^ 2 / (2 * lam i) - ∑ i, g / (2 * lam i)) / t| ≤ (∑ i, (g ^ 2 / (2
        * lam i ^ 2) + a i ^ 2 / 2 * (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3))) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  -- per-direction identities and bounds
  have key : ∀ i, 1 / 2 * (t * lam i / (t * lam i + g)) + t / 2 * (lam i * (a i / (t * lam i + g))
      ^ 2) -
      1 / 2 - (a i ^ 2 / (2 * lam i) - g / (2 * lam i)) / t =
      g / 2 * (1 / (t * lam i) - 1 / (t * lam i + g)) +
        a i ^ 2 * lam i * t / 2 * (1 / (t * lam i + g) ^ 2 - 1 / (t * lam i) ^ 2) := fun i => by
    have := (hlam i).ne'
    have := ht0.ne'
    have : t * lam i + g ≠ 0 := by have := hlam i; positivity
    field_simp
    ring
  have hb : ∀ i, |g / 2 * (1 / (t * lam i) - 1 / (t * lam i + g)) +
      a i ^ 2 * lam i * t / 2 * (1 / (t * lam i + g) ^ 2 - 1 / (t * lam i) ^ 2)| ≤
      (g ^ 2 / (2 * lam i ^ 2) + a i ^ 2 / 2 * (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3)) / t ^ 2 :=
          fun i => by
    have hl := hlam i
    have hu : 0 < t * lam i := by positivity
    have h1 := inv_shift_rate hu hg
    have h2 := inv_sq_shift_rate hu hg
    have b1 : |g / 2 * (1 / (t * lam i) - 1 / (t * lam i + g))| ≤ g ^ 2 / (2 * lam i ^ 2) / t ^ 2
        := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g / 2), abs_sub_comm]
      calc g / 2 * |1 / (t * lam i + g) - 1 / (t * lam i)| ≤ g / 2 * (g / (t * lam i) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = g ^ 2 / (2 * lam i ^ 2) / t ^ 2 := by
            field_simp
    have b2 : |a i ^ 2 * lam i * t / 2 * (1 / (t * lam i + g) ^ 2 - 1 / (t * lam i) ^ 2)| ≤
        a i ^ 2 / 2 * (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3) / t ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a i ^ 2 * lam i * t / 2)]
      have h3 : g ^ 2 / lam i ^ 3 / t ^ 3 ≤ g ^ 2 / lam i ^ 3 / t ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg t)])
      calc a i ^ 2 * lam i * t / 2 * |1 / (t * lam i + g) ^ 2 - 1 / (t * lam i) ^ 2|
          ≤ a i ^ 2 * lam i * t / 2 * (2 * g / (t * lam i) ^ 3 + g ^ 2 / (t * lam i) ^ 4) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = a i ^ 2 / 2 * (2 * g / lam i ^ 2 / t ^ 2 + g ^ 2 / lam i ^ 3 / t ^ 3) := by
            field_simp
        _ ≤ a i ^ 2 / 2 * (2 * g / lam i ^ 2 / t ^ 2 + g ^ 2 / lam i ^ 3 / t ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add le_rfl h3) (by positivity)
        _ = a i ^ 2 / 2 * (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3) / t ^ 2 := by ring
    calc _ ≤ |g / 2 * (1 / (t * lam i) - 1 / (t * lam i + g))| +
          |a i ^ 2 * lam i * t / 2 * (1 / (t * lam i + g) ^ 2 - 1 / (t * lam i) ^ 2)| := abs_add_le
              _ _
      _ ≤ g ^ 2 / (2 * lam i ^ 2) / t ^ 2 + a i ^ 2 / 2 * (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3) /
          t ^ 2 :=
          add_le_add b1 b2
      _ = _ := by ring
  -- assemble the sums
  have hd : (d : ℝ) / 2 = ∑ _i : Fin d, (1 / 2 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have e : (1 / 2 * ∑ i, t * lam i / (t * lam i + g) + t / 2 * ∑ i, lam i * (a i / (t * lam i + g))
      ^ 2) - (d : ℝ) / 2 - (∑ i, a i ^ 2 / (2 * lam i) - ∑ i, g / (2 * lam i)) / t = ∑ i, (1 / 2 *
      (t * lam i / (t * lam i + g)) + t / 2 * (lam i * (a i / (t * lam i + g)) ^ 2) - 1 / 2 - (a i ^
      2 / (2 * lam i) - g / (2 * lam i)) / t) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum,
      sub_div, hd]
  rw [e]
  calc _ ≤ ∑ i, |1 / 2 * (t * lam i / (t * lam i + g)) + t / 2 * (lam i * (a i / (t * lam i + g)) ^
      2) -
        1 / 2 - (a i ^ 2 / (2 * lam i) - g / (2 * lam i)) / t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (g ^ 2 / (2 * lam i ^ 2) + a i ^ 2 / 2 * (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3)) / t
        ^ 2 :=
        Finset.sum_le_sum fun i _ => by rw [key i]; exact hb i
    _ = _ := by rw [Finset.sum_div]

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The anchored energy gap is governed by `C₁′`**:
`t⟨L∘A⟩_loc − (½∑ᵢ tλᵢ/(tλᵢ+g) + (t/2)∑ᵢ λᵢ(aᵢ/(tλᵢ+g))²) = C₁′/t + O(t⁻²)`, `aᵢ = g·u₀ᵢ`,
`C₁′ = ∑ᵢ(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ)) = ∑ᵢ(e₀ᵢ − aᵢαᵢ/(2λᵢ²))` — the transform gap's coefficient. -/
theorem localisedEnergy_anchoredGap (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) - (1 / 2 * ∑ i, t * lam i / (t * lam i + g) + t / 2
        * ∑ i, lam i * ((g * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2) - (∑ i, (energyLocCoeff1
        (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q
        c w₀ i) ^ 2 / (2 * lam i))) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ :=
    localisedRotatedAnharmonic_llc_order2_rate hQ c w₀ hlam hgamma hdisc hg
  refine ⟨K₁ + ∑ i, (g ^ 2 / (2 * lam i ^ 2) + (g * affineFrame Q c w₀ i) ^ 2 / 2 *
    (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3)), T₁, ?_, hT₁, fun {t} ht => ?_⟩
  · have : 0 ≤ ∑ i, (g ^ 2 / (2 * lam i ^ 2) + (g * affineFrame Q c w₀ i) ^ 2 / 2 *
        (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3)) := Finset.sum_nonneg fun i _ => by
      have := hlam i
      positivity
    linarith
  have ht1 : 1 ≤ t := by linarith
  have e₁ := h₁ ht
  have e₂ := anchoredGaussianEnergy_rate2 hlam hg (fun i => g * affineFrame Q c w₀ i) ht1
  have hC : (∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) - (∑ i, (g *
      affineFrame Q c w₀ i) ^ 2 / (2 * lam i) - ∑ i, g / (2 * lam i)) = ∑ i, (energyLocCoeff1 (lam
      i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i)
      ^ 2 / (2 * lam i)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have e : t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) - (1 / 2 * ∑ i, t * lam i / (t * lam i + g) + t / 2 *
      ∑ i, lam i * ((g * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2) - (∑ i, (energyLocCoeff1 (lam
      i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i)
      ^ 2 / (2 * lam i))) / t = (t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma) - (d : ℝ) / 2 - (∑ i, energyLocCoeff1
      (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t) - ((1 / 2 * ∑ i, t * lam i / (t *
      lam i + g) + t / 2 * ∑ i, lam i * ((g * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2) - (d :
      ℝ) / 2 - (∑ i, (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i) - ∑ i, g / (2 * lam i)) / t) := by
    rw [← hC]
    ring
  rw [e]
  calc _ ≤ |_| + |_| := abs_sub _ _
    _ ≤ K₁ / t ^ 2 + (∑ i, (g ^ 2 / (2 * lam i ^ 2) + (g * affineFrame Q c w₀ i) ^ 2 / 2 *
        (2 * g / lam i ^ 2 + g ^ 2 / lam i ^ 3))) / t ^ 2 := add_le_add e₁ e₂
    _ = _ := by ring

end Multi

end Laplace.Multi
