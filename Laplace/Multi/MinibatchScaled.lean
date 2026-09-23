/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MinibatchLongRun
import Laplace.Multi.AutocovScaled

/-!
# The minibatch long-run variance at the β-scaled step (E8 + E5 at the anchored scaling)

On the anchored model `P_t = tH + g·1`, `m_t = P_t⁻¹g(w₀ − c)`, with step `h = η/t` and `0 < ηλᵢ <
2`, tide 105's
`τ²_{mb}` reads (`mbAnchored_longRunVar`) `½∑ᵢⱼλᵢλⱼŜᵢⱼ²w₂(j) + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼw₁(j)` with
`Ŝᵢⱼ = (2h[i=j] + h²t²Ĉᵢⱼ)/(1 − ρᵢρⱼ)`, `m̂ᵢ = gŵᵢ/(tλᵢ+g)`.

* **Fixed gradient-noise covariance `C`**: `Ŝᵢⱼ(t) → η²Ĉᵢⱼ/(1 − (1−ηλᵢ)(1−ηλⱼ)) =
ηĈᵢⱼ/(λᵢ+λⱼ−ηλᵢλⱼ)`
  (`mbEntry_scaled_tendsto`), the mean part vanishes, and the *unscaled* long-run variance tends to
  **`L_∞ = ½∑ᵢⱼλᵢλⱼ(η²Ĉᵢⱼ/(1−(1−ηλᵢ)(1−ηλⱼ)))²·(1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))`**
  (`mbScaled_longRunVar_tendsto`); hence the
  long-run variance of the scaled statistic `t·½uᵀHu` is `Θ(t²)`: **`t²τ²_{mb}(t) → ∞`** whenever
  `L_∞ > 0`
  (`mbScaled_longRunVar_mul_sq_tendsto_atTop`).
* **Linear batch growth `C_t = C₀/t`**: `t·Ŝᵢⱼ(t) → (2η[i=j] + η²Ĉ₀ᵢⱼ)/(1 − (1−ηλᵢ)(1−ηλⱼ))`
(`mbEntry_lin_scaled_tendsto`),
  `t·m̂ᵢ → gŵᵢ/λᵢ`, `Ŝᵢⱼ → 0`, and **`t²τ²_{mb}(t) → L_lin = ½∑ᵢⱼλᵢλⱼ((2η[i=j] +
  η²Ĉ₀ᵢⱼ)/(1−(1−ηλᵢ)(1−ηλⱼ)))²·(1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))`**
  (`mbScaled_lin_longRunVar_tendsto`), finite: linear batch growth bounds the scaled fluctuation,
  as it bounds the
  scaled bias (tide 101).
* **Comparison**: `L_lin(C₀ = 0) = L_η = ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)` (tide 103's
exact-gradient limit,
  `Llin_zero_eq`) and `L_η ≤ L_lin` for `C₀ ⪰ 0` (`Leta_le_Llin`).
-/

open Matrix Filter Topology MeasureTheory

namespace Laplace.Multi

/-! ### Scalar limits at `h = η/t` -/

section Scalar

variable {lam₁ lam₂ g η : ℝ}

/-- `1 − ρᵢ(t)ρⱼ(t) → 1 − (1−ηλᵢ)(1−ηλⱼ)`. -/
theorem one_sub_rho_mul_scaled_tendsto (lam₁ lam₂ g η : ℝ) :
    Tendsto (fun t : ℝ => 1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g))) atTop
      (𝓝 (1 - (1 - η * lam₁) * (1 - η * lam₂))) :=
  ((rho_scaled_tendsto lam₁ g η).mul (rho_scaled_tendsto lam₂ g η)).const_sub 1

theorem one_sub_rho_mul_pos (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hη : 0 < η) (hηl₁ : η * lam₁ < 2)
    (hηl₂ : η * lam₂ < 2) : 0 < 1 - (1 - η * lam₁) * (1 - η * lam₂) := by
  have h1 := mul_pos hη hlam₁
  have h2 := mul_pos hη hlam₂
  exact Laplace.Sampler.one_sub_mul_pos_of_abs_lt_one (abs_lt.2 ⟨by linarith, by linarith⟩)
    (abs_lt.2 ⟨by linarith, by linarith⟩)

/-- Fixed noise: the frame entry `(2(η/t)δ + (η/t)²t²c)/(1 − ρᵢρⱼ) → η²c/(1 − (1−ηλᵢ)(1−ηλⱼ))`. -/
theorem mbEntry_scaled_tendsto (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hη : 0 < η) (hηl₁ : η * lam₁
    < 2)
    (hηl₂ : η * lam₂ < 2) (δ c : ℝ) :
    Tendsto (fun t : ℝ => (2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * c) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) atTop
      (𝓝 (η ^ 2 * c / (1 - (1 - η * lam₁) * (1 - η * lam₂)))) := by
  have e : (fun t : ℝ => 2 * η * δ / t + η ^ 2 * c) =ᶠ[atTop]
      fun t => 2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * c := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp
  have hnum := ((tendsto_const_nhds (x := 2 * η * δ)).div_atTop tendsto_id).add
    (tendsto_const_nhds (x := η ^ 2 * c))
  rw [zero_add] at hnum
  exact (hnum.congr' e).div (one_sub_rho_mul_scaled_tendsto lam₁ lam₂ g η)
    (one_sub_rho_mul_pos hlam₁ hlam₂ hη hηl₁ hηl₂).ne'

/-- Linear batch growth: `t·(2(η/t)δ + (η/t)²t²(c/t))/(1 − ρᵢρⱼ) → (2ηδ + η²c)/(1 −
(1−ηλᵢ)(1−ηλⱼ))`. -/
theorem mbEntry_lin_scaled_tendsto (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hη : 0 < η)
    (hηl₁ : η * lam₁ < 2) (hηl₂ : η * lam₂ < 2) (δ c : ℝ) :
    Tendsto (fun t : ℝ => t * ((2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * (1 / t * c)) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g))))) atTop
      (𝓝 ((2 * η * δ + η ^ 2 * c) / (1 - (1 - η * lam₁) * (1 - η * lam₂)))) := by
  have e : (fun t : ℝ => (2 * η * δ + η ^ 2 * c) /
      (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) =ᶠ[atTop]
      fun t => t * ((2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * (1 / t * c)) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    rw [← mul_div_assoc]
    congr 1
    field_simp
  exact ((tendsto_const_nhds (x := 2 * η * δ + η ^ 2 * c)).div
    (one_sub_rho_mul_scaled_tendsto lam₁ lam₂ g η) (one_sub_rho_mul_pos hlam₁ hlam₂ hη hηl₁
        hηl₂).ne').congr' e

/-- Linear batch growth: the entry itself vanishes, `Ŝᵢⱼ(t) = (tŜᵢⱼ)/t → 0`. -/
theorem mbEntry_lin_tendsto_zero (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hη : 0 < η)
    (hηl₁ : η * lam₁ < 2) (hηl₂ : η * lam₂ < 2) (δ c : ℝ) :
    Tendsto (fun t : ℝ => (2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * (1 / t * c)) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) atTop (𝓝 0) := by
  refine ((mbEntry_lin_scaled_tendsto (g := g) hlam₁ hlam₂ hη hηl₁ hηl₂ δ c).div_atTop
    tendsto_id).congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  exact mul_div_cancel_left₀ _ ht

/-- `t·gw/(tλ + g) → gw/λ`. -/
theorem mul_anchoredMean_tendsto (hlam₁ : 0 < lam₁) (hg : 0 ≤ g) (w : ℝ) :
    Tendsto (fun t : ℝ => t * (g * w / (t * lam₁ + g))) atTop (𝓝 (g * w / lam₁)) := by
  have h := (tendsto_const_nhds (x := g * w / lam₁)).mul (ratio_scaled_tendsto (g := g) hlam₁)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hp : t * lam₁ + g ≠ 0 := by positivity
  have := hlam₁.ne'
  field_simp

/-- `gw/(tλ + g) → 0`. -/
theorem anchoredMean_tendsto_zero (hlam₁ : 0 < lam₁) (g w : ℝ) :
    Tendsto (fun t : ℝ => g * w / (t * lam₁ + g)) atTop (𝓝 0) :=
  (tendsto_const_nhds (x := g * w)).div_atTop
    (tendsto_atTop_add_const_right atTop g (tendsto_id.atTop_mul_const hlam₁))

end Scalar

/-! ### The anchored model -/

section Anchored

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g : ℝ}

/-- Tide 105's `τ²_{mb}` on the anchored model, with explicit frame entries. -/
theorem mbAnchored_longRunVar (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0
    ≤ g)
    {t : ℝ} (ht : 0 < t) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * (t * lam i + g) < 2)
    {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) :
    Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) h t C ((t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) = 1 / 2 * ∑ i, ∑ j, lam i * lam j * ((2 *
      h * (if i = j then 1 else 0) + h ^ 2 * t ^ 2 * (Qᵀ * C * Q) i j) / (1 - (1 - h * (t * lam i +
      g)) * (1 - h * (t * lam j + g)))) ^ 2 * ((1 + (1 - h * (t * lam j + g)) ^ 2) / (1 - (1 - h *
      (t * lam j + g)) ^ 2)) + ∑ i, ∑ j, lam i * lam j * (g * affineFrame Q c w₀ i / (t * lam i +
      g)) * (g * affineFrame Q c w₀ j / (t * lam j + g)) * ((2 * h * (if i = j then 1 else 0) + h ^
      2 * t ^ 2 * (Qᵀ * C * Q) i j) / (1 - (1 - h * (t * lam i + g)) * (1 - h * (t * lam j + g)))) *
      ((1 + (1 - h * (t * lam j + g))) / (1 - (1 - h * (t * lam j + g)))) := by
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have hdiagP := transpose_localisedPrecision_conj (lam := lam) hQ t g
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  rw [Laplace.Sampler.mbLongRunVar_eq hQ hdiagP hp hh hev hdiagH t hC]
  simp only [transpose_mulVec_anchoredMean hlam hQ c w₀ hg ht, Laplace.Sampler.diagLyapunov,
    Matrix.of_apply, Laplace.Sampler.minibatchNoise, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hQ, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]

end Anchored

/-! ### The β-scaled limits -/

section Scaled

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g η : ℝ}

/-- **Fixed gradient noise**: `τ²_{mb}(t) → L_∞`. -/
theorem mbScaled_longRunVar_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) :
    Tendsto (fun t : ℝ => Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g • (1 :
      Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t C ((t •
      (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c)))) atTop (𝓝
      (1 / 2 * ∑ i, ∑ j, lam i * lam j * (η ^ 2 * (Qᵀ * C * Q) i j / (1 - (1 - η * lam i) * (1 - η *
      lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 - η * lam j))))) := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ ∀ i, η / t * (t * lam i + g) < 2 :=
    (eventually_gt_atTop 0).and (Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1))
  have hmain : Tendsto (fun t : ℝ => 1 / 2 * ∑ i, ∑ j, lam i * lam j * ((2 * (η / t) * (if i = j
      then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * C * Q) i j) / (1 - (1 - (η / t) * (t * lam i +
      g)) * (1 - (η / t) * (t * lam j + g)))) ^ 2 * ((1 + (1 - (η / t) * (t * lam j + g)) ^ 2) / (1
      - (1 - (η / t) * (t * lam j + g)) ^ 2))) atTop (𝓝 (1 / 2 * ∑ i, ∑ j, lam i * lam j * (η ^ 2 *
      (Qᵀ * C * Q) i j / (1 - (1 - η * lam i) * (1 - η * lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) /
      (η * lam j * (2 - η * lam j))))) :=
    (tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ =>
      ((tendsto_const_nhds (x := lam i * lam j)).mul
        ((mbEntry_scaled_tendsto (g := g) (hlam i) (hlam j) hη (hηl i) (hηl j) (if i = j then 1
            else 0)
          ((Qᵀ * C * Q) i j)).pow 2)).mul (iat_quad_scaled_tendsto (g := g) (hlam j) hη (hηl
              j))).const_mul
      (1 / 2)
  have hmean : Tendsto (fun t : ℝ => ∑ i, ∑ j, lam i * lam j * (g * affineFrame Q c w₀ i / (t * lam
      i + g)) * (g * affineFrame Q c w₀ j / (t * lam j + g)) * ((2 * (η / t) * (if i = j then 1 else
      0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * C * Q) i j) / (1 - (1 - (η / t) * (t * lam i + g)) * (1 - (η
      / t) * (t * lam j + g)))) * ((1 + (1 - (η / t) * (t * lam j + g))) / (1 - (1 - (η / t) * (t *
      lam j + g))))) atTop (𝓝 (∑ i : Fin d, ∑ j : Fin d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ => by
      have := ((((tendsto_const_nhds (x := lam i * lam j)).mul
        (anchoredMean_tendsto_zero (hlam i) g (affineFrame Q c w₀ i))).mul
        (anchoredMean_tendsto_zero (hlam j) g (affineFrame Q c w₀ j))).mul
        (mbEntry_scaled_tendsto (g := g) (hlam i) (hlam j) hη (hηl i) (hηl j) (if i = j then 1 else
            0)
          ((Qᵀ * C * Q) i j))).mul (iat_lin_scaled_tendsto (g := g) (hlam j) hη)
      simpa using this
  have hF := hmain.add hmean
  simp only [Finset.sum_const_zero, add_zero] at hF
  refine hF.congr' ?_
  filter_upwards [hev] with t ⟨ht, hev⟩
  rw [mbAnchored_longRunVar hlam hQ c w₀ hg ht (div_pos hη ht) hev hC]

/-- **`t²τ²_{mb}(t) → ∞`** under fixed gradient noise (whenever `L_∞ > 0`). -/
theorem mbScaled_longRunVar_mul_sq_tendsto_atTop (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ :
    Fin d → ℝ) (hg : 0 ≤ g) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) {C : Matrix (Fin d) (Fin d) ℝ}
    (hC : C.PosSemidef) (hL : 0 < 1 / 2 * ∑ i, ∑ j, lam i * lam j * (η ^ 2 * (Qᵀ * C * Q) i j / (1
        - (1 - η * lam i) * (1 - η * lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 -
            η * lam j)))) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t C
      ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))))
      atTop atTop :=
  (tendsto_pow_atTop two_ne_zero).atTop_mul_pos hL (mbScaled_longRunVar_tendsto hlam hQ c w₀ hg hη
      hηl hC)

/-- **Linear batch growth** `C_t = C₀/t`: `t²τ²_{mb}(t) → L_lin`. -/
theorem mbScaled_lin_longRunVar_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d →
    ℝ) (hg : 0 ≤ g) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) {C₀ : Matrix (Fin d) (Fin d) ℝ} (hC₀ : C₀.PosSemidef) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t ((1
      / t) • C₀) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ -
      c)))) atTop (𝓝 (1 / 2 * ∑ i, ∑ j, lam i * lam j * ((2 * η * (if i = j then 1 else 0) + η ^ 2 *
      (Qᵀ * C₀ * Q) i j) / (1 - (1 - η * lam i) * (1 - η * lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2)
      / (η * lam j * (2 - η * lam j))))) := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ ∀ i, η / t * (t * lam i + g) < 2 :=
    (eventually_gt_atTop 0).and (Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1))
  have hCt : ∀ t : ℝ, Qᵀ * ((1 / t) • C₀) * Q = (1 / t) • (Qᵀ * C₀ * Q) := fun t => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hmain : Tendsto (fun t : ℝ => 1 / 2 * ∑ i, ∑ j, lam i * lam j * (t * ((2 * (η / t) * (if i =
      j then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (1 / t * (Qᵀ * C₀ * Q) i j)) / (1 - (1 - (η / t) * (t
      * lam i + g)) * (1 - (η / t) * (t * lam j + g))))) ^ 2 * ((1 + (1 - (η / t) * (t * lam j + g))
      ^ 2) / (1 - (1 - (η / t) * (t * lam j + g)) ^ 2))) atTop (𝓝 (1 / 2 * ∑ i, ∑ j, lam i * lam j *
      ((2 * η * (if i = j then 1 else 0) + η ^ 2 * (Qᵀ * C₀ * Q) i j) / (1 - (1 - η * lam i) * (1 -
      η * lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 - η * lam j))))) :=
    (tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ =>
      ((tendsto_const_nhds (x := lam i * lam j)).mul
        ((mbEntry_lin_scaled_tendsto (g := g) (hlam i) (hlam j) hη (hηl i) (hηl j) (if i = j then 1
            else 0)
          ((Qᵀ * C₀ * Q) i j)).pow 2)).mul (iat_quad_scaled_tendsto (g := g) (hlam j) hη (hηl
              j))).const_mul
      (1 / 2)
  have hmean : Tendsto (fun t : ℝ => ∑ i, ∑ j, lam i * lam j * (t * (g * affineFrame Q c w₀ i / (t *
      lam i + g))) * (t * (g * affineFrame Q c w₀ j / (t * lam j + g))) * ((2 * (η / t) * (if i = j
      then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (1 / t * (Qᵀ * C₀ * Q) i j)) / (1 - (1 - (η / t) * (t *
      lam i + g)) * (1 - (η / t) * (t * lam j + g)))) * ((1 + (1 - (η / t) * (t * lam j + g))) / (1
      - (1 - (η / t) * (t * lam j + g))))) atTop (𝓝 (∑ i : Fin d, ∑ j : Fin d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ => by
      have := ((((tendsto_const_nhds (x := lam i * lam j)).mul
        (mul_anchoredMean_tendsto (hlam i) hg (affineFrame Q c w₀ i))).mul
        (mul_anchoredMean_tendsto (hlam j) hg (affineFrame Q c w₀ j))).mul
        (mbEntry_lin_tendsto_zero (g := g) (hlam i) (hlam j) hη (hηl i) (hηl j) (if i = j then 1
            else 0)
          ((Qᵀ * C₀ * Q) i j))).mul (iat_lin_scaled_tendsto (g := g) (hlam j) hη)
      simpa using this
  have hF := hmain.add hmean
  simp only [Finset.sum_const_zero, add_zero] at hF
  refine hF.congr' ?_
  filter_upwards [hev] with t ⟨ht, hev⟩
  rw [mbAnchored_longRunVar hlam hQ c w₀ hg ht (div_pos hη ht) hev (hC₀.smul (by positivity : (0 :
      ℝ) ≤ 1 / t))]
  simp only [hCt, Matrix.smul_apply, smul_eq_mul]
  rw [mul_add]
  congr 1
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `L_∞ > 0` as soon as one frame entry of the gradient-noise covariance is nonzero. -/
theorem Linf_pos_of_ne (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2)
    (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (hne : (Qᵀ * C * Q) i j ≠ 0) :
    0 < 1 / 2 * ∑ i, ∑ j, lam i * lam j * (η ^ 2 * (Qᵀ * C * Q) i j / (1 - (1 - η * lam i) * (1 - η
        * lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 - η * lam j))) := by
  have hpos : ∀ a b : Fin d, 0 ≤ lam a * lam b * (η ^ 2 * (Qᵀ * C * Q) a b /
      (1 - (1 - η * lam a) * (1 - η * lam b))) ^ 2 *
      ((1 + (1 - η * lam b) ^ 2) / (η * lam b * (2 - η * lam b))) := fun a b =>
    mul_nonneg (mul_nonneg (mul_pos (hlam a) (hlam b)).le (sq_nonneg _))
      (div_nonneg (by positivity) (mul_pos (mul_pos hη (hlam b)) (by linarith [hηl b])).le)
  refine mul_pos (by norm_num) (Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ => hpos a b)
    ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun b _ => hpos i b) ⟨j, Finset.mem_univ _, ?_⟩⟩)
  have hD := one_sub_rho_mul_pos (hlam i) (hlam j) hη (hηl i) (hηl j)
  have hx : η ^ 2 * (Qᵀ * C * Q) i j / (1 - (1 - η * lam i) * (1 - η * lam j)) ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero 2 hη.ne') hne) hD.ne'
  exact mul_pos (mul_pos (mul_pos (hlam i) (hlam j)) (sq_pos_iff.2 hx))
    (div_pos (by positivity) (mul_pos (mul_pos hη (hlam j)) (by linarith [hηl j])))

/-! ### Comparison with the exact-gradient limit -/

/-- `L_lin(C₀ = 0) = L_η`: linear batch growth with vanishing noise recovers tide 103's limit. -/
theorem Llin_zero_eq (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) :
    1 / 2 * ∑ i, ∑ j, lam i * lam j * ((2 * η * (if i = j then 1 else 0) + η ^ 2 * (Qᵀ * (0 : Matrix
      (Fin d) (Fin d) ℝ) * Q) i j) / (1 - (1 - η * lam i) * (1 - η * lam j))) ^ 2 * ((1 + (1 - η *
      lam j) ^ 2) / (η * lam j * (2 - η * lam j))) = ∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i
      * (1 - η * lam i / 2) ^ 3) := by
  have key : ∀ i j : Fin d, 1 / 2 * (lam i * lam j * ((2 * η * (if i = j then 1 else 0) +
      η ^ 2 * (Qᵀ * (0 : Matrix (Fin d) (Fin d) ℝ) * Q) i j) / (1 - (1 - η * lam i) * (1 - η * lam
          j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 - η * lam j)))) =
      if i = j then (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) else 0 :=
          by
    intro i j
    simp only [Matrix.zero_mul, Matrix.zero_apply, mul_zero, add_zero]
    split_ifs with hij
    · subst hij
      have hx := mul_pos hη (hlam i)
      have hk : 2 - η * lam i ≠ 0 := by linarith [hηl i]
      have hk' : 1 - η * lam i / 2 ≠ 0 := by linarith [hηl i]
      have e : 1 - (1 - η * lam i) * (1 - η * lam i) = η * lam i * (2 - η * lam i) := by ring
      rw [e]
      field_simp
      ring
    · simp
  simp only [Finset.mul_sum, key, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- `L_η ≤ L_lin` for `C₀ ⪰ 0`: exact-gradient ULA is the best case of linear batch growth. -/
theorem Leta_le_Llin (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2)
    {C₀ : Matrix (Fin d) (Fin d) ℝ} (hC₀ : C₀.PosSemidef) :
    ∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) ≤ 1 / 2 * ∑ i, ∑ j,
      lam i * lam j * ((2 * η * (if i = j then 1 else 0) + η ^ 2 * (Qᵀ * C₀ * Q) i j) / (1 - (1 - η
      * lam i) * (1 - η * lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 - η * lam j)))
      := by
  have hCU : (Qᵀ * C₀ * Q).PosSemidef := by
    have := hC₀.conjTranspose_mul_mul_same Q
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [← Llin_zero_eq (Q := Q) hlam hη hηl]
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hw : 0 ≤ ((1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 - η * lam j))) :=
    div_nonneg (by positivity) (mul_pos (mul_pos hη (hlam j)) (by linarith [hηl j])).le
  have hD := one_sub_rho_mul_pos (hlam i) (hlam j) hη (hηl i) (hηl j)
  have hsq : ((2 * η * (if i = j then 1 else 0) + η ^ 2 * (Qᵀ * (0 : Matrix (Fin d) (Fin d) ℝ) * Q)
      i j) /
      (1 - (1 - η * lam i) * (1 - η * lam j))) ^ 2 ≤ ((2 * η * (if i = j then 1 else 0) + η ^ 2 *
          (Qᵀ * C₀ * Q) i j) / (1 - (1 - η * lam i) * (1 - η * lam j))) ^ 2 := by
    rw [div_pow, div_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    simp only [Matrix.zero_mul, Matrix.zero_apply, mul_zero, add_zero]
    split_ifs with hij
    · subst hij
      have hc : 0 ≤ (Qᵀ * C₀ * Q) i i := hCU.diag_nonneg
      have hη2 : 0 ≤ η ^ 2 * (Qᵀ * C₀ * Q) i i := by positivity
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    · simp only [mul_zero, zero_add, zero_pow two_ne_zero]
      positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (mul_pos (hlam i) (hlam j)).le) hw) (by norm_num)

end Scaled

end Laplace.Multi
