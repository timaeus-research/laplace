/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MinibatchScaled

/-!
# The general scaled-noise regime for the minibatch long-run variance (E8 + E5)

Tide 106 evaluated the β-scaled limit of tide 105's minibatch long-run variance `τ²_mb` for a fixed
gradient-noise covariance
(`t²τ²_mb → ∞`) and for linear batch growth `C = C₀/t` (`t²τ²_mb → L_lin`). This file organises the
batch regimes around the
scaled frame noise `t·Ĉ_t`, `Ĉ = QᵀCQ`:
* **the limit functional** `scaledNoiseLimit lam η B̂ = ½∑ᵢⱼλᵢλⱼ((2ηδᵢⱼ +
η²B̂ᵢⱼ)/dᵢⱼ)²(1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))`,
  `dᵢⱼ = 1 − (1−ηλᵢ)(1−ηλⱼ)`, with `scaledNoiseLimit lam η 0 = L_η` (`scaledNoiseLimit_zero`) and
  tide 106's
  `L_lin = scaledNoiseLimit lam η Ĉ₀` (`Llin_eq_scaledNoiseLimit`);
* **the general regime** (`mbGeneral_longRunVar_tendsto`): if `C_t` is eventually PSD and
`t·(QᵀC_tQ)ᵢⱼ → B̂ᵢⱼ`, then
  `t²τ²_mb(t) → scaledNoiseLimit lam η B̂`; the mean part is `A_mean/t + o(1/t)` with `A_mean`
  explicit
  (`mbGeneral_meanPart_mul_tendsto`);
* **the batch trichotomy** for `C_t = C_g/n_t`: `n_t → ∞` with `n_t/t → 0` gives `t²τ²_mb → ∞`
(`mbBatch_longRunVar_tendsto_atTop`,
  once some frame diagonal entry of `C_g` is positive); `n_t/t → ν ∈ (0,∞)` gives `scaledNoiseLimit
  lam η (Ĉ_g/ν)`
  (`mbBatch_longRunVar_tendsto`); `n_t/t → ∞` gives the exact-gradient value `L_η`
  (`mbBatch_longRunVar_tendsto_Leta`,
  `mbGeneral_longRunVar_tendsto_Leta`, `mbScaled_quad_longRunVar_tendsto`): the inflation is set by
  the ratio of batch size
  to inverse temperature;
* **monotonicity and strictness**: `scaledNoiseLimit` is monotone (strictly, given one strict
entry) under entrywise
  `|B̂₁ᵢⱼ| ≤ |B̂₂ᵢⱼ|` with nonnegative diagonals (`scaledNoiseLimit_mono`, `scaledNoiseLimit_lt`),
  `L_η ≤ scaledNoiseLimit lam η B̂`
  (`Leta_le_scaledNoiseLimit`), `L_η < scaledNoiseLimit lam η B̂ ⟺ B̂ ≠ 0`
  (`Leta_lt_scaledNoiseLimit_iff`), `L_η < L_lin` for PSD
  `C₀ ≠ 0` (`Leta_lt_Llin`), and the batch limit strictly decreases in `ν` for `C_g ≠ 0`
  (`scaledNoiseLimit_batch_anti`,
  `scaledNoiseLimit_batch_anti_strict`).
-/

open Matrix Filter Topology

namespace Laplace.Multi

/-! ### The limit functional -/

/-- The β-scaled minibatch long-run variance limit as a function of the scaled frame noise `B̂ =
lim t·QᵀC_tQ`. -/
noncomputable def scaledNoiseLimit {d : ℕ} (lam : Fin d → ℝ) (η : ℝ) (B : Fin d → Fin d → ℝ) : ℝ :=
  1 / 2 * ∑ i, ∑ j, lam i * lam j * ((2 * η * (if i = j then 1 else 0) + η ^ 2 * B i j) /
    (1 - (1 - η * lam i) * (1 - η * lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 - η
        * lam j)))

section Weight

variable {d : ℕ} {lam : Fin d → ℝ} {η : ℝ}

/-- The positive weight `(1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))`. -/
theorem iat_weight_pos (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) (j : Fin d) :
    0 < (1 + (1 - η * lam j) ^ 2) / (η * lam j * (2 - η * lam j)) :=
  div_pos (by positivity) (mul_pos (mul_pos hη (hlam j)) (by linarith [hηl j]))

end Weight

section Scalar

variable {lam₁ lam₂ g η : ℝ}

/-- General scaled noise: if `t·c(t) → b` then `t·(2(η/t)δ + (η/t)²t²c(t))/(1 − ρᵢρⱼ) → (2ηδ +
η²b)/(1 − (1−ηλᵢ)(1−ηλⱼ))`. -/
theorem mbEntry_general_scaled_tendsto (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hη : 0 < η)
    (hηl₁ : η * lam₁ < 2) (hηl₂ : η * lam₂ < 2) (δ : ℝ) {c : ℝ → ℝ} {b : ℝ}
    (hc : Tendsto (fun t : ℝ => t * c t) atTop (𝓝 b)) :
    Tendsto (fun t : ℝ => t * ((2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * c t) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g))))) atTop
      (𝓝 ((2 * η * δ + η ^ 2 * b) / (1 - (1 - η * lam₁) * (1 - η * lam₂)))) := by
  have e : (fun t : ℝ => (2 * η * δ + η ^ 2 * (t * c t)) /
      (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) =ᶠ[atTop]
      fun t => t * ((2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * c t) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    rw [← mul_div_assoc]
    congr 1
    field_simp
  exact (((tendsto_const_nhds (x := 2 * η * δ)).add ((tendsto_const_nhds (x := η ^ 2)).mul hc)).div
    (one_sub_rho_mul_scaled_tendsto lam₁ lam₂ g η)
    (one_sub_rho_mul_pos hlam₁ hlam₂ hη hηl₁ hηl₂).ne').congr' e

/-- General scaled noise: the unscaled entry vanishes. -/
theorem mbEntry_general_tendsto_zero (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hη : 0 < η)
    (hηl₁ : η * lam₁ < 2) (hηl₂ : η * lam₂ < 2) (δ : ℝ) {c : ℝ → ℝ} {b : ℝ}
    (hc : Tendsto (fun t : ℝ => t * c t) atTop (𝓝 b)) :
    Tendsto (fun t : ℝ => (2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * c t) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) atTop (𝓝 0) := by
  refine ((mbEntry_general_scaled_tendsto (g := g) hlam₁ hlam₂ hη hηl₁ hηl₂ δ hc).div_atTop
    tendsto_id).congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  exact mul_div_cancel_left₀ _ ht

/-- Growing batch: the unscaled entry `(2(η/t)δ + (η/t)²t²(c/n_t))/(1 − ρᵢρⱼ)` vanishes when `n_t →
∞`. -/
theorem mbEntry_batch_tendsto_zero (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hη : 0 < η)
    (hηl₁ : η * lam₁ < 2) (hηl₂ : η * lam₂ < 2) (δ c : ℝ) {n : ℝ → ℝ} (hn : Tendsto n atTop atTop) :
    Tendsto (fun t : ℝ => (2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * (1 / n t * c)) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) atTop (𝓝 0) := by
  have e : (fun t : ℝ => (2 * η * δ / t + η ^ 2 * c / n t) /
      (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g)))) =ᶠ[atTop]
      fun t => (2 * (η / t) * δ + (η / t) ^ 2 * t ^ 2 * (1 / n t * c)) /
        (1 - (1 - η / t * (t * lam₁ + g)) * (1 - η / t * (t * lam₂ + g))) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ), hn.eventually_gt_atTop 0] with t ht hnt
    have hn0 := hnt.ne'
    congr 1
    field_simp
  have hnum : Tendsto (fun t : ℝ => 2 * η * δ / t + η ^ 2 * c / n t) atTop (𝓝 (0 + 0)) :=
    ((tendsto_const_nhds (x := 2 * η * δ)).div_atTop tendsto_id).add
      ((tendsto_const_nhds (x := η ^ 2 * c)).div_atTop hn)
  rw [add_zero] at hnum
  have h := hnum.div (one_sub_rho_mul_scaled_tendsto lam₁ lam₂ g η)
    (one_sub_rho_mul_pos hlam₁ hlam₂ hη hηl₁ hηl₂).ne'
  rw [zero_div] at h
  exact h.congr' e

end Scalar

/-! ### The anchored model: quadratic and mean parts -/

section Anchored

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g η : ℝ}

/-- `t²τ²_mb` at the β-scaled step, split into the quadratic part (with `t`-scaled entries) and the
mean part. -/
theorem mbAnchored_sq_longRunVar_eq (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) {t : ℝ} (ht : 0 < t) (hev : ∀ i, η / t * (t * lam i + g) < 2)
    {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) :
    t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d)
      (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t C ((t • (Q * diagonal
      lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) = 1 / 2 * ∑ i, ∑ j, lam i
      * lam j * (t * ((2 * (η / t) * (if i = j then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * C * Q) i
      j) / (1 - (1 - (η / t) * (t * lam i + g)) * (1 - (η / t) * (t * lam j + g))))) ^ 2 * ((1 + (1
      - (η / t) * (t * lam j + g)) ^ 2) / (1 - (1 - (η / t) * (t * lam j + g)) ^ 2)) + ∑ i, ∑ j, lam
      i * lam j * (t * (g * affineFrame Q c w₀ i / (t * lam i + g))) * (t * (g * affineFrame Q c w₀
      j / (t * lam j + g))) * ((2 * (η / t) * (if i = j then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ *
      C * Q) i j) / (1 - (1 - (η / t) * (t * lam i + g)) * (1 - (η / t) * (t * lam j + g)))) * ((1 +
      (1 - (η / t) * (t * lam j + g))) / (1 - (1 - (η / t) * (t * lam j + g)))) := by
  rw [mbAnchored_longRunVar hlam hQ c w₀ hg ht (div_pos hη ht) hev hC, mul_add]
  congr 1
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The mean part of `t²τ²_mb` vanishes whenever the frame entries do. -/
theorem mbMeanPart_tendsto_zero (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) (hη : 0 < η)
    (Q : Matrix (Fin d) (Fin d) ℝ) (c w₀ : Fin d → ℝ) (E : Fin d → Fin d → ℝ → ℝ)
    (hE : ∀ i j, Tendsto (E i j) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => ∑ i, ∑ j, lam i * lam j * (t * (g * affineFrame Q c w₀ i / (t * lam i +
      g))) * (t * (g * affineFrame Q c w₀ j / (t * lam j + g))) * E i j t * ((1 + (1 - (η / t) * (t
      * lam j + g))) / (1 - (1 - (η / t) * (t * lam j + g))))) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => ∑ i, ∑ j, lam i * lam j * (t * (g * affineFrame Q c w₀ i / (t * lam
      i + g))) * (t * (g * affineFrame Q c w₀ j / (t * lam j + g))) * E i j t * ((1 + (1 - (η / t) *
      (t * lam j + g))) / (1 - (1 - (η / t) * (t * lam j + g))))) atTop (𝓝 (∑ i : Fin d, ∑ j : Fin
      d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ => by
      have := ((((tendsto_const_nhds (x := lam i * lam j)).mul
        (mul_anchoredMean_tendsto (hlam i) hg (affineFrame Q c w₀ i))).mul
        (mul_anchoredMean_tendsto (hlam j) hg (affineFrame Q c w₀ j))).mul (hE i j)).mul
        (iat_lin_scaled_tendsto (g := g) (hlam j) hη)
      simpa using this
  simpa using h

end Anchored

/-! ### The general regime -/

section General

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g η : ℝ}

/-- **The general scaled-noise regime**: `C_t` eventually PSD with `t·(QᵀC_tQ)ᵢⱼ → B̂ᵢⱼ` gives
`t²τ²_mb(t) → scaledNoiseLimit lam η B̂`. -/
theorem mbGeneral_longRunVar_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {C : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hC : ∀ᶠ t : ℝ in atTop, (C t).PosSemidef) {B : Fin d → Fin d → ℝ}
    (hB : ∀ i j, Tendsto (fun t : ℝ => t * (Qᵀ * C t * Q) i j) atTop (𝓝 (B i j))) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t (C
      t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))))
      atTop (𝓝 (scaledNoiseLimit lam η B)) := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ ∀ i, η / t * (t * lam i + g) < 2 :=
    (eventually_gt_atTop 0).and (Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1))
  have hmain : Tendsto (fun t : ℝ => 1 / 2 * ∑ i, ∑ j, lam i * lam j * (t * ((2 * (η / t) * (if i =
      j then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * (C t) * Q) i j) / (1 - (1 - (η / t) * (t * lam
      i + g)) * (1 - (η / t) * (t * lam j + g))))) ^ 2 * ((1 + (1 - (η / t) * (t * lam j + g)) ^ 2)
      / (1 - (1 - (η / t) * (t * lam j + g)) ^ 2))) atTop (𝓝 (scaledNoiseLimit lam η B)) :=
    (tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ =>
      ((tendsto_const_nhds (x := lam i * lam j)).mul
        ((mbEntry_general_scaled_tendsto (g := g) (hlam i) (hlam j) hη (hηl i) (hηl j)
          (if i = j then 1 else 0) (hB i j)).pow 2)).mul
        (iat_quad_scaled_tendsto (g := g) (hlam j) hη (hηl j))).const_mul (1 / 2)
  have hmean : Tendsto (fun t : ℝ => ∑ i, ∑ j, lam i * lam j * (t * (g * affineFrame Q c w₀ i / (t *
      lam i + g))) * (t * (g * affineFrame Q c w₀ j / (t * lam j + g))) * ((2 * (η / t) * (if i = j
      then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * (C t) * Q) i j) / (1 - (1 - (η / t) * (t * lam i
      + g)) * (1 - (η / t) * (t * lam j + g)))) * ((1 + (1 - (η / t) * (t * lam j + g))) / (1 - (1 -
      (η / t) * (t * lam j + g))))) atTop (𝓝 0) :=
    mbMeanPart_tendsto_zero hlam hg hη Q c w₀ (fun i j t => ((2 * (η / t) * (if i = j then 1 else
        0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * (C t) * Q) i j) / (1 - (1 - (η / t) * (t * lam i + g)) *
            (1 - (η / t) * (t * lam j + g))))) fun i j =>
      mbEntry_general_tendsto_zero (g := g) (hlam i) (hlam j) hη (hηl i) (hηl j)
        (if i = j then 1 else 0) (hB i j)
  have hF := hmain.add hmean
  rw [add_zero] at hF
  refine hF.congr' ?_
  filter_upwards [hev, hC] with t ⟨ht, hevt⟩ hCt
  exact (mbAnchored_sq_longRunVar_eq hlam hQ c w₀ hg hη ht hevt hCt).symm

/-- **The mean coefficient**: under the general regime the mean part of `t²τ²_mb` is `A_mean/t +
o(1/t)`,
`A_mean = ∑ᵢⱼλᵢλⱼ(gŵᵢ/λᵢ)(gŵⱼ/λⱼ)((2ηδᵢⱼ + η²B̂ᵢⱼ)/dᵢⱼ)((2−ηλⱼ)/(ηλⱼ))`. -/
theorem mbGeneral_meanPart_mul_tendsto (hlam : ∀ i, 0 < lam i) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {C : ℝ → Matrix (Fin d) (Fin d) ℝ} {B : Fin d → Fin d →
        ℝ}
    (hB : ∀ i j, Tendsto (fun t : ℝ => t * (Qᵀ * C t * Q) i j) atTop (𝓝 (B i j))) :
    Tendsto (fun t : ℝ => t * ∑ i, ∑ j, lam i * lam j * (t * (g * affineFrame Q c w₀ i / (t * lam i
      + g))) * (t * (g * affineFrame Q c w₀ j / (t * lam j + g))) * ((2 * (η / t) * (if i = j then 1
      else 0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * (C t) * Q) i j) / (1 - (1 - (η / t) * (t * lam i + g)) *
      (1 - (η / t) * (t * lam j + g)))) * ((1 + (1 - (η / t) * (t * lam j + g))) / (1 - (1 - (η / t)
      * (t * lam j + g))))) atTop (𝓝 (∑ i, ∑ j, lam i * lam j * (g * affineFrame Q c w₀ i / lam i) *
      (g * affineFrame Q c w₀ j / lam j) * ((2 * η * (if i = j then 1 else 0) + η ^ 2 * B i j) / (1
      - (1 - η * lam i) * (1 - η * lam j))) * ((2 - η * lam j) / (η * lam j)))) := by
  have h := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
    tendsto_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) =>
      ((((tendsto_const_nhds (x := lam i * lam j)).mul
        (mul_anchoredMean_tendsto (hlam i) hg (affineFrame Q c w₀ i))).mul
        (mul_anchoredMean_tendsto (hlam j) hg (affineFrame Q c w₀ j))).mul
        (mbEntry_general_scaled_tendsto (g := g) (hlam i) (hlam j) hη (hηl i) (hηl j)
          (if i = j then 1 else 0) (hB i j))).mul (iat_lin_scaled_tendsto (g := g) (hlam j) hη)
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `scaledNoiseLimit lam η 0 = L_η`: the zero scaled noise recovers tide 103's exact-gradient
limit. -/
theorem scaledNoiseLimit_zero (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) :
    scaledNoiseLimit lam η (fun _ _ => 0) = ∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 -
        η * lam i / 2) ^ 3) := by
  have h := Llin_zero_eq (Q := (1 : Matrix (Fin d) (Fin d) ℝ)) hlam hη hηl
  simpa [scaledNoiseLimit] using h

/-- Tide 106's linear-growth limit is `scaledNoiseLimit lam η Ĉ₀`. -/
theorem Llin_eq_scaledNoiseLimit (C₀ : Matrix (Fin d) (Fin d) ℝ) :
    1 / 2 * ∑ i, ∑ j, lam i * lam j * ((2 * η * (if i = j then 1 else 0) + η ^ 2 * (Qᵀ * C₀ * Q) i
        j)
      / (1 - (1 - η * lam i) * (1 - η * lam j))) ^ 2 * ((1 + (1 - η * lam j) ^ 2) / (η * lam j *
      (2 - η * lam j))) = scaledNoiseLimit lam η (fun i j => (Qᵀ * C₀ * Q) i j) := rfl

/-- **Vanishing scaled noise**: `t·Ĉ_t → 0` gives the exact-gradient value `L_η`. -/
theorem mbGeneral_longRunVar_tendsto_Leta (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d →
    ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {C : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hC : ∀ᶠ t : ℝ in atTop, (C t).PosSemidef)
    (hB : ∀ i j, Tendsto (fun t : ℝ => t * (Qᵀ * C t * Q) i j) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t (C
      t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))))
      atTop (𝓝 (∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3))) := by
  have h := mbGeneral_longRunVar_tendsto hlam hQ c w₀ hg hη hηl hC (B := fun _ _ => 0) hB
  rwa [scaledNoiseLimit_zero hlam hη hηl] at h

/-- `C_t = C₀/t²`: `t²τ²_mb → L_η`. -/
theorem mbScaled_quad_longRunVar_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d →
    ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {C₀ : Matrix (Fin d) (Fin d) ℝ}
    (hC₀ : C₀.PosSemidef) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t ((1
      / t ^ 2) • C₀) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g •
      (w₀ - c)))) atTop (𝓝 (∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^
      3))) := by
  refine mbGeneral_longRunVar_tendsto_Leta hlam hQ c w₀ hg hη hηl
    (Filter.Eventually.of_forall fun t => hC₀.smul (by positivity)) fun i j => ?_
  have h := (tendsto_const_nhds (x := (Qᵀ * C₀ * Q) i j)).div_atTop (tendsto_id (x := atTop))
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  simp only [id_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- **Batch size against inverse temperature**: `C_t = C_g/n_t` with `n_t/t → ν > 0` gives
`scaledNoiseLimit lam η (Ĉ_g/ν)`. -/
theorem mbBatch_longRunVar_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {Cg : Matrix (Fin d) (Fin d) ℝ}
    (hCg : Cg.PosSemidef) {n : ℝ → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hn : Tendsto (fun t : ℝ => n t / t) atTop (𝓝 ν)) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t ((1
      / n t) • Cg) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀
      - c)))) atTop (𝓝 (scaledNoiseLimit lam η (fun i j => (Qᵀ * Cg * Q) i j / ν))) := by
  have hnpos : ∀ᶠ t : ℝ in atTop, 0 < n t := by
    filter_upwards [hn.eventually_const_lt (by linarith : ν / 2 < ν), eventually_gt_atTop (0 : ℝ)]
      with t ht ht0
    have : 0 < n t / t := lt_trans (by positivity) ht
    exact (div_pos_iff_of_pos_right ht0).1 this
  refine mbGeneral_longRunVar_tendsto hlam hQ c w₀ hg hη hηl
    (hnpos.mono fun t ht => hCg.smul (by positivity)) fun i j => ?_
  have h := (tendsto_const_nhds (x := (Qᵀ * Cg * Q) i j)).div hn hν.ne'
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ), hnpos] with t ht hnt
  have hn0 := hnt.ne'
  simp only [Pi.div_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- **Super-linear batch growth**: `n_t/t → ∞` gives the exact-gradient value `L_η`. -/
theorem mbBatch_longRunVar_tendsto_Leta (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {Cg : Matrix (Fin d) (Fin d) ℝ}
    (hCg : Cg.PosSemidef) {n : ℝ → ℝ} (hn : Tendsto (fun t : ℝ => n t / t) atTop atTop) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t ((1
      / n t) • Cg) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀
      - c)))) atTop (𝓝 (∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3)))
      := by
  have hnpos : ∀ᶠ t : ℝ in atTop, 0 < n t := by
    filter_upwards [hn.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    exact (div_pos_iff_of_pos_right ht0).1 ht
  refine mbGeneral_longRunVar_tendsto_Leta hlam hQ c w₀ hg hη hηl
    (hnpos.mono fun t ht => hCg.smul (by positivity)) fun i j => ?_
  have h := (tendsto_const_nhds (x := (Qᵀ * Cg * Q) i j)).div_atTop hn
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ), hnpos] with t ht hnt
  have hn0 := hnt.ne'
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- **Sub-linear batch growth diverges**: `C_t = C_g/n_t` with `n_t → ∞`, `n_t/t → 0` and a
positive frame diagonal
entry `(QᵀC_gQ)ᵢᵢ > 0` gives `t²τ²_mb → ∞`. -/
theorem mbBatch_longRunVar_tendsto_atTop (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d →
    ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {Cg : Matrix (Fin d) (Fin d) ℝ}
    (hCg : Cg.PosSemidef) {i₀ : Fin d} (hii : 0 < (Qᵀ * Cg * Q) i₀ i₀) {n : ℝ → ℝ}
    (hn : Tendsto n atTop atTop) (hn0 : Tendsto (fun t : ℝ => n t / t) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.mbLongRunVar Q (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (fun i => t * lam i + g) (η / t) t ((1
      / n t) • Cg) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀
      - c)))) atTop atTop := by
  have hnpos : ∀ᶠ t : ℝ in atTop, 0 < n t := hn.eventually_gt_atTop 0
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ ∀ i, η / t * (t * lam i + g) < 2 :=
    (eventually_gt_atTop 0).and (Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1))
  have hratio : Tendsto (fun t : ℝ => t / n t) atTop atTop := by
    have h1 : Tendsto (fun t : ℝ => n t / t) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hn0, (hnpos.and (eventually_gt_atTop 0)).mono fun t ht =>
        div_pos ht.1 ht.2⟩
    refine h1.inv_tendsto_nhdsGT_zero.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp [inv_div]
  have hD := one_sub_rho_mul_pos (hlam i₀) (hlam i₀) hη (hηl i₀) (hηl i₀)
  have hS : Tendsto (fun t : ℝ => ((2 * η + η ^ 2 * (Qᵀ * Cg * Q) i₀ i₀ * (t / n t)) * (1 - (1 - (η
      / t) * (t * lam i₀ + g)) * (1 - (η / t) * (t * lam i₀ + g)))⁻¹)) atTop atTop :=
    (tendsto_atTop_add_const_left _ _ (hratio.const_mul_atTop (mul_pos (pow_pos hη 2)
        hii))).atTop_mul_pos
      (inv_pos.2 hD) ((one_sub_rho_mul_scaled_tendsto (lam i₀) (lam i₀) g η).inv₀ hD.ne')
  have hsq : Tendsto (fun t : ℝ => ((2 * η + η ^ 2 * (Qᵀ * Cg * Q) i₀ i₀ * (t / n t)) * (1 - (1 - (η
      / t) * (t * lam i₀ + g)) * (1 - (η / t) * (t * lam i₀ + g)))⁻¹) ^ 2) atTop atTop := by
    simpa [sq] using hS.atTop_mul_atTop₀ hS
  have hterm : Tendsto (fun t : ℝ => 1 / 2 * (lam i₀ * lam i₀ * ((2 * η + η ^ 2 * (Qᵀ * Cg * Q) i₀
      i₀ * (t / n t)) * (1 - (1 - (η / t) * (t * lam i₀ + g)) * (1 - (η / t) * (t * lam i₀ + g)))⁻¹)
      ^ 2 * ((1 + (1 - (η / t) * (t * lam i₀ + g)) ^ 2) / (1 - (1 - (η / t) * (t * lam i₀ + g)) ^
      2)))) atTop atTop := by
    have := (hsq.atTop_mul_pos (iat_weight_pos hlam hη hηl i₀)
      (iat_quad_scaled_tendsto (g := g) (hlam i₀) hη (hηl i₀))).const_mul_atTop
      (by have := hlam i₀; positivity : (0 : ℝ) < 1 / 2 * (lam i₀ * lam i₀))
    exact this.congr' (Filter.Eventually.of_forall fun t => by ring)
  have hmean : Tendsto (fun t : ℝ => ∑ i, ∑ j, lam i * lam j * (t * (g * affineFrame Q c w₀ i / (t *
      lam i + g))) * (t * (g * affineFrame Q c w₀ j / (t * lam j + g))) * ((2 * (η / t) * (if i = j
      then 1 else 0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * ((1 / n t) • Cg) * Q) i j) / (1 - (1 - (η / t) *
      (t * lam i + g)) * (1 - (η / t) * (t * lam j + g)))) * ((1 + (1 - (η / t) * (t * lam j + g)))
      / (1 - (1 - (η / t) * (t * lam j + g))))) atTop (𝓝 0) :=
    mbMeanPart_tendsto_zero hlam hg hη Q c w₀ (fun i j t => ((2 * (η / t) * (if i = j then 1 else
        0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * ((1 / n t) • Cg) * Q) i j) / (1 - (1 - (η / t) * (t * lam
            i + g)) * (1 - (η / t) * (t * lam j + g))))) fun i j =>
      (mbEntry_batch_tendsto_zero (g := g) (hlam i) (hlam j) hη (hηl i) (hηl j)
        (if i = j then 1 else 0) ((Qᵀ * Cg * Q) i j) hn).congr' (Filter.Eventually.of_forall fun t
            => by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul])
  refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-1) hterm)
  filter_upwards [hev, hnpos, hmean.eventually (eventually_ge_nhds (by norm_num : (-1 : ℝ) < 0))]
    with t ⟨ht, hevt⟩ hnt hm
  rw [mbAnchored_sq_longRunVar_eq hlam hQ c w₀ hg hη ht hevt (hCg.smul (by positivity))]
  have hpos : ∀ b : Fin d, 0 < 1 - (1 - η / t * (t * lam b + g)) ^ 2 := fun b => by
    have hx : 0 < η / t * (t * lam b + g) := by have := hlam b; positivity
    have e : 1 - (1 - η / t * (t * lam b + g)) ^ 2 =
        η / t * (t * lam b + g) * (2 - η / t * (t * lam b + g)) := by ring
    rw [e]
    exact mul_pos hx (by linarith [hevt b])
  have hf : ∀ a b : Fin d, 0 ≤ lam a * lam b * (t * ((2 * (η / t) * (if a = b then 1 else 0) + (η /
      t) ^ 2 * t ^ 2 * (Qᵀ * ((1 / n t) • Cg) * Q) a b) / (1 - (1 - (η / t) * (t * lam a + g)) * (1
      - (η / t) * (t * lam b + g))))) ^ 2 * ((1 + (1 - (η / t) * (t * lam b + g)) ^ 2) / (1 - (1 -
      (η / t) * (t * lam b + g)) ^ 2)) := fun a b => by
    have h1 := hlam a
    have h2 := hlam b
    exact mul_nonneg (mul_nonneg (mul_pos h1 h2).le (sq_nonneg _)) (div_nonneg (by positivity)
        (hpos b).le)
  have hle : lam i₀ * lam i₀ * (t * ((2 * (η / t) * (if i₀ = i₀ then 1 else 0) + (η / t) ^ 2 * t ^ 2
      * (Qᵀ * ((1 / n t) • Cg) * Q) i₀ i₀) / (1 - (1 - (η / t) * (t * lam i₀ + g)) * (1 - (η / t) *
      (t * lam i₀ + g))))) ^ 2 * ((1 + (1 - (η / t) * (t * lam i₀ + g)) ^ 2) / (1 - (1 - (η / t) *
      (t * lam i₀ + g)) ^ 2)) ≤ ∑ a, ∑ b, lam a * lam b * (t * ((2 * (η / t) * (if a = b then 1 else
      0) + (η / t) ^ 2 * t ^ 2 * (Qᵀ * ((1 / n t) • Cg) * Q) a b) / (1 - (1 - (η / t) * (t * lam a +
      g)) * (1 - (η / t) * (t * lam b + g))))) ^ 2 * ((1 + (1 - (η / t) * (t * lam b + g)) ^ 2) / (1
      - (1 - (η / t) * (t * lam b + g)) ^ 2)) :=
    le_trans (Finset.single_le_sum (fun b _ => hf i₀ b) (Finset.mem_univ i₀))
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => hf a b) (Finset.mem_univ i₀))
  have hSe : ((2 * η + η ^ 2 * (Qᵀ * Cg * Q) i₀ i₀ * (t / n t)) * (1 - (1 - (η / t) * (t * lam i₀ +
      g)) * (1 - (η / t) * (t * lam i₀ + g)))⁻¹) = t * ((2 * (η / t) * (if i₀ = i₀ then 1 else 0) +
      (η / t) ^ 2 * t ^ 2 * (Qᵀ * ((1 / n t) • Cg) * Q) i₀ i₀) / (1 - (1 - (η / t) * (t * lam i₀ +
      g)) * (1 - (η / t) * (t * lam i₀ + g)))) := by
    have hDt : (1 - (1 - η / t * (t * lam i₀ + g)) * (1 - η / t * (t * lam i₀ + g))) ≠ 0 := by
      have := hpos i₀
      rw [sq] at this
      exact this.ne'
    have hif : (if i₀ = i₀ then (1 : ℝ) else 0) = 1 := if_pos rfl
    rw [hif]
    have hn0 := hnt.ne'
    have ht0 := ht.ne'
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    field_simp
  rw [hSe]
  linarith [mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 1 / 2)]

end General

/-! ### Monotonicity and strictness -/

section Order

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {η : ℝ}

/-- The squared frame entry is monotone under `|b₁| ≤ |b₂|` with nonnegative diagonals. -/
theorem entry_sq_mono (hη : 0 < η) {b₁ b₂ : ℝ} (i j : Fin d) (hd : i = j → 0 ≤ b₁ ∧ 0 ≤ b₂)
    (hab : |b₁| ≤ |b₂|) :
    (2 * η * (if i = j then 1 else 0) + η ^ 2 * b₁) ^ 2 ≤
      (2 * η * (if i = j then 1 else 0) + η ^ 2 * b₂) ^ 2 := by
  split_ifs with hij
  · obtain ⟨h1, h2⟩ := hd hij
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at hab
    have : 0 ≤ 2 * η * 1 + η ^ 2 * b₁ := by positivity
    exact pow_le_pow_left₀ this (by nlinarith [sq_nonneg η]) 2
  · simp only [mul_zero, zero_add, mul_pow]
    exact mul_le_mul_of_nonneg_left (sq_le_sq.2 hab) (by positivity)

/-- The squared frame entry is strictly monotone under `|b₁| < |b₂|` with nonnegative diagonals. -/
theorem entry_sq_lt (hη : 0 < η) {b₁ b₂ : ℝ} (i j : Fin d) (hd : i = j → 0 ≤ b₁ ∧ 0 ≤ b₂)
    (hab : |b₁| < |b₂|) :
    (2 * η * (if i = j then 1 else 0) + η ^ 2 * b₁) ^ 2 <
      (2 * η * (if i = j then 1 else 0) + η ^ 2 * b₂) ^ 2 := by
  split_ifs with hij
  · obtain ⟨h1, h2⟩ := hd hij
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at hab
    have h3 : η ^ 2 * b₁ < η ^ 2 * b₂ := mul_lt_mul_of_pos_left hab (by positivity)
    have h4 : 0 ≤ η ^ 2 * b₁ := by positivity
    exact sq_lt_sq' (by linarith) (by linarith)
  · simp only [mul_zero, zero_add, mul_pow]
    exact mul_lt_mul_of_pos_left (sq_lt_sq.2 hab) (by positivity)

/-- **Monotonicity**: `|B₁ᵢⱼ| ≤ |B₂ᵢⱼ|` entrywise with nonnegative diagonals gives
`scaledNoiseLimit lam η B₁ ≤ scaledNoiseLimit lam η B₂`. -/
theorem scaledNoiseLimit_mono (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2)
    {B₁ B₂ : Fin d → Fin d → ℝ} (hd₁ : ∀ i, 0 ≤ B₁ i i) (hd₂ : ∀ i, 0 ≤ B₂ i i)
    (hab : ∀ i j, |B₁ i j| ≤ |B₂ i j|) :
    scaledNoiseLimit lam η B₁ ≤ scaledNoiseLimit lam η B₂ := by
  unfold scaledNoiseLimit
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    (by norm_num)
  have hD := one_sub_rho_mul_pos (hlam i) (hlam j) hη (hηl i) (hηl j)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (mul_pos (hlam i) (hlam j)).le)
    (iat_weight_pos hlam hη hηl j).le
  rw [div_pow, div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact entry_sq_mono hη i j (fun h => by subst h; exact ⟨hd₁ _, hd₂ _⟩) (hab i j)

/-- **Strict monotonicity**: one strict entry `|B₁ᵢⱼ| < |B₂ᵢⱼ|` gives `scaledNoiseLimit lam η B₁ <
scaledNoiseLimit lam η B₂`. -/
theorem scaledNoiseLimit_lt (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2)
    {B₁ B₂ : Fin d → Fin d → ℝ} (hd₁ : ∀ i, 0 ≤ B₁ i i) (hd₂ : ∀ i, 0 ≤ B₂ i i)
    (hab : ∀ i j, |B₁ i j| ≤ |B₂ i j|) (hlt : ∃ i j, |B₁ i j| < |B₂ i j|) :
    scaledNoiseLimit lam η B₁ < scaledNoiseLimit lam η B₂ := by
  obtain ⟨i, j, hij⟩ := hlt
  unfold scaledNoiseLimit
  refine mul_lt_mul_of_pos_left ?_ (by norm_num)
  have hle : ∀ a b : Fin d, lam a * lam b * ((2 * η * (if a = b then 1 else 0) + η ^ 2 * B₁ a b) /
      (1 - (1 - η * lam a) * (1 - η * lam b))) ^ 2 *
      ((1 + (1 - η * lam b) ^ 2) / (η * lam b * (2 - η * lam b))) ≤
      lam a * lam b * ((2 * η * (if a = b then 1 else 0) + η ^ 2 * B₂ a b) /
      (1 - (1 - η * lam a) * (1 - η * lam b))) ^ 2 *
      ((1 + (1 - η * lam b) ^ 2) / (η * lam b * (2 - η * lam b))) := fun a b => by
    have hD := one_sub_rho_mul_pos (hlam a) (hlam b) hη (hηl a) (hηl b)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (mul_pos (hlam a) (hlam b)).le)
      (iat_weight_pos hlam hη hηl b).le
    rw [div_pow, div_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact entry_sq_mono hη a b (fun h => by subst h; exact ⟨hd₁ _, hd₂ _⟩) (hab a b)
  refine Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => hle a b)
    ⟨i, Finset.mem_univ _, Finset.sum_lt_sum (fun b _ => hle i b) ⟨j, Finset.mem_univ _, ?_⟩⟩
  have hD := one_sub_rho_mul_pos (hlam i) (hlam j) hη (hηl i) (hηl j)
  refine mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left ?_ (mul_pos (hlam i) (hlam j)))
    (iat_weight_pos hlam hη hηl j)
  rw [div_pow, div_pow]
  refine div_lt_div_of_pos_right ?_ (by positivity)
  exact entry_sq_lt hη i j (fun h => by subst h; exact ⟨hd₁ _, hd₂ _⟩) hij

/-- `L_η ≤ scaledNoiseLimit lam η B` for `B` with nonnegative diagonal. -/
theorem Leta_le_scaledNoiseLimit (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2)
    {B : Fin d → Fin d → ℝ} (hd : ∀ i, 0 ≤ B i i) :
    ∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) ≤ scaledNoiseLimit
        lam η B := by
  rw [← scaledNoiseLimit_zero hlam hη hηl]
  exact scaledNoiseLimit_mono hlam hη hηl (fun _ => le_rfl) hd fun i j => by simp

/-- **Strictness**: for `B` with nonnegative diagonal, `L_η < scaledNoiseLimit lam η B` iff `B ≠
0`. -/
theorem Leta_lt_scaledNoiseLimit_iff (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2)
    {B : Fin d → Fin d → ℝ} (hd : ∀ i, 0 ≤ B i i) :
    ∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) < scaledNoiseLimit
        lam η B ↔ ∃ i j, B i j ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    have hB : B = fun _ _ => 0 :=
      funext fun i => funext fun j => of_not_not fun hij => hne ⟨i, j, hij⟩
    rw [hB, scaledNoiseLimit_zero hlam hη hηl] at h
    exact lt_irrefl _ h
  · rintro ⟨i, j, hij⟩
    rw [← scaledNoiseLimit_zero hlam hη hηl]
    exact scaledNoiseLimit_lt hlam hη hηl (fun _ => le_rfl) hd (fun i j => by simp)
      ⟨i, j, by simpa using abs_pos.2 hij⟩

/-- A PSD matrix conjugated into the frame has nonnegative diagonal. -/
theorem frame_diag_nonneg (Q : Matrix (Fin d) (Fin d) ℝ) {C : Matrix (Fin d) (Fin d) ℝ}
    (hC : C.PosSemidef) (i : Fin d) : 0 ≤ (Qᵀ * C * Q) i i := by
  have hCU : (Qᵀ * C * Q).PosSemidef := by
    have := hC.conjTranspose_mul_mul_same Q
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact hCU.diag_nonneg

/-- `QᵀCQ = 0` forces `C = 0` for orthogonal `Q`. -/
theorem conj_eq_zero_iff (hQ : Qᵀ * Q = 1) (C : Matrix (Fin d) (Fin d) ℝ) :
    Qᵀ * C * Q = 0 ↔ C = 0 := by
  constructor
  · intro h
    have := Laplace.Sampler.conj_transpose_mul_mul_self hQ C
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this.symm
  · rintro rfl
    simp

/-- A nonzero matrix has a nonzero frame entry. -/
theorem exists_conj_ne_zero (hQ : Qᵀ * Q = 1) {C : Matrix (Fin d) (Fin d) ℝ} (hne : C ≠ 0) :
    ∃ i j, (Qᵀ * C * Q) i j ≠ 0 := by
  by_contra h
  exact hne ((conj_eq_zero_iff hQ C).1 (Matrix.ext fun i j => of_not_not fun hij => h ⟨i, j, hij⟩))

/-- **`L_η < L_lin` for PSD `C₀ ≠ 0`**: linear batch growth with any nonzero gradient noise
strictly inflates the
long-run variance. -/
theorem Leta_lt_Llin (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (hη : 0 < η) (hηl : ∀ i, η * lam i <
    2)
    {C₀ : Matrix (Fin d) (Fin d) ℝ} (hC₀ : C₀.PosSemidef) (hne : C₀ ≠ 0) :
    ∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) < scaledNoiseLimit
        lam η (fun i j => (Qᵀ * C₀ * Q) i j) :=
  (Leta_lt_scaledNoiseLimit_iff hlam hη hηl (frame_diag_nonneg Q hC₀)).2 (exists_conj_ne_zero hQ
      hne)

/-- In the batch form, a larger batch-to-temperature ratio gives a smaller limit. -/
theorem scaledNoiseLimit_batch_anti (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2)
    (Q : Matrix (Fin d) (Fin d) ℝ) {Cg : Matrix (Fin d) (Fin d) ℝ} (hCg : Cg.PosSemidef) {ν₁ ν₂ : ℝ}
    (hν₁ : 0 < ν₁) (hν : ν₁ ≤ ν₂) :
    scaledNoiseLimit lam η (fun i j => (Qᵀ * Cg * Q) i j / ν₂) ≤
      scaledNoiseLimit lam η (fun i j => (Qᵀ * Cg * Q) i j / ν₁) := by
  have hν₂ : 0 < ν₂ := lt_of_lt_of_le hν₁ hν
  refine scaledNoiseLimit_mono hlam hη hηl (fun i => div_nonneg (frame_diag_nonneg Q hCg i) hν₂.le)
    (fun i => div_nonneg (frame_diag_nonneg Q hCg i) hν₁.le) fun i j => ?_
  rw [abs_div, abs_div, abs_of_pos hν₁, abs_of_pos hν₂]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hν₁ hν

/-- For `C_g ≠ 0` the batch limit strictly decreases in the batch-to-temperature ratio. -/
theorem scaledNoiseLimit_batch_anti_strict (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) {Cg : Matrix (Fin d) (Fin d) ℝ} (hCg : Cg.PosSemidef) (hne : Cg ≠ 0)
    {ν₁ ν₂ : ℝ} (hν₁ : 0 < ν₁) (hν : ν₁ < ν₂) :
    scaledNoiseLimit lam η (fun i j => (Qᵀ * Cg * Q) i j / ν₂) <
      scaledNoiseLimit lam η (fun i j => (Qᵀ * Cg * Q) i j / ν₁) := by
  have hν₂ : 0 < ν₂ := hν₁.trans hν
  obtain ⟨i, j, hij⟩ := exists_conj_ne_zero hQ hne
  refine scaledNoiseLimit_lt hlam hη hηl (fun i => div_nonneg (frame_diag_nonneg Q hCg i) hν₂.le)
    (fun i => div_nonneg (frame_diag_nonneg Q hCg i) hν₁.le) (fun i j => ?_) ⟨i, j, ?_⟩
  · rw [abs_div, abs_div, abs_of_pos hν₁, abs_of_pos hν₂]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hν₁ hν.le
  · rw [abs_div, abs_div, abs_of_pos hν₁, abs_of_pos hν₂]
    exact div_lt_div_of_pos_left (abs_pos.2 hij) hν₁ hν

end Order

end Laplace.Multi
