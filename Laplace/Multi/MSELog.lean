/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BurnInLog

/-!
# Variance and single-draw mean-square error after logarithmic burn-in (E4)

Tide 108 showed that after `k(t) = ⌈κ log t⌉₊` ULA steps the scaled mean of the LLC statistic `q(u)
= ½uᵀHu` converges to the
exact localised energy plus the step-size bias `b_η = (η/4)∑ᵢλᵢ/(1−ηλᵢ/2)`. This file adds the
second moment:
* **bias–variance decomposition** of the tilted Gaussian expectation, `⟨(q − a)²⟩ = (⟨q²⟩ − ⟨q⟩²) +
(⟨q⟩ − a)²` (`tiltedMSE`,
  `tiltedMSE_energy`);
* **the `k`-step variance at the anchored scaling** along any schedule with `k(t) → ∞`,
`t·r^{2k(t)} → 0`, `r ∈ (maxᵢ|1−ηλᵢ|, 1)`:
  `t²Var_{k(t)}(q) → V_η = ½∑ᵢ(1−ηλᵢ/2)⁻²` (`ulaAnchored_var_schedule_tendsto`), in particular
  along `⌈κ log t⌉₊` for
  `κ > 1/(2 log(1/r))` (`ulaAnchored_var_log_tendsto`);
* **the single-draw mean-square error**: `t²⟨(q − ⟨L⟩_loc)²⟩_{⌈κ log t⌉₊} → b_η² + V_η`
(`ulaAnchored_mse_log_tendsto`): after
  logarithmic burn-in one ULA draw estimates the localised energy with scaled root-mean-square
  error `√(b_η² + V_η)`;
* **the limit is increasing in the step** (`mseLimit_mono`): at fixed burn-in the single-draw error
prefers the smallest `η`, the cost
  being the burn-in count `κ_crit(η) = 1/(2 log(1/maxᵢ|1−ηλᵢ|))`, which decreases in `η`.
-/

open Matrix Filter Topology MeasureTheory

namespace Laplace.Multi

/-! ### Bias–variance decomposition of a tilted Gaussian expectation -/

section MSE

variable {ι : Type*} [Fintype ι]

/-- `⟨(q − a)²⟩ = (⟨q²⟩ − ⟨q⟩²) + (⟨q⟩ − a)²` for the tilted Gaussian, given (shifted)
integrability of `q` and `q²`. -/
theorem tiltedMSE [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) (q : (ι → ℝ) → ℝ)
    (a : ℝ)
    (hqq : Integrable (fun u : ι → ℝ =>
      q (u + tiltMean P v) * q (u + tiltMean P v) * gaussianWeight (matCLM P) u))
    (hq : Integrable (fun u : ι → ℝ => q (u + tiltMean P v) * gaussianWeight (matCLM P) u)) :
    tiltedExpectation P v (fun u => (q u - a) ^ 2) =
      (tiltedExpectation P v (fun u => q u ^ 2) - (tiltedExpectation P v q) ^ 2) +
        (tiltedExpectation P v q - a) ^ 2 := by
  have hint : Integrable (fun u : ι → ℝ =>
      q (u + tiltMean P v) * (q (u + tiltMean P v) + (-2 * a)) * gaussianWeight (matCLM P) u) := by
    refine (hqq.add (hq.const_mul (-2 * a))).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.add_apply]
    ring
  have e : (fun u : ι → ℝ => (q u - a) ^ 2) = fun u => q u * (q u + (-2 * a)) + a ^ 2 := by
    funext u
    ring
  rw [e, Laplace.Sampler.tiltedExpectation_add_const hP v (fun u => q u * (q u + (-2 * a))) (a ^ 2)
    hint, Laplace.Sampler.tiltedExpectation_mul_add_const hP v q q (-2 * a) hqq hq]
  have e2 : (fun u : ι → ℝ => q u * q u) = fun u => q u ^ 2 := by
    funext u
    ring
  rw [e2]
  ring

/-- The bias–variance decomposition for the energy `q(u) = ½uᵀHu`. -/
theorem tiltedMSE_energy {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) {H : Matrix ι ι ℝ}
    (hH : H.IsHermitian) (a : ℝ) :
    tiltedExpectation P v (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u) - a) ^ 2) =
      (tiltedExpectation P v (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) ^ 2) -
        (tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u))) ^ 2) +
        (tiltedExpectation P v (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) - a) ^ 2 := by
  classical
  refine tiltedMSE hP v (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) a ?_
    (Laplace.Sampler.integrable_shift_energy hP hH (tiltMean P v))
  have := Laplace.Sampler.integrable_shift_energy_mul_quadProbe hP hH hH 0 (tiltMean P v)
  simpa using this

end MSE

/-! ### The `k`-step variance at the anchored scaling -/

section Variance

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g η : ℝ}

/-- **The `k`-step variance vanishes onto the stationary value** along any schedule with `k(t) → ∞`
and `t·r^{2k(t)} → 0`:
`t²Var_{k(t)}(½uᵀHu) → ½∑ᵢ(1−ηλᵢ/2)⁻²`. -/
theorem ulaAnchored_var_schedule_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d →
    ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hr : ∀ i, |1 - η * lam i| < r) {k : ℝ → ℕ} (hk : Tendsto k atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * (tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam
      * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * k t)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) (k t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g
      • (w₀ - c))) x₀) (fun u => ((1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) ^ 2) -
      (tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin
      d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g • (1 :
      Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * k t)))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) (k t) ((t • (Q * diagonal lam
      * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ
      (Q * diagonal lam * Qᵀ) *ᵥ u))) ^ 2)) atTop (𝓝 (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2))
      := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ (∀ i, η / t * (t * lam i + g) < 2) ∧ 1 ≤ k t :=
    (eventually_gt_atTop 0).and ((Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1)).and (hk.eventually_ge_atTop
          1))
  have hk2 : Tendsto (fun t => 2 * k t) atTop atTop := tendsto_atTop_mono (fun t => by omega) hk
  have hV : ∀ i, Tendsto (fun t : ℝ => (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) /
      2))) * (1 - (1 - η / t * (t * lam i + g)) ^ (2 * k t)))) atTop (𝓝 (1 / (lam i * (1 - η * lam i
      / 2)) * (1 - 0))) := fun i =>
    (tsigma_scaled_tendsto (g := g) (hlam i) (hηl i)).mul (tendsto_const_nhds.sub
      (rho_pow_schedule_tendsto_zero hr0 hr1 (abs_rho_scaled_eventually_le (lam i) g η (hr i)) hk2))
  have h1 : Tendsto (fun t : ℝ => 1 / 2 * ∑ i, (lam i * (t * (1 / ((t * lam i + g) * (1 - η / t * (t
      * lam i + g) / 2))) * (1 - (1 - η / t * (t * lam i + g)) ^ (2 * k t)))) ^ 2) atTop (𝓝 (1 / 2 *
      ∑ i, (lam i * (1 / (lam i * (1 - η * lam i / 2)) * (1 - 0))) ^ 2)) :=
    (tendsto_finsetSum Finset.univ fun i _ => ((tendsto_const_nhds (x := lam i)).mul (hV i)).pow
        2).const_mul
      (1 / 2)
  have h2 : Tendsto (fun t : ℝ => ∑ i, ((t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) /
      2))) * (1 - (1 - η / t * (t * lam i + g)) ^ (2 * k t))) * lam i ^ 2 * ((t * (g * affineFrame Q
      c w₀ i / (t * lam i + g))) * (g * affineFrame Q c w₀ i / (t * lam i + g)) + 2 * (t * (g *
      affineFrame Q c w₀ i / (t * lam i + g))) * (1 - η / t * (t * lam i + g)) ^ k t * ((Qᵀ *ᵥ x₀) i
      - (g * affineFrame Q c w₀ i / (t * lam i + g))) + (t * (1 - η / t * (t * lam i + g)) ^ (2 * k
      t)) * ((Qᵀ *ᵥ x₀) i - (g * affineFrame Q c w₀ i / (t * lam i + g))) ^ 2))) atTop (𝓝 (∑ i : Fin
      d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => by
      have hρ := abs_rho_scaled_eventually_le (lam i) g η (hr i)
      have hd : Tendsto (fun t : ℝ => (Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t * lam i + g))
          atTop
          (𝓝 ((Qᵀ *ᵥ x₀) i - 0)) :=
        tendsto_const_nhds.sub (anchoredMean_tendsto_zero (hlam i) g (affineFrame Q c w₀ i))
      have hA := (mul_anchoredMean_tendsto (hlam i) hg (affineFrame Q c w₀ i)).mul
        (anchoredMean_tendsto_zero (hlam i) g (affineFrame Q c w₀ i))
      have hB := (((tendsto_const_nhds (x := (2 : ℝ))).mul
        (mul_anchoredMean_tendsto (hlam i) hg (affineFrame Q c w₀ i))).mul
        (rho_pow_schedule_tendsto_zero hr0 hr1 hρ hk)).mul hd
      have hC := (mul_rho_pow_schedule_tendsto_zero hρ htr).mul (hd.pow 2)
      have := ((hV i).mul (tendsto_const_nhds (x := lam i ^ 2))).mul ((hA.add hB).add hC)
      simpa using this
  have hlim : ∀ i, (lam i * (1 / (lam i * (1 - η * lam i / 2)) * (1 - 0))) ^ 2 =
      (1 / (1 - η * lam i / 2)) ^ 2 := fun i => by
    have h1 := (hlam i).ne'
    have h2 : 1 - η * lam i / 2 ≠ 0 := by linarith [hηl i]
    simp only [sub_zero, mul_one]
    field_simp
  have hF := h1.add h2
  simp only [Finset.sum_const_zero, add_zero, hlim] at hF
  refine hF.congr' ?_
  filter_upwards [hev] with t ⟨ht, hevt, hkt⟩
  rw [ulaAnchored_llc_var hlam hQ c w₀ hg ht (div_pos hη ht) hevt hkt x₀]
  simp only [Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => by
      simp only [pow_mul']
      ring

/-- **Logarithmic burn-in suffices for the variance**: along `k(t) = ⌈κ log t⌉₊` with `κ > 1/(2
log(1/r))`,
`t²Var_{k(t)}(½uᵀHu) → ½∑ᵢ(1−ηλᵢ/2)⁻²`. -/
theorem ulaAnchored_var_log_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {r κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : ∀ i, |1 - η * lam i| < r) (hκ : 1 + 2 * κ * Real.log r < 0) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * (tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam
      * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * ⌈κ * Real.log t⌉₊)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) (⌈κ * Real.log t⌉₊) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin
      d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => ((1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) ^ 2)
      - (tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix
      (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * ⌈κ * Real.log t⌉₊)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) (⌈κ * Real.log t⌉₊) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin
      d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u))) ^
      2)) atTop (𝓝 (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2)) := by
  have hκpos : 0 < κ := by nlinarith [Real.log_neg hr0 hr1]
  exact ulaAnchored_var_schedule_tendsto hlam hQ c w₀ hg hη hηl hr0.le hr1 hr
    (log_schedule_natCeil_tendsto hκpos) (log_schedule_tendsto hr0 hr1 hκ) x₀

/-- The limiting scaled single-draw mean-square error `b_η² + V_η` is increasing in the step `η` on
`(0, 2/λ_max)`. -/
theorem mseLimit_mono (hlam : ∀ i, 0 < lam i) {η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂)
    (hηl : ∀ i, η₂ * lam i < 2) :
    (η₁ / 4 * ∑ i, lam i / (1 - η₁ * lam i / 2)) ^ 2 + 1 / 2 * ∑ i, (1 / (1 - η₁ * lam i / 2)) ^ 2 ≤
      (η₂ / 4 * ∑ i, lam i / (1 - η₂ * lam i / 2)) ^ 2 +
        1 / 2 * ∑ i, (1 / (1 - η₂ * lam i / 2)) ^ 2 := by
  have hden : ∀ i, 0 < 1 - η₂ * lam i / 2 := fun i => by linarith [hηl i]
  have hden₁ : ∀ i, 1 - η₂ * lam i / 2 ≤ 1 - η₁ * lam i / 2 := fun i => by
    have := mul_le_mul_of_nonneg_right hη (hlam i).le
    linarith
  have hden₁' : ∀ i, 0 < 1 - η₁ * lam i / 2 := fun i => lt_of_lt_of_le (hden i) (hden₁ i)
  have hsum1 : ∑ i, lam i / (1 - η₁ * lam i / 2) ≤ ∑ i, lam i / (1 - η₂ * lam i / 2) :=
    Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (hlam i).le (hden i) (hden₁ i)
  have hsum1pos : 0 ≤ ∑ i, lam i / (1 - η₁ * lam i / 2) :=
    Finset.sum_nonneg fun i _ => div_nonneg (hlam i).le (hden₁' i).le
  have hb : η₁ / 4 * ∑ i, lam i / (1 - η₁ * lam i / 2) ≤ η₂ / 4 * ∑ i, lam i / (1 - η₂ * lam i / 2)
      :=
    mul_le_mul (by linarith) hsum1 hsum1pos (by linarith)
  have hb0 : 0 ≤ η₁ / 4 * ∑ i, lam i / (1 - η₁ * lam i / 2) := mul_nonneg (by linarith) hsum1pos
  have h2 : ∀ i, (1 / (1 - η₁ * lam i / 2)) ^ 2 ≤ (1 / (1 - η₂ * lam i / 2)) ^ 2 := fun i =>
    pow_le_pow_left₀ (one_div_pos.2 (hden₁' i)).le (one_div_le_one_div_of_le (hden i) (hden₁ i)) 2
  exact add_le_add (pow_le_pow_left₀ hb0 hb 2)
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h2 i) (by norm_num))

end Variance

/-! ### The single-draw mean-square error after logarithmic burn-in -/

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g η : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The single-draw mean-square error after logarithmic burn-in**: along `k(t) = ⌈κ log t⌉₊`, `κ
> 1/(2 log(1/r))`,
`t²⟨(½uᵀHu − ⟨L⟩_loc)²⟩_{k(t)} → b_η² + V_η`, `b_η = (η/4)∑ᵢλᵢ/(1−ηλᵢ/2)`, `V_η = ½∑ᵢ(1−ηλᵢ/2)⁻²`.
-/
theorem ulaAnchored_mse_log_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) {r κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r)
    (hκ : 1 + 2 * κ * Real.log r < 0) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam *
      Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * ⌈κ * Real.log t⌉₊)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) (⌈κ * Real.log t⌉₊) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin
      d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => ((1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u) -
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic
      Q c lam alpha gamma)) ^ 2)) atTop (𝓝 ((η / 4 * ∑ i, lam i / (1 - η * lam i / 2)) ^ 2 + 1 / 2 *
      ∑ i, (1 / (1 - η * lam i / 2)) ^ 2)) := by
  have hκpos : 0 < κ := by nlinarith [Real.log_neg hr0 hr1]
  have hk : Tendsto (fun t : ℝ => ⌈κ * Real.log t⌉₊) atTop atTop := log_schedule_natCeil_tendsto
      hκpos
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ (∀ i, η / t * (t * lam i + g) < 2) ∧ 1 ≤ ⌈κ * Real.log t⌉₊
      :=
    (eventually_gt_atTop 0).and ((Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1)).and (hk.eventually_ge_atTop
          1))
  have hbias := ulaAnchored_sampled_log_tendsto (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc)
      hQ c w₀
    hg hη hηl hr0 hr1 hr hκ x₀
  have hvar := ulaAnchored_var_log_tendsto hlam hQ c w₀ hg hη hηl hr0 hr1 hr hκ x₀
  have h := (hbias.pow 2).add hvar
  refine h.congr' ?_
  filter_upwards [hev] with t ⟨ht, hevt, hkt⟩
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have hdiagP := transpose_localisedPrecision_conj (lam := lam) hQ t g
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  have hP := Laplace.Sampler.burnInCov_inv_posDef_frame hQ hdiagP hp (div_pos hη ht) hevt hkt
  have hH : (Q * diagonal lam * Qᵀ).IsHermitian := Laplace.Sampler.isHermitian_of_frame hQ hdiagH
  rw [tiltedMSE_energy hP _ hH _]
  ring

/-- `t⟨L⟩_loc → d/2`: the scaled localised energy tends to half the dimension (the anchored
Gaussian value; the anchor and
anharmonic corrections are `O(1/t)`). -/
theorem ulaAnchored_localisedEnergy_scaled_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤
    g) :
    Tendsto (fun t : ℝ => t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀
      t) t (rotatedAnharmonic Q c lam alpha gamma)) atTop (𝓝 ((d : ℝ) / 2)) := by
  obtain ⟨K, T, hK, hT, hb⟩ :=
    localisedEnergy_anchoredGap (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀ hg
  have hX : Tendsto (fun t : ℝ => t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma) - (1 / 2 * ∑ i, t * lam i / (t * lam i
      + g) + t / 2 * ∑ i, lam i * ((g * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2) - (∑ i,
      (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g *
      affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t) atTop (𝓝 0) := by
    refine tendsto_zero_of_abs_le ?_
      ((tendsto_const_nhds (x := K)).div_atTop (tendsto_pow_atTop two_ne_zero))
    filter_upwards [eventually_ge_atTop T] with t hTt
    exact hb hTt
  have hG : Tendsto (fun t : ℝ => (1 / 2 * ∑ i, t * lam i / (t * lam i + g) + t / 2 * ∑ i, lam i *
      ((g * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2)) atTop (𝓝 (1 / 2 * ∑ i : Fin d, (1 : ℝ) +
      1 / 2 * ∑ i : Fin d, lam i * ((g * affineFrame Q c w₀ i / lam i) * 0))) := by
    refine ((tendsto_finsetSum Finset.univ fun i _ =>
      ratio_scaled_tendsto (g := g) (hlam i)).const_mul (1 / 2)).add ?_
    have : Tendsto (fun t : ℝ => 1 / 2 * ∑ i, lam i * ((t * (g * affineFrame Q c w₀ i / (t * lam i +
      g))) * (g * affineFrame Q c w₀ i / (t * lam i + g)))) atTop (𝓝 (1 / 2 * ∑ i : Fin d, lam i *
      ((g * affineFrame Q c w₀ i / lam i) * 0))) :=
      (tendsto_finsetSum Finset.univ fun i _ => (tendsto_const_nhds (x := lam i)).mul
        ((mul_anchoredMean_tendsto (hlam i) hg _).mul (anchoredMean_tendsto_zero (hlam i) g
            _))).const_mul
        (1 / 2)
    refine this.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hE : Tendsto (fun t : ℝ => (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame
      Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t) atTop (𝓝 0)
          :=
    (tendsto_const_nhds (x := (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
        w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))))).div_atTop
            tendsto_id
  have h := (hX.add hG).add hE
  have hlim : (0 : ℝ) + (1 / 2 * ∑ i : Fin d, (1 : ℝ) + 1 / 2 * ∑ i : Fin d, lam i * ((g *
      affineFrame Q c w₀ i / lam i) * 0)) + 0 = (d : ℝ) / 2 := by
    simp only [mul_zero, Finset.sum_const_zero, add_zero, zero_add, Finset.sum_const,
        Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  rw [hlim] at h
  exact h.congr' (Filter.Eventually.of_forall fun t => by ring)

/-- **Centre transfer**: any deterministic centre `cen(t)` with `t·cen(t) − t⟨L⟩_loc → 0` has the
same limiting scaled
single-draw mean-square error `b_η² + V_η`. -/
theorem ulaAnchored_mse_center_log_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {r κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : ∀ i, |1 - η * lam i| < r) (hκ : 1 + 2 * κ * Real.log r < 0) (x₀ : Fin d → ℝ) (cen : ℝ → ℝ)
    (hcen : Tendsto (fun t : ℝ => t * cen t - t * gibbsExpectation (localisedRotatedAnharmonic Q c
      lam alpha gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma)) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => t ^ 2 * tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam *
      Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * ⌈κ * Real.log t⌉₊)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) (⌈κ * Real.log t⌉₊) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin
      d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => ((1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u) - cen
      t) ^ 2)) atTop (𝓝 ((η / 4 * ∑ i, lam i / (1 - η * lam i / 2)) ^ 2 + 1 / 2 * ∑ i, (1 / (1 - η *
      lam i / 2)) ^ 2)) := by
  have hκpos : 0 < κ := by nlinarith [Real.log_neg hr0 hr1]
  have hk : Tendsto (fun t : ℝ => ⌈κ * Real.log t⌉₊) atTop atTop := log_schedule_natCeil_tendsto
      hκpos
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ (∀ i, η / t * (t * lam i + g) < 2) ∧ 1 ≤ ⌈κ * Real.log t⌉₊
      :=
    (eventually_gt_atTop 0).and ((Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1)).and (hk.eventually_ge_atTop
          1))
  have hbias := (ulaAnchored_sampled_log_tendsto (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc)
      hQ c
    w₀ hg hη hηl hr0 hr1 hr hκ x₀).sub hcen
  rw [sub_zero] at hbias
  have hvar := ulaAnchored_var_log_tendsto hlam hQ c w₀ hg hη hηl hr0 hr1 hr hκ x₀
  have h := (hbias.pow 2).add hvar
  refine h.congr' ?_
  filter_upwards [hev] with t ⟨ht, hevt, hkt⟩
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have hdiagP := transpose_localisedPrecision_conj (lam := lam) hQ t g
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  have hP := Laplace.Sampler.burnInCov_inv_posDef_frame hQ hdiagP hp (div_pos hη ht) hevt hkt
  have hH : (Q * diagonal lam * Qᵀ).IsHermitian := Laplace.Sampler.isHermitian_of_frame hQ hdiagH
  rw [tiltedMSE_energy hP _ hH _]
  ring

/-- **The scaled LLC statistic against `d/2`**: `⟨(t·½uᵀHu − d/2)²⟩_{⌈κ log t⌉₊} → b_η² + V_η`. -/
theorem ulaAnchored_mse_half_log_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {r κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : ∀ i, |1 - η * lam i| < r) (hκ : 1 + 2 * κ * Real.log r < 0) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ) + g
      • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q * diagonal
      lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * ⌈κ * Real.log t⌉₊)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) (⌈κ * Real.log t⌉₊) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin
      d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (t * ((1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u))
      - (d : ℝ) / 2) ^ 2)) atTop (𝓝 ((η / 4 * ∑ i, lam i / (1 - η * lam i / 2)) ^ 2 + 1 / 2 * ∑ i,
      (1 / (1 - η * lam i / 2)) ^ 2)) := by
  have hL := ulaAnchored_localisedEnergy_scaled_tendsto (hlam := hlam) (hgamma := hgamma)
    (hdisc := hdisc) hQ c w₀ hg
  have hcen : Tendsto (fun t : ℝ => t * ((d : ℝ) / 2 / t) - t * gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha
      gamma)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (d : ℝ) / 2)).sub hL
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    congr 1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ ht]
  have h := ulaAnchored_mse_center_log_tendsto (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc)
      hQ c w₀
    hg hη hηl hr0 hr1 hr hκ x₀ (fun t => (d : ℝ) / 2 / t) hcen
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  rw [← tiltedExpectation_const_mul]
  congr 1
  funext u
  field_simp

end Multi

end Laplace.Multi
