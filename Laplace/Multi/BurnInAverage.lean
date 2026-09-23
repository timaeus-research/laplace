/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MSELog

/-!
# The post-burn-in average: non-stationary autocovariance and the `n`-draw estimator (E4)

Tides 108 and 110 treated a single ULA draw after `k(t) = ⌈κ log t⌉₊` steps. This file treats the
average of `n` consecutive
post-burn-in draws:
* **the non-stationary autocovariance** from a fixed start (`burnAutoCov`, `burnAutoCov_eq`): the
covariance under the `s`-step law
  between the energy `q(u) = ½uᵀHu` and its `ℓ`-step conditional mean (tide 102's kernel-level
  device) is
  `½∑ᵢλᵢ²v_{s,i}²ρᵢ^{2ℓ} + ∑ᵢλᵢ²v_{s,i}ρᵢ^ℓμ_{s,i}μ_{s+ℓ,i}` with `v_{s,i} = σᵢ²(1−ρᵢ^{2s})`,
  `μ_{s,i} = m̂ᵢ + ρᵢ^s(x̂₀ᵢ − m̂ᵢ)`;
* **its scaled limit along a burn-in schedule** (`ulaAnchored_autoCov_schedule_tendsto`): at `h =
η/t` with `k(t) → ∞`, `t·r^{2k(t)} → 0`,
  `t²·Cov_{k(t)}(q, q∘K^ℓ) → c_ℓ^∞ = ½∑ᵢ(1−ηλᵢ/2)⁻²(1−ηλᵢ)^{2ℓ}`, the stationary scaled
  autocovariance of tide 103;
* **the mean along a schedule** (`ulaAnchored_sampled_schedule_tendsto`): tide 108's limit for a
general schedule;
* **the `n`-draw average** (`avgVar`, `lagWeight`, `ulaAnchored_avgVar_schedule_tendsto`,
`ulaAnchored_avg_mse_log_tendsto`): the kernel-level
  variance of `(1/n)∑_{a<n}q(X_{k+a})` satisfies `t²·avgVar → (1/n²)(n c₀^∞ +
  2∑_{j<n}(n−(j+1))c^∞_{j+1}) = ½∑ᵢ(1−ηλᵢ/2)⁻²F_n((1−ηλᵢ)²)`
  (`avgLimit_eq_lagWeight`), `F_n(z) = (n + 2∑_{j<n}(n−(j+1))z^{j+1})/n²`, the scaled bias of the
  average tends to `b_η`, and the scaled
  mean-square error of the average tends to `b_η² + ½∑ᵢ(1−ηλᵢ/2)⁻²F_n((1−ηλᵢ)²)`; `1/n ≤ F_n(z) ≤
  1` (`inv_le_lagWeight`, `lagWeight_le_one`):
  `n` correlated draws are worth between one and `n` independent ones, and averaging does not
  reduce the step-size bias.
The identification of `Cov_s(q, condEnergy_ℓ)` with `Cov(q(X_s), q(X_{s+ℓ}))` and of `avgVar` with
the variance of the average is the
Markov/tower bridge, as in tide 102.
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Covariance under the `s`-step law from `x₀` between the energy and its `ℓ`-step conditional
mean. -/
noncomputable def burnAutoCov (P H : Matrix ι ι ℝ) (h : ℝ) (m : ι → ℝ) (s ℓ : ℕ) (x₀ : ι → ℝ) : ℝ :=
  tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * s)))⁻¹ (burnInTiltAnch P h s m x₀)
      (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * condEnergy P H h m ℓ u) -
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * s)))⁻¹ (burnInTiltAnch P h s m x₀)
        (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) *
      tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * s)))⁻¹ (burnInTiltAnch P h s m x₀)
        (condEnergy P H h m ℓ)

/-- The kernel-level variance of the average of `n` consecutive draws `q(X_{s+a})`, `a < n`:
`(1/n²)(∑ₐVar_{s+a} + 2∑_{j<n}∑_{a<n−(j+1)}Cov_{s+a}(q, q∘K^{j+1}))`. -/
noncomputable def avgVar (P H : Matrix ι ι ℝ) (h : ℝ) (m : ι → ℝ) (s n : ℕ) (x₀ : ι → ℝ) : ℝ :=
  1 / (n : ℝ) ^ 2 * (∑ a ∈ Finset.range n, burnAutoCov P H h m (s + a) 0 x₀ +
    2 * ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), burnAutoCov P H h m (s + a) (j + 1)
        x₀)

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-- Lag 0 is the `k`-step variance of tide 105. -/
theorem burnAutoCov_zero_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 < lam i) {s : ℕ} (hs : 1 ≤ s) (m x₀ : ι → ℝ) :
    burnAutoCov P H h m s 0 x₀ = 1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h
      * p i) ^ (2 * s)))) ^ 2 + ∑ i, lam i ^ 2 * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i)
      ^ (2 * s))) * ((Uᵀ *ᵥ m) i + (1 - h * p i) ^ s * (Uᵀ *ᵥ (x₀ - m)) i) * ((Uᵀ *ᵥ m) i + (1 - h *
      p i) ^ s * (Uᵀ *ᵥ (x₀ - m)) i) := by
  have hc0 : condEnergy P H h m 0 = fun x₀ => 1 / 2 * (x₀ ⬝ᵥ H *ᵥ x₀) := funext fun x₀ => by
    unfold condEnergy
    exact if_pos rfl
  have e1 : (fun u : ι → ℝ => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * (1 / 2 * (u ⬝ᵥ H *ᵥ u))) =
      fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) ^ 2 := by
    funext u
    ring
  have hv := burnInAnch_var_frame hU hdiag hp hh hev hdiagH hlam hs m x₀
  unfold burnAutoCov
  simp only [hc0]
  rw [e1, ← sq, hv]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Lag `ℓ ≥ 1`: the Wick computation under the `s`-step law. -/
theorem burnAutoCov_eq_of_pos (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p
    i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    {s : ℕ} (hs : 1 ≤ s) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (m x₀ : ι → ℝ) :
    burnAutoCov P H h m s ℓ x₀ = 1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h
      * p i) ^ (2 * s)))) ^ 2 * (1 - h * p i) ^ (2 * ℓ) + ∑ i, lam i ^ 2 * (1 / (p i * (1 - h * p i
      / 2)) * (1 - (1 - h * p i) ^ (2 * s))) * (1 - h * p i) ^ ℓ * ((Uᵀ *ᵥ m) i + (1 - h * p i) ^ s
      * (Uᵀ *ᵥ (x₀ - m)) i) * ((Uᵀ *ᵥ m) i + (1 - h * p i) ^ (s + ℓ) * (Uᵀ *ᵥ (x₀ - m)) i) := by
  have hQ := burnInCov_inv_posDef_frame hU hdiag hp hh hev hs
  have hinv := burnInCov_inv_inv_frame hU hdiag hp hh hev hs
  have hH := isHermitian_of_frame hU hdiagH
  have hcond : condEnergy P H h m ℓ = fun x₀ => 1 / 2 * (x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 -
      h * p i) ^ (2 * ℓ)) * Uᵀ) *ᵥ x₀) + x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 - h * p i) ^ ℓ *
      (1 - (1 - h * p i) ^ ℓ)) * Uᵀ) *ᵥ m + (1 / 2 * ∑ i, lam i * (1 / (p i * (1 - h * p i / 2)) *
      (1 - (1 - h * p i) ^ (2 * ℓ))) + 1 / 2 * ∑ i, lam i * ((1 - (1 - h * p i) ^ ℓ) * (Uᵀ *ᵥ m) i)
      ^ 2) :=
    funext fun x₀ => condEnergy_eq hU hdiag hp hh hev hdiagH hℓ m x₀
  unfold burnAutoCov
  simp only [hcond]
  unfold burnInTiltAnch
  rw [tiltedCov_energy_quadProbe_add_const hQ ((ulaCov P h * (1 - ulaStep P h ^ (2 * s)))⁻¹ *ᵥ
      burnInMeanAnch P h s m x₀) hH (isHermitian_conj_diagonal U _) _ _,
    tiltedCov_quadForm_quadProbe hQ ((ulaCov P h * (1 - ulaStep P h ^ (2 * s)))⁻¹ *ᵥ burnInMeanAnch
        P h s m x₀) hH (isHermitian_conj_diagonal U _) _,
    tiltMean_mulVec_self hQ, hinv, frame_eq_conj hU hdiagH]
  simp only [conj_mul_conj_frame hU, Matrix.diagonal_mul_diagonal, sum_sum_conj_mul_conj hU,
    conj_mulVec_dotProduct_conj_mulVec hU, transpose_mulVec_burnInMeanAnch hU hdiag, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The non-stationary energy autocovariance from a fixed start**, all lags:
`Cov_s(q, q∘K^ℓ) = ½∑ᵢλᵢ²v_{s,i}²ρᵢ^{2ℓ} + ∑ᵢλᵢ²v_{s,i}ρᵢ^ℓμ_{s,i}μ_{s+ℓ,i}`. -/
theorem burnAutoCov_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 < lam i) {s : ℕ} (hs : 1 ≤ s) (ℓ : ℕ) (m x₀ : ι → ℝ) :
    burnAutoCov P H h m s ℓ x₀ = 1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h
      * p i) ^ (2 * s)))) ^ 2 * (1 - h * p i) ^ (2 * ℓ) + ∑ i, lam i ^ 2 * (1 / (p i * (1 - h * p i
      / 2)) * (1 - (1 - h * p i) ^ (2 * s))) * (1 - h * p i) ^ ℓ * ((Uᵀ *ᵥ m) i + (1 - h * p i) ^ s
      * (Uᵀ *ᵥ (x₀ - m)) i) * ((Uᵀ *ᵥ m) i + (1 - h * p i) ^ (s + ℓ) * (Uᵀ *ᵥ (x₀ - m)) i) := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · subst hℓ
    rw [burnAutoCov_zero_eq hU hdiag hp hh hev hdiagH hlam hs m x₀]
    simp only [mul_zero, pow_zero, mul_one, add_zero]
  · exact burnAutoCov_eq_of_pos hU hdiag hp hh hev hdiagH hs hℓ m x₀

end Frame

end Laplace.Sampler

namespace Laplace.Multi

/-! ### The anchored model -/

section Anchored

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g η : ℝ}

/-- `burnAutoCov` on the anchored model, in explicit frame coordinates. -/
theorem ulaAnchored_burnAutoCov (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * (t * lam i + g) < 2)
    {s : ℕ} (hs : 1 ≤ s) (ℓ : ℕ) (x₀ : Fin d → ℝ) :
    Laplace.Sampler.burnAutoCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))
      (Q * diagonal lam * Qᵀ) h ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ))⁻¹ *ᵥ (g • (w₀ - c))) s ℓ x₀ = 1 / 2 * ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - h * (t *
      lam i + g) / 2)) * (1 - (1 - h * (t * lam i + g)) ^ (2 * s)))) ^ 2 * (1 - h * (t * lam i + g))
      ^ (2 * ℓ) + ∑ i, lam i ^ 2 * (1 / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) * (1 - (1
      - h * (t * lam i + g)) ^ (2 * s))) * (1 - h * (t * lam i + g)) ^ ℓ * ((g * affineFrame Q c w₀
      i / (t * lam i + g)) + (1 - h * (t * lam i + g)) ^ s * ((Qᵀ *ᵥ x₀) i - (g * affineFrame Q c w₀
      i / (t * lam i + g)))) * ((g * affineFrame Q c w₀ i / (t * lam i + g)) + (1 - h * (t * lam i +
      g)) ^ (s + ℓ) * ((Qᵀ *ᵥ x₀) i - (g * affineFrame Q c w₀ i / (t * lam i + g)))) := by
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have hdiagP := transpose_localisedPrecision_conj (lam := lam) hQ t g
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  have hV := Laplace.Sampler.burnAutoCov_eq hQ hdiagP hp hh hev hdiagH hlam hs ℓ ((t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀
  have hm : ∀ i, (Qᵀ *ᵥ ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g
      • (w₀ - c)))) i = g * affineFrame Q c w₀ i / (t * lam i + g) := by
    intro i
    rw [Laplace.Sampler.inv_localisedPrecision_eq_conj_frame hQ hdiagH hlam ht hg, ←
        Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Qᵀ Q, hQ, Matrix.one_mulVec,
          Matrix.mulVec_diagonal,
      Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    unfold affineFrame
    ring
  have hx : ∀ i, (Qᵀ *ᵥ (x₀ - ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹
      *ᵥ (g • (w₀ - c))))) i = (Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t * lam i + g) := by
    intro i
    rw [Matrix.mulVec_sub, Pi.sub_apply, hm i]
  simp only [hm, hx] at hV
  exact hV

/-- **The scaled autocovariance along a burn-in schedule** converges to the stationary value
`c_ℓ^∞ = ½∑ᵢ(1−ηλᵢ/2)⁻²(1−ηλᵢ)^{2ℓ}` for each fixed lag `ℓ`. -/
theorem ulaAnchored_autoCov_schedule_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1)
    (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r) {k : ℝ → ℕ} (hk : Tendsto k atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) (ℓ : ℕ) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.burnAutoCov (t • (Q * diagonal lam * Qᵀ) + g • (1
      : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ) + g
      • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k t) ℓ x₀) atTop (𝓝 (1 / 2 * ∑ i, (1 /
      (1 - η * lam i / 2)) ^ 2 * (1 - η * lam i) ^ (2 * ℓ))) := by
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
  have hρ : ∀ i, Tendsto (fun t : ℝ => 1 - η / t * (t * lam i + g)) atTop (𝓝 (1 - η * lam i)) :=
    fun i => rho_scaled_tendsto (lam i) g η
  have h1 : Tendsto (fun t : ℝ => 1 / 2 * ∑ i, (lam i * (t * (1 / ((t * lam i + g) * (1 - η / t * (t
      * lam i + g) / 2))) * (1 - (1 - η / t * (t * lam i + g)) ^ (2 * k t)))) ^ 2 * (1 - η / t * (t
      * lam i + g)) ^ (2 * ℓ)) atTop (𝓝 (1 / 2 * ∑ i, (lam i * (1 / (lam i * (1 - η * lam i / 2)) *
      (1 - 0))) ^ 2 * (1 - η * lam i) ^ (2 * ℓ))) :=
    (tendsto_finsetSum Finset.univ fun i _ => (((tendsto_const_nhds (x := lam i)).mul (hV i)).pow
        2).mul
      ((hρ i).pow (2 * ℓ))).const_mul (1 / 2)
  have h2 : Tendsto (fun t : ℝ => ∑ i, ((t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) /
      2))) * (1 - (1 - η / t * (t * lam i + g)) ^ (2 * k t))) * lam i ^ 2 * (1 - η / t * (t * lam i
      + g)) ^ ℓ * ((t * (g * affineFrame Q c w₀ i / (t * lam i + g))) * (g * affineFrame Q c w₀ i /
      (t * lam i + g)) + (t * (g * affineFrame Q c w₀ i / (t * lam i + g))) * ((1 - η / t * (t * lam
      i + g)) ^ k t * (1 - η / t * (t * lam i + g)) ^ ℓ) * ((Qᵀ *ᵥ x₀) i - (g * affineFrame Q c w₀ i
      / (t * lam i + g))) + (t * (g * affineFrame Q c w₀ i / (t * lam i + g))) * (1 - η / t * (t *
      lam i + g)) ^ k t * ((Qᵀ *ᵥ x₀) i - (g * affineFrame Q c w₀ i / (t * lam i + g))) + (t * (1 -
      η / t * (t * lam i + g)) ^ (2 * k t)) * (1 - η / t * (t * lam i + g)) ^ ℓ * ((Qᵀ *ᵥ x₀) i - (g
      * affineFrame Q c w₀ i / (t * lam i + g))) ^ 2))) atTop (𝓝 (∑ i : Fin d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => by
      have hρk := rho_pow_schedule_tendsto_zero hr0 hr1 (abs_rho_scaled_eventually_le (lam i) g η
          (hr i)) hk
      have hd : Tendsto (fun t : ℝ => (Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t * lam i + g))
          atTop
          (𝓝 ((Qᵀ *ᵥ x₀) i - 0)) :=
        tendsto_const_nhds.sub (anchoredMean_tendsto_zero (hlam i) g (affineFrame Q c w₀ i))
      have hM := mul_anchoredMean_tendsto (hlam i) hg (affineFrame Q c w₀ i)
      have hA := hM.mul (anchoredMean_tendsto_zero (hlam i) g (affineFrame Q c w₀ i))
      have hB := (hM.mul (hρk.mul ((hρ i).pow ℓ))).mul hd
      have hC := (hM.mul hρk).mul hd
      have hD := ((mul_rho_pow_schedule_tendsto_zero (abs_rho_scaled_eventually_le (lam i) g η (hr
          i))
        htr).mul ((hρ i).pow ℓ)).mul (hd.pow 2)
      have := (((hV i).mul (tendsto_const_nhds (x := lam i ^ 2))).mul ((hρ i).pow ℓ)).mul
        (((hA.add hB).add hC).add hD)
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
  rw [ulaAnchored_burnAutoCov hlam hQ c w₀ hg ht (div_pos hη ht) hevt hkt ℓ x₀, mul_add]
  congr 1
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [pow_add, pow_mul']
      ring

end Anchored

/-! ### The lag weight `F_n` -/

/-- `F_n(z) = (n + 2∑_{j<n}(n−(j+1))z^{j+1})/n²`: the variance factor of the average of `n`
consecutive draws of an
AR(1)-correlated sequence with lag-1 correlation `z` (relative to one draw). -/
noncomputable def lagWeight (n : ℕ) (z : ℝ) : ℝ :=
  1 / (n : ℝ) ^ 2 * (n + 2 * ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z ^ (j + 1))

theorem sum_range_sub_succ (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) = (n : ℝ) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have e : ∑ j ∈ Finset.range n, (((n + 1 : ℕ) : ℝ) - (j + 1)) =
        ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) + ∑ j ∈ Finset.range n, (1 : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [e, ih]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring

/-- `F_n(z) ≤ 1` for `0 ≤ z ≤ 1`: `n` correlated draws are worth at least one independent draw. -/
theorem lagWeight_le_one {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    lagWeight n z ≤ 1 := by
  unfold lagWeight
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z ^ (j + 1) ≤
      ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) := Finset.sum_le_sum fun j hj => by
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hj
    exact mul_le_of_le_one_right (by linarith) (pow_le_one₀ hz0 hz1)
  rw [sum_range_sub_succ] at hsum
  rw [one_div_mul_eq_div, div_le_one₀ (by positivity)]
  nlinarith [hsum]

/-- `1/n ≤ F_n(z)` for `z ≥ 0`: `n` positively correlated draws are worth at most `n` independent
ones. -/
theorem inv_le_lagWeight {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz0 : 0 ≤ z) : 1 / (n : ℝ) ≤ lagWeight n z
    := by
  unfold lagWeight
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 ≤ ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z ^ (j + 1) :=
    Finset.sum_nonneg fun j hj => mul_nonneg (by
      have : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hj
      linarith) (pow_nonneg hz0 _)
  rw [one_div_mul_eq_div, le_div_iff₀ (by positivity), div_mul_eq_mul_div, one_mul, pow_two,
    mul_div_assoc, div_self hn'.ne', mul_one]
  linarith

/-- `F_n(0) = 1/n`: independent draws. -/
theorem lagWeight_zero {n : ℕ} (hn : 1 ≤ n) : lagWeight n 0 = 1 / (n : ℝ) := by
  unfold lagWeight
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [zero_pow (Nat.succ_ne_zero _), mul_zero, Finset.sum_const_zero, add_zero]
  field_simp

/-- `F_1(z) = 1`: one draw. -/
theorem lagWeight_one_draw (z : ℝ) : lagWeight 1 z = 1 := by
  simp [lagWeight]

/-- `F_n(1) = 1`: perfectly correlated draws are worth one. -/
theorem lagWeight_at_one {n : ℕ} (hn : 1 ≤ n) : lagWeight n 1 = 1 := by
  unfold lagWeight
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [one_pow, mul_one, sum_range_sub_succ]
  field_simp
  ring

/-- `F_n` is nondecreasing in the correlation parameter. -/
theorem lagWeight_mono {n : ℕ} {z₁ z₂ : ℝ} (hz0 : 0 ≤ z₁) (hz : z₁ ≤ z₂) :
    lagWeight n z₁ ≤ lagWeight n z₂ := by
  unfold lagWeight
  have hsum : ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z₁ ^ (j + 1) ≤
      ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z₂ ^ (j + 1) := Finset.sum_le_sum fun j hj => by
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hj
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz _) (by linarith)
  have hN : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hN]

/-- **The integrated-autocorrelation bound** `F_n(z) ≤ (1+z)/(n(1−z))` for `0 ≤ z < 1`. -/
theorem lagWeight_le_iat {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    lagWeight n z ≤ (1 + z) / (n * (1 - z)) := by
  unfold lagWeight
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1z : 0 < 1 - z := by linarith
  have hgeom : ∑ j ∈ Finset.range n, z ^ j ≤ 1 / (1 - z) := by
    rw [geom_sum_eq hz1.ne n, ← neg_sub (1 : ℝ) (z ^ n), ← neg_sub (1 : ℝ) z, neg_div_neg_eq]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hz0 n]) h1z.le
  have hS : ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z ^ (j + 1) ≤ n * z * (1 / (1 - z)) := by
    calc ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z ^ (j + 1)
        ≤ ∑ j ∈ Finset.range n, (n : ℝ) * (z * z ^ j) := Finset.sum_le_sum fun j hj => by
          have : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hj
          rw [pow_succ']
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = n * z * ∑ j ∈ Finset.range n, z ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ n * z * (1 / (1 - z)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hS' : (∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * z ^ (j + 1)) * (1 - z) ≤ n * z := by
    have := mul_le_mul_of_nonneg_right hS h1z.le
    rwa [mul_assoc, one_div_mul_cancel h1z.ne', mul_one] at this
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by
      positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hS' hn'.le]

/-- The limit of the scaled average variance in lag-weight form. -/
theorem avgLimit_eq_lagWeight {d : ℕ} (lam : Fin d → ℝ) (η : ℝ) (n : ℕ) :
    1 / (n : ℝ) ^ 2 * (n * (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η * lam i) ^ (2 * 0))
      + 2 * ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2
      * (1 - η * lam i) ^ (2 * (j + 1)))) = 1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * lagWeight n
      ((1 - η * lam i) ^ 2) := by
  unfold lagWeight
  simp only [pow_mul, pow_zero, mul_one]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### The `n`-draw average -/

section Average

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g η : ℝ}

/-- **The scaled variance of the `n`-draw average along a burn-in schedule**. -/
theorem ulaAnchored_avgVar_schedule_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1)
    (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r) {k : ℝ → ℕ} (hk : Tendsto k atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) (n : ℕ) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.avgVar (t • (Q * diagonal lam * Qᵀ) + g • (1 :
      Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k t) n x₀) atTop (𝓝 (1 / (n : ℝ) ^ 2 *
      (n * (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η * lam i) ^ (2 * 0)) + 2 * ∑ j ∈
      Finset.range n, ((n : ℝ) - (j + 1)) * (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η *
      lam i) ^ (2 * (j + 1)))))) := by
  have hka : ∀ a : ℕ, Tendsto (fun t => k t + a) atTop atTop := fun a =>
    tendsto_atTop_mono (fun t => Nat.le_add_right _ _) hk
  have htra : ∀ a : ℕ, Tendsto (fun t : ℝ => t * r ^ (2 * (k t + a))) atTop (𝓝 0) := fun a => by
    have := htr.mul_const (r ^ (2 * a))
    rw [zero_mul] at this
    exact this.congr' (Filter.Eventually.of_forall fun t => by ring)
  have hc : ∀ a ℓ : ℕ, Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.burnAutoCov (t • (Q * diagonal
      lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k t + a) ℓ x₀)
      atTop (𝓝 (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η * lam i) ^ (2 * ℓ))) :=
    fun a ℓ => ulaAnchored_autoCov_schedule_tendsto hlam hQ c w₀ hg hη hηl hr0 hr1 hr (hka a) (htra
        a) ℓ x₀
  have h := ((tendsto_finsetSum (Finset.range n) fun a _ => hc a 0).add
    ((tendsto_finsetSum (Finset.range n) fun j _ =>
      tendsto_finsetSum (Finset.range (n - (j + 1))) fun a _ => hc a (j + 1)).const_mul
          2)).const_mul
    (1 / (n : ℝ) ^ 2)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have hcast : ∑ j ∈ Finset.range n, (((n - (j + 1) : ℕ) : ℝ) * (1 / 2 * ∑ i, (1 / (1 - η * lam i /
      2)) ^ 2 * (1 - η * lam i) ^ (2 * (j + 1)))) = ∑ j ∈ Finset.range n, (((n : ℝ) - (j + 1)) * (1
      / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η * lam i) ^ (2 * (j + 1)))) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Nat.cast_sub (Finset.mem_range.1 hj), Nat.cast_succ]
  rw [hcast] at h
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
  unfold Laplace.Sampler.avgVar
  simp only [← Finset.mul_sum]
  ring

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- Tide 108's mean limit for a general burn-in schedule: `t⟨q⟩_{k(t)} − t⟨L⟩_loc → b_η`. -/
theorem ulaAnchored_sampled_schedule_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hr : ∀ i, |1 - η * lam i| < r) {k : ℝ → ℕ} (hk : Tendsto k atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t * tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ)
      + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * k t)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) (k t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g
      • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) - t *
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic
      Q c lam alpha gamma)) atTop (𝓝 (η / 4 * ∑ i, lam i / (1 - η * lam i / 2))) := by
  obtain ⟨K, T, hK, hT, hb⟩ :=
    ulaAnchored_llc_budget (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀ hg
  have hev : ∀ᶠ t : ℝ in atTop, T ≤ t ∧ 0 < t ∧ (∀ i, η / t * (t * lam i + g) < 2) ∧ 1 ≤ k t :=
    ((eventually_ge_atTop T).and ((eventually_gt_atTop 0).and ((Filter.eventually_all.2 fun i =>
      (scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1).and (hk.eventually_ge_atTop
          1))))
  have hX : Tendsto (fun t : ℝ => t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma) - t * tiltedExpectation
      (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η
      / t) * (1 - Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d)
      (Fin d) ℝ)) (η / t) ^ (2 * k t)))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam *
      Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) (k t) ((t • (Q * diagonal lam * Qᵀ) + g • (1
      : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal
      lam * Qᵀ) *ᵥ u)) - (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)
      + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t + t * (η / t) / 4 * ∑
      i, lam i / (1 - η / t * (t * lam i + g) / 2) - burnScaled lam g (affineFrame Q c w₀) (Qᵀ *ᵥ
      x₀) t (η / t) (k t)) atTop (𝓝 0) := by
    refine tendsto_zero_of_abs_le ?_
      ((tendsto_const_nhds (x := K)).div_atTop (tendsto_pow_atTop two_ne_zero))
    filter_upwards [hev] with t ⟨hTt, ht0, hevt, hkt⟩
    unfold burnScaled
    exact hb hTt (div_pos hη ht0) hevt hkt x₀
  have hE : Tendsto (fun t : ℝ => (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame
      Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t) atTop (𝓝 0)
          :=
    (tendsto_const_nhds (x := (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
        w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))))).div_atTop
            tendsto_id
  have hbias := ulaScaledStep_bias_tendsto (g := g) hηl
  have hburn := burnScaled_tendsto_zero hlam hηl hg (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) hr0 hr1 hr hk
      htr
  have h := ((hbias.sub hburn).sub hE).sub hX
  simp only [sub_zero] at h
  refine h.congr (fun t => ?_)
  ring

/-- **The `n`-draw average after logarithmic burn-in**: along `k(t) = ⌈κ log t⌉₊`, `κ > 1/(2
log(1/r))`, the scaled
mean-square error `t²·avgVar + (t·avgBias)²` of `(1/n)∑_{a<n}q(X_{k+a})` against `⟨L⟩_loc` tends to
`(1/n²)(n c₀^∞ + 2∑_{j<n}(n−(j+1))c^∞_{j+1}) + b_η²`, i.e. `½∑ᵢ(1−ηλᵢ/2)⁻²F_n((1−ηλᵢ)²) + b_η²`. -/
theorem ulaAnchored_avg_mse_log_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) (hη : 0 <
    η)
    (hηl : ∀ i, η * lam i < 2) {r κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r)
    (hκ : 1 + 2 * κ * Real.log r < 0) {n : ℕ} (hn : 1 ≤ n) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.avgVar (t • (Q * diagonal lam * Qᵀ) + g • (1 :
      Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (⌈κ * Real.log t⌉₊) n x₀ + (1 / (n : ℝ) *
      ∑ a ∈ Finset.range n, (t * tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam *
      Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * (⌈κ * Real.log t⌉₊ +
      a))))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d)
      (Fin d) ℝ)) (η / t) ((⌈κ * Real.log t⌉₊ + a)) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix
      (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ)
      *ᵥ u)) - t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma))) ^ 2) atTop (𝓝 (1 / (n : ℝ) ^ 2 * (n * (1 / 2 * ∑ i,
      (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η * lam i) ^ (2 * 0)) + 2 * ∑ j ∈ Finset.range n, ((n :
      ℝ) - (j + 1)) * (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η * lam i) ^ (2 * (j +
      1)))) + (η / 4 * ∑ i, lam i / (1 - η * lam i / 2)) ^ 2)) := by
  have hκpos : 0 < κ := by nlinarith [Real.log_neg hr0 hr1]
  have hk : Tendsto (fun t : ℝ => ⌈κ * Real.log t⌉₊) atTop atTop := log_schedule_natCeil_tendsto
      hκpos
  have htr := log_schedule_tendsto hr0 hr1 hκ
  have hka : ∀ a : ℕ, Tendsto (fun t : ℝ => ⌈κ * Real.log t⌉₊ + a) atTop atTop := fun a =>
    tendsto_atTop_mono (fun t => Nat.le_add_right _ _) hk
  have htra : ∀ a : ℕ, Tendsto (fun t : ℝ => t * r ^ (2 * (⌈κ * Real.log t⌉₊ + a))) atTop (𝓝 0) :=
    fun a => by
      have := htr.mul_const (r ^ (2 * a))
      rw [zero_mul] at this
      exact this.congr' (Filter.Eventually.of_forall fun t => by ring)
  have hV := ulaAnchored_avgVar_schedule_tendsto hlam hQ c w₀ hg hη hηl hr0.le hr1 hr hk htr n x₀
  have hB := (tendsto_finsetSum (Finset.range n) fun a _ =>
    ulaAnchored_sampled_schedule_tendsto (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀
        hg
      hη hηl hr0.le hr1 hr (hka a) (htra a) x₀).const_mul (1 / (n : ℝ))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hB
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  rw [show (1 : ℝ) / n * (n * (η / 4 * ∑ i, lam i / (1 - η * lam i / 2))) = η / 4 * ∑ i, lam i / (1
      - η * lam i / 2) by rw [← mul_assoc, one_div_mul_cancel hn0, one_mul]] at hB
  exact (hV.add (hB.pow 2)).congr' (Filter.Eventually.of_forall fun t => rfl)

end Average

end Laplace.Multi
