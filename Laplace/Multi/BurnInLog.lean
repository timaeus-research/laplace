/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MinibatchScaled

/-!
# Logarithmic burn-in at the anchored scaling (E4)

Tide 99's E2–E4 budget carries the burn-in term
`Burn(t,k) = (t/2)∑ᵢλᵢρᵢ^{2k}σᵢ² − (t/2)∑ᵢλᵢ[(m̂ᵢ + ρᵢ^k(x̂₀ᵢ − m̂ᵢ))² − m̂ᵢ²]` (`burnScaled`), the
stationary value of the scaled
`k`-step ULA energy from `x₀` minus its value after `k` steps. At the β-scaled step `h = η/t` with
`0 < ηλᵢ < 2`:
* **any schedule with `k(t) → ∞` and `t·r^{2k(t)} → 0`** for some `r ∈ (maxᵢ|1−ηλᵢ|, 1)` makes the
burn-in vanish
  (`burnScaled_tendsto_zero`): the three pieces are `λᵢ(tσᵢ²)ρᵢ^{2k}`, `(t/2)λᵢρᵢ^{2k}dᵢ²`,
  `tλᵢρᵢ^k m̂ᵢ dᵢ`, with `tσᵢ²`,
  `tm̂ᵢ`, `dᵢ = x̂₀ᵢ − m̂ᵢ` convergent and `|ρᵢ(t)| ≤ r` eventually;
* **the logarithmic schedule `k(t) = ⌈κ log t⌉₊` qualifies for `κ > 1/(2 log(1/r))`**
(`log_schedule_natCeil_tendsto`,
  `log_schedule_tendsto`): for `t > 1`, `t·r^{2⌈κ log t⌉} ≤ t^{1 + 2κ log r} → 0`;
* hence **burn-in of order `log t` suffices for the scaled statistic**
(`burnScaled_log_tendsto_zero`), and, combining with the
  budget and the step-size bias limit, **`t⟨½uᵀHu⟩_{k(t)} − t⟨L⟩_loc → (η/4)∑ᵢλᵢ/(1−ηλᵢ/2)`**
  (`ulaAnchored_sampled_log_tendsto`):
  after `⌈κ log t⌉` steps the sampled scaled statistic converges to the exact localised energy plus
  the step-size bias.
-/

open Matrix Filter Topology MeasureTheory

namespace Laplace.Multi

/-! ### The burn-in term and the per-mode limits -/

/-- Tide 99's burn-in term: the stationary scaled energy minus the scaled `k`-step energy from
`x₀`. -/
noncomputable def burnScaled {d : ℕ} (lam : Fin d → ℝ) (g : ℝ) (wh xh : Fin d → ℝ) (t h : ℝ) (k :
    ℕ) :
    ℝ :=
  t / 2 * ∑ i, lam i * (1 - h * (t * lam i + g)) ^ (2 * k) /
      ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) -
    t / 2 * ∑ i, lam i * ((g * wh i / (t * lam i + g) + (1 - h * (t * lam i + g)) ^ k *
      (xh i - g * wh i / (t * lam i + g))) ^ 2 - (g * wh i / (t * lam i + g)) ^ 2)

section Scalar

variable {lam g η r : ℝ}

/-- A function squeezed in absolute value by a null function is null. -/
theorem tendsto_zero_of_abs_le {α : Type*} {l : Filter α} {f a : α → ℝ}
    (h : ∀ᶠ x in l, |f x| ≤ a x) (ha : Tendsto a l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  have hneg : Tendsto (fun x => -a x) l (𝓝 0) := by simpa using ha.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg ha
    (h.mono fun x hx => (abs_le.1 hx).1) (h.mono fun x hx => (abs_le.1 hx).2)

/-- Eventually `|ρ(t)| ≤ r` for every `r > |1 − ηλ|`. -/
theorem abs_rho_scaled_eventually_le (lam g η : ℝ) (hr : |1 - η * lam| < r) :
    ∀ᶠ t : ℝ in atTop, |1 - η / t * (t * lam + g)| ≤ r :=
  (((continuous_abs.tendsto _).comp (rho_scaled_tendsto lam g η)).eventually_lt_const hr).mono
    fun _ h => h.le

/-- `t·σ²(t) → 1/(λ(1 − ηλ/2))`. -/
theorem tsigma_scaled_tendsto (hlam : 0 < lam) (hηl : η * lam < 2) :
    Tendsto (fun t : ℝ => t * (1 / ((t * lam + g) * (1 - η / t * (t * lam + g) / 2)))) atTop
      (𝓝 (1 / (lam * (1 - η * lam / 2)))) := by
  have h := (tendsto_const_nhds (x := 1 / lam)).mul (ulaScaledStep_factor_tendsto (g := g) hlam hηl)
  rw [one_div_mul_one_div] at h
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
  have := hlam.ne'
  field_simp

/-- `|x^k| ≤ r^k` from `|x| ≤ r`. -/
theorem abs_pow_le_pow_of_abs_le {x : ℝ} (hx : |x| ≤ r) (k : ℕ) : |x ^ k| ≤ r ^ k := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hx k

/-- `ρ(t)^{k(t)} → 0` along any `k(t) → ∞` once `|ρ(t)| ≤ r < 1` eventually. -/
theorem rho_pow_schedule_tendsto_zero (hr0 : 0 ≤ r) (hr1 : r < 1) {ρ : ℝ → ℝ}
    (hρ : ∀ᶠ t : ℝ in atTop, |ρ t| ≤ r) {k : ℝ → ℕ} (hk : Tendsto k atTop atTop) :
    Tendsto (fun t : ℝ => ρ t ^ k t) atTop (𝓝 0) :=
  tendsto_zero_of_abs_le (hρ.mono fun t ht => abs_pow_le_pow_of_abs_le ht (k t))
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hk)

/-- `t·ρ(t)^{2k(t)} → 0` given `t·r^{2k(t)} → 0`. -/
theorem mul_rho_pow_schedule_tendsto_zero {ρ : ℝ → ℝ} (hρ : ∀ᶠ t : ℝ in atTop, |ρ t| ≤ r)
    {k : ℝ → ℕ} (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => t * ρ t ^ (2 * k t)) atTop (𝓝 0) := by
  refine tendsto_zero_of_abs_le ?_ htr
  filter_upwards [hρ, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  rw [abs_mul, abs_of_nonneg ht0]
  exact mul_le_mul_of_nonneg_left (abs_pow_le_pow_of_abs_le ht (2 * k t)) ht0

/-! ### The logarithmic schedule -/

/-- `κ log t → ∞` for `κ > 0`, hence `⌈κ log t⌉₊ → ∞`. -/
theorem log_schedule_natCeil_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => ⌈κ * Real.log t⌉₊) atTop atTop :=
  tendsto_natCast_atTop_iff.1
    (tendsto_atTop_mono (fun t => Nat.le_ceil (κ * Real.log t))
      (Real.tendsto_log_atTop.const_mul_atTop hκ))

/-- For `t > 1`, `t·r^{2⌈κ log t⌉₊} ≤ t^{1 + 2κ log r}`. -/
theorem mul_pow_natCeil_le_rpow {κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hκ : 0 ≤ κ) {t : ℝ} (ht : 1 <
    t) :
    t * r ^ (2 * ⌈κ * Real.log t⌉₊) ≤ t ^ (1 + 2 * κ * Real.log r) := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 ≤ κ * Real.log t := mul_nonneg hκ (Real.log_pos ht).le
  have h1 : r ^ (2 * ⌈κ * Real.log t⌉₊) ≤ r ^ (2 * κ * Real.log t) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le ?_
    push_cast
    linarith [Nat.le_ceil (κ * Real.log t)]
  have h2 : t * r ^ (2 * κ * Real.log t) = t ^ (1 + 2 * κ * Real.log r) := by
    rw [Real.rpow_def_of_pos hr0, Real.rpow_def_of_pos ht0]
    have e : Real.log t * (1 + 2 * κ * Real.log r) =
        Real.log t + Real.log r * (2 * κ * Real.log t) := by ring
    rw [e, Real.exp_add, Real.exp_log ht0]
  calc t * r ^ (2 * ⌈κ * Real.log t⌉₊) ≤ t * r ^ (2 * κ * Real.log t) :=
        mul_le_mul_of_nonneg_left h1 ht0.le
    _ = t ^ (1 + 2 * κ * Real.log r) := h2

/-- **The logarithmic schedule**: for `0 < r < 1` and `1 + 2κ log r < 0` (i.e. `κ > 1/(2
log(1/r))`),
`t·r^{2⌈κ log t⌉₊} → 0`. -/
theorem log_schedule_tendsto {κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hκ : 1 + 2 * κ * Real.log r < 0) :
    Tendsto (fun t : ℝ => t * r ^ (2 * ⌈κ * Real.log t⌉₊)) atTop (𝓝 0) := by
  have hlr := Real.log_neg hr0 hr1
  have hκpos : 0 < κ := by nlinarith
  have hlim : Tendsto (fun t : ℝ => t ^ (1 + 2 * κ * Real.log r)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := -(1 + 2 * κ * Real.log r)) (by linarith)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact mul_pow_natCeil_le_rpow hr0 hr1 hκpos.le ht

end Scalar

/-! ### The general vanishing criterion -/

section Criterion

variable {d : ℕ} {lam : Fin d → ℝ} {g η : ℝ}

/-- **Burn-in vanishes along any schedule with `k(t) → ∞` and `t·r^{2k(t)} → 0`**, `r ∈
(maxᵢ|1−ηλᵢ|, 1)`. -/
theorem burnScaled_tendsto_zero (hlam : ∀ i, 0 < lam i) (hηl : ∀ i, η * lam i < 2) (hg : 0 ≤ g)
    (wh xh : Fin d → ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r)
    {k : ℝ → ℕ} (hk : Tendsto k atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => burnScaled lam g wh xh t (η / t) (k t)) atTop (𝓝 0) := by
  have e : ∀ t : ℝ, burnScaled lam g wh xh t (η / t) (k t) = ∑ i, (lam i / 2 * (t * (1 / ((t * lam i
      + g) * (1 - η / t * (t * lam i + g) / 2)))) * (1 - η / t * (t * lam i + g)) ^ (2 * k t) - (lam
      i * (1 - η / t * (t * lam i + g)) ^ k t * (t * (g * wh i / (t * lam i + g))) * (xh i - g * wh
      i / (t * lam i + g)) + lam i / 2 * (t * (1 - η / t * (t * lam i + g)) ^ (2 * k t)) * (xh i - g
      * wh i / (t * lam i + g)) ^ 2)) := by
    intro t
    unfold burnScaled
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  have hk2 : Tendsto (fun t => 2 * k t) atTop atTop :=
    tendsto_atTop_mono (fun t => by omega) hk
  have h : Tendsto (fun t : ℝ => ∑ i, (lam i / 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t *
      lam i + g) / 2)))) * (1 - η / t * (t * lam i + g)) ^ (2 * k t) - (lam i * (1 - η / t * (t *
      lam i + g)) ^ k t * (t * (g * wh i / (t * lam i + g))) * (xh i - g * wh i / (t * lam i + g)) +
      lam i / 2 * (t * (1 - η / t * (t * lam i + g)) ^ (2 * k t)) * (xh i - g * wh i / (t * lam i +
      g)) ^ 2))) atTop (𝓝 (∑ i : Fin d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => by
      have hρ := abs_rho_scaled_eventually_le (lam i) g η (hr i)
      have hd : Tendsto (fun t : ℝ => xh i - g * wh i / (t * lam i + g)) atTop (𝓝 (xh i - 0)) :=
        tendsto_const_nhds.sub (anchoredMean_tendsto_zero (hlam i) g (wh i))
      have h1 := ((tendsto_const_nhds (x := lam i / 2)).mul
        (tsigma_scaled_tendsto (g := g) (hlam i) (hηl i))).mul
        (rho_pow_schedule_tendsto_zero hr0 hr1 hρ hk2)
      have h2 := ((((tendsto_const_nhds (x := lam i)).mul
        (rho_pow_schedule_tendsto_zero hr0 hr1 hρ hk)).mul
        (mul_anchoredMean_tendsto (hlam i) hg (wh i))).mul hd).add
        (((tendsto_const_nhds (x := lam i / 2)).mul (mul_rho_pow_schedule_tendsto_zero hρ htr)).mul
          (hd.pow 2))
      have := h1.sub h2
      simpa using this
  simpa using h

end Criterion

/-! ### Logarithmic burn-in suffices -/

section Log

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g η : ℝ}

/-- **Burn-in of order `log t` suffices**: `Burn(t, ⌈κ log t⌉₊) → 0` for `κ > 1/(2 log(1/r))`, `r ∈
(maxᵢ|1−ηλᵢ|, 1)`. -/
theorem burnScaled_log_tendsto_zero (hlam : ∀ i, 0 < lam i) (hηl : ∀ i, η * lam i < 2) (hg : 0 ≤ g)
    (wh xh : Fin d → ℝ) {r κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r)
    (hκ : 1 + 2 * κ * Real.log r < 0) :
    Tendsto (fun t : ℝ => burnScaled lam g wh xh t (η / t) ⌈κ * Real.log t⌉₊) atTop (𝓝 0) := by
  have hκpos : 0 < κ := by nlinarith [Real.log_neg hr0 hr1]
  exact burnScaled_tendsto_zero hlam hηl hg wh xh hr0.le hr1 hr (log_schedule_natCeil_tendsto hκpos)
    (log_schedule_tendsto hr0 hr1 hκ)

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **E2–E4 at the logarithmic schedule**: along `k(t) = ⌈κ log t⌉₊` with `κ > 1/(2 log(1/r))`, the
sampled scaled
statistic converges to the localised energy plus the step-size bias,
`t⟨½uᵀHu⟩_{k(t)} − t⟨L⟩_loc → (η/4)∑ᵢλᵢ/(1−ηλᵢ/2)`. -/
theorem ulaAnchored_sampled_log_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) (hη : 0 <
    η)
    (hηl : ∀ i, η * lam i < 2) {r κ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r)
    (hκ : 1 + 2 * κ * Real.log r < 0) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t * tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ)
      + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * ⌈κ * Real.log t⌉₊)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) ⌈κ * Real.log t⌉₊ ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) - t *
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic
      Q c lam alpha gamma)) atTop (𝓝 (η / 4 * ∑ i, lam i / (1 - η * lam i / 2))) := by
  have hκpos : 0 < κ := by nlinarith [Real.log_neg hr0 hr1]
  have hk : Tendsto (fun t : ℝ => ⌈κ * Real.log t⌉₊) atTop atTop := log_schedule_natCeil_tendsto
      hκpos
  obtain ⟨K, T, hK, hT, hb⟩ :=
    ulaAnchored_llc_budget (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀ hg
  have hev : ∀ᶠ t : ℝ in atTop,
      T ≤ t ∧ 0 < t ∧ (∀ i, η / t * (t * lam i + g) < 2) ∧ 1 ≤ ⌈κ * Real.log t⌉₊ :=
    ((eventually_ge_atTop T).and ((eventually_gt_atTop 0).and ((Filter.eventually_all.2 fun i =>
      (scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1).and (hk.eventually_ge_atTop
          1))))
  have hX : Tendsto (fun t : ℝ => t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma) - t * tiltedExpectation
      (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η
      / t) * (1 - Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d)
      (Fin d) ℝ)) (η / t) ^ (2 * ⌈κ * Real.log t⌉₊)))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ⌈κ * Real.log t⌉₊ ((t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1
      / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) - (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma
      i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i)))
      / t + t * (η / t) / 4 * ∑ i, lam i / (1 - η / t * (t * lam i + g) / 2) - burnScaled lam g
      (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) t (η / t) ⌈κ * Real.log t⌉₊) atTop (𝓝 0) := by
    refine tendsto_zero_of_abs_le ?_ ((tendsto_const_nhds (x := K)).div_atTop (tendsto_pow_atTop
        two_ne_zero))
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
  have hburn := burnScaled_log_tendsto_zero hlam hηl hg (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) hr0 hr1 hr
      hκ
  have h := ((hbias.sub hburn).sub hE).sub hX
  simp only [sub_zero] at h
  refine h.congr (fun t => ?_)
  ring

end Log

end Laplace.Multi
