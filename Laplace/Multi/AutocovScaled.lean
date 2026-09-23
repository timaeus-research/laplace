/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ULAAutocovariance

/-!
# The ULA long-run variance at the β-scaled step (E5 at the anchored scaling)

On the anchored quadratic model `P_t = tH + g·1`, `pᵢ = tλᵢ + g`, anchored mean `m̂ᵢ = gŵᵢ/pᵢ` (`ŵ
= affineFrame Q c w₀`),
tide 102's formulas read (`ulaAnchored_autoCov`, `ulaAnchored_longRunVar`)
**`τ²(t, h) = ∑ᵢλᵢ²(1+ρᵢ²)/(4hpᵢ³κᵢ³) + 2∑ᵢλᵢ²(gŵᵢ/pᵢ)²/(hpᵢ²)`**, `ρᵢ = 1 − hpᵢ`, `κᵢ = 1 −
hpᵢ/2`. At the β-scaled step
`h = η/t` with `0 < ηλᵢ < 2`: `ρᵢ(t) → 1 − ηλᵢ` (`rho_scaled_tendsto`), the integrated
autocorrelation times
**`(1+ρᵢ²)/(1−ρᵢ²) → (1+(1−ηλᵢ)²)/(ηλᵢ(2−ηλᵢ))`**, **`(1+ρᵢ)/(1−ρᵢ) → (2−ηλᵢ)/(ηλᵢ)`**
(`iat_quad_scaled_tendsto`,
`iat_lin_scaled_tendsto`), the main term `t²∑λᵢ²(1+ρᵢ²)/(4hpᵢ³κᵢ³) = ∑(1+ρᵢ²)/(4ηλᵢ)·(tλᵢ/(pᵢκᵢ))³`
tends to
**`L_η = ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)`** and the mean term `t²·2∑λᵢ²(gŵᵢ/pᵢ)²/(hpᵢ²) = O(1/t)`
vanishes
(`ulaScaledStep_longRunVar_main_tendsto`, `ulaScaledStep_longRunVar_mean_tendsto`), so
**`t² · τ²(t, η/t) → L_η`** (`ulaScaledStep_longRunVar_tendsto`, `ulaAnchored_longRunVar_tendsto`):
the long-run variance of
the scaled statistic `t·½uᵀHu` along the stationary chain is asymptotically `t`-independent, and so
is the number of
stationary steps for a fixed absolute precision. For comparison the single-sample variance of the
scaled statistic
tends to `½∑ᵢ(1−ηλᵢ/2)⁻²` (`ulaScaledStep_var0_tendsto`), and per mode the ratio of the two limits
is the limiting
quadratic integrated autocorrelation time (`longRun_ratio_eq_iat`): `n` stationary steps are worth
`n·ηλᵢ(2−ηλᵢ)/(1+(1−ηλᵢ)²)`
independent samples of mode `i`, a fraction `≤ 1` with equality at `ηλᵢ = 1`
(`one_le_iat_quad_limit`, `longRun_limit_ge_var0`).
The anchored-mean contribution decays at the exact rate `t·t²M(t) → (2g²/η)∑ᵢŵᵢ²/λᵢ²`
(`ulaScaledStep_longRunVar_mean_rate`), and
the fixed-lag scaled autocovariance tends to `½∑ᵢ(1−ηλᵢ/2)⁻²(1−ηλᵢ)^{2ℓ}`
(`ulaScaledStep_autoCov_tendsto`).
-/

open Matrix Filter Topology MeasureTheory

namespace Laplace.Multi

/-! ### Per-mode limits at `h = η/t` -/

section Scalar

variable {lam g η : ℝ}

/-- `(η/t)(tλ + g) → ηλ`. -/
theorem scaledStep_mul_tendsto (lam g η : ℝ) :
    Tendsto (fun t : ℝ => η / t * (t * lam + g)) atTop (𝓝 (η * lam)) := by
  have e : (fun t : ℝ => η * lam + η * g / t) =ᶠ[atTop] fun t => η / t * (t * lam + g) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp
  have hz : Tendsto (fun t : ℝ => η * g / t) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := η * g)).div_atTop tendsto_id
  have h := (tendsto_const_nhds (x := η * lam)).add hz
  rw [add_zero] at h
  exact h.congr' e

/-- `ρ(t) = 1 − (η/t)(tλ + g) → 1 − ηλ`. -/
theorem rho_scaled_tendsto (lam g η : ℝ) :
    Tendsto (fun t : ℝ => 1 - η / t * (t * lam + g)) atTop (𝓝 (1 - η * lam)) :=
  (scaledStep_mul_tendsto lam g η).const_sub 1

/-- `κ(t) = 1 − (η/t)(tλ + g)/2 → 1 − ηλ/2`. -/
theorem kappa_scaled_tendsto (lam g η : ℝ) :
    Tendsto (fun t : ℝ => 1 - η / t * (t * lam + g) / 2) atTop (𝓝 (1 - η * lam / 2)) :=
  ((scaledStep_mul_tendsto lam g η).div_const 2).const_sub 1

/-- Eventual stability and positivity of `κ` at the β-scaled step. -/
theorem scaledStep_eventually (hηl : η * lam < 2) :
    ∀ᶠ t : ℝ in atTop, η / t * (t * lam + g) < 2 ∧ 0 < 1 - η / t * (t * lam + g) / 2 :=
  ((scaledStep_mul_tendsto lam g η).eventually_lt_const hηl).and
    ((kappa_scaled_tendsto lam g η).eventually_const_lt (by linarith))

theorem one_sub_sq_pos_of_scaled (hlam : 0 < lam) (hη : 0 < η) (hηl : η * lam < 2) :
    0 < 1 - (1 - η * lam) ^ 2 := by
  have := mul_pos hη hlam
  nlinarith

/-- The quadratic integrated autocorrelation time `(1+ρ²)/(1−ρ²) → (1+(1−ηλ)²)/(ηλ(2−ηλ))`. -/
theorem iat_quad_scaled_tendsto (hlam : 0 < lam) (hη : 0 < η) (hηl : η * lam < 2) :
    Tendsto (fun t : ℝ => (1 + (1 - η / t * (t * lam + g)) ^ 2) / (1 - (1 - η / t * (t * lam + g))
        ^ 2))
      atTop (𝓝 ((1 + (1 - η * lam) ^ 2) / (η * lam * (2 - η * lam)))) := by
  have hρ := rho_scaled_tendsto lam g η
  rw [show (1 + (1 - η * lam) ^ 2) / (η * lam * (2 - η * lam)) =
    (1 + (1 - η * lam) ^ 2) / (1 - (1 - η * lam) ^ 2) by ring]
  exact ((hρ.pow 2).const_add 1).div ((hρ.pow 2).const_sub 1)
    (one_sub_sq_pos_of_scaled hlam hη hηl).ne'

/-- The mean-part integrated autocorrelation time `(1+ρ)/(1−ρ) → (2−ηλ)/(ηλ)`. -/
theorem iat_lin_scaled_tendsto (hlam : 0 < lam) (hη : 0 < η) :
    Tendsto (fun t : ℝ => (1 + (1 - η / t * (t * lam + g))) / (1 - (1 - η / t * (t * lam + g))))
      atTop (𝓝 ((2 - η * lam) / (η * lam))) := by
  have hρ := rho_scaled_tendsto lam g η
  rw [show (2 - η * lam) / (η * lam) = (1 + (1 - η * lam)) / (1 - (1 - η * lam)) by ring]
  exact (hρ.const_add 1).div (hρ.const_sub 1) (by have := mul_pos hη hlam; linarith)

/-- `tλ/(tλ + g) → 1`. -/
theorem ratio_scaled_tendsto (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => t * lam / (t * lam + g)) atTop (𝓝 1) := by
  have e : (fun t : ℝ => lam / (lam + g / t)) =ᶠ[atTop] fun t => t * lam / (t * lam + g) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp
  have hz : Tendsto (fun t : ℝ => g / t) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := g)).div_atTop tendsto_id
  have h := (tendsto_const_nhds (x := lam)).div ((tendsto_const_nhds (x := lam)).add hz)
    (by rw [add_zero]; exact hlam.ne')
  rw [add_zero, div_self hlam.ne'] at h
  exact h.congr' e

/-- `1/(λ(tλ + g)) → 0`. -/
theorem inv_scaled_tendsto (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => 1 / (lam * (t * lam + g))) atTop (𝓝 0) :=
  (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
    ((tendsto_atTop_add_const_right atTop g (tendsto_id.atTop_mul_const hlam)).const_mul_atTop hlam)

/-- `1/(tλ + g) → 0`. -/
theorem inv_p_tendsto (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => 1 / (t * lam + g)) atTop (𝓝 0) :=
  (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
    (tendsto_atTop_add_const_right atTop g (tendsto_id.atTop_mul_const hlam))

/-- The limiting ratio of the long-run to the single-sample variance of a mode is its limiting
quadratic integrated autocorrelation time. -/
theorem longRun_ratio_eq_iat (hlam : 0 < lam) (hη : 0 < η) (hηl : η * lam < 2) :
    (1 + (1 - η * lam) ^ 2) / (4 * η * lam * (1 - η * lam / 2) ^ 3) /
        (1 / 2 * (1 / (1 - η * lam / 2)) ^ 2) =
      (1 + (1 - η * lam) ^ 2) / (η * lam * (2 - η * lam)) := by
  have hx : η * lam ≠ 0 := (mul_pos hη hlam).ne'
  have hk : 2 - η * lam ≠ 0 := by linarith
  have hk' : 1 - η * lam / 2 ≠ 0 := by linarith
  field_simp
  ring

/-- `IAT_quad(∞) − 1 = 2(1−ηλ)²/(ηλ(2−ηλ))`. -/
theorem iat_quad_limit_sub_one (hlam : 0 < lam) (hη : 0 < η) (hηl : η * lam < 2) :
    (1 + (1 - η * lam) ^ 2) / (η * lam * (2 - η * lam)) - 1 =
      2 * (1 - η * lam) ^ 2 / (η * lam * (2 - η * lam)) := by
  have hx : η * lam ≠ 0 := (mul_pos hη hlam).ne'
  have hk : 2 - η * lam ≠ 0 := by linarith
  field_simp
  ring

/-- The effective-sample-size fraction of a mode is at most one: `1 ≤ IAT_quad(∞)`, with equality
exactly at `ηλ = 1` (`ρ = 0`). -/
theorem one_le_iat_quad_limit (hlam : 0 < lam) (hη : 0 < η) (hηl : η * lam < 2) :
    1 ≤ (1 + (1 - η * lam) ^ 2) / (η * lam * (2 - η * lam)) := by
  rw [le_div_iff₀ (mul_pos (mul_pos hη hlam) (by linarith))]
  nlinarith [sq_nonneg (1 - η * lam)]

/-- `L_η ≥ ½∑ᵢ(1−ηλᵢ/2)⁻²` mode by mode: the chain average is never better than independent
replicates. -/
theorem longRun_limit_ge_var0 (hlam : 0 < lam) (hη : 0 < η) (hηl : η * lam < 2) :
    1 / 2 * (1 / (1 - η * lam / 2)) ^ 2 ≤
      (1 + (1 - η * lam) ^ 2) / (4 * η * lam * (1 - η * lam / 2) ^ 3) := by
  have hk : 0 < 1 - η * lam / 2 := by linarith
  have hV : 0 < 1 / 2 * (1 / (1 - η * lam / 2)) ^ 2 :=
    mul_pos one_half_pos (pow_pos (one_div_pos.2 hk) 2)
  have h := one_le_iat_quad_limit hlam hη hηl
  rw [← longRun_ratio_eq_iat hlam hη hηl, le_div_iff₀ hV, one_mul] at h
  exact h

end Scalar

/-! ### The anchored model -/

section Anchored

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g : ℝ}

/-- `m̂ᵢ = gŵᵢ/(tλᵢ + g)` for the anchored mean `P_t⁻¹ g(w₀ − c)`. -/
theorem transpose_mulVec_anchoredMean (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) (i : Fin d) :
    (Qᵀ *ᵥ ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ -
        c)))) i = g * affineFrame Q c w₀ i / (t * lam i + g) := by
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  rw [Laplace.Sampler.inv_localisedPrecision_eq_conj_frame hQ hdiagH hlam ht hg, ←
      Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Qᵀ Q, hQ, Matrix.one_mulVec,
        Matrix.mulVec_diagonal,
    Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  unfold affineFrame
  ring

/-- Tide 102's autocovariance on the anchored model. -/
theorem ulaAnchored_autoCov (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤
    g)
    {t : ℝ} (ht : 0 < t) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * (t * lam i + g) < 2) (ℓ : ℕ) :
    Laplace.Sampler.ulaAutoCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (Q
      * diagonal lam * Qᵀ) h ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹
      *ᵥ (g • (w₀ - c))) ℓ = 1 / 2 * ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - h * (t * lam i + g)
      / 2)))) ^ 2 * (1 - h * (t * lam i + g)) ^ (2 * ℓ) + ∑ i, lam i ^ 2 * (1 / ((t * lam i + g) *
      (1 - h * (t * lam i + g) / 2))) * (g * affineFrame Q c w₀ i / (t * lam i + g)) ^ 2 * (1 - h *
      (t * lam i + g)) ^ ℓ := by
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have hdiagP := transpose_localisedPrecision_conj (lam := lam) hQ t g
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  rw [Laplace.Sampler.ulaAutoCov_eq hQ hdiagP hp hh hev hdiagH ℓ]
  simp only [transpose_mulVec_anchoredMean hlam hQ c w₀ hg ht]

/-- Tide 102's long-run variance on the anchored model, in sampler variables. -/
theorem ulaAnchored_longRunVar (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * (t * lam i + g) < 2) :
    Laplace.Sampler.ulaLongRunVar (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))
      (Q * diagonal lam * Qᵀ) h ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ))⁻¹ *ᵥ (g • (w₀ - c))) = ∑ i, lam i ^ 2 * (1 + (1 - h * (t * lam i + g)) ^ 2) / (4 * h * (t
      * lam i + g) ^ 3 * (1 - h * (t * lam i + g) / 2) ^ 3) + 2 * ∑ i, lam i ^ 2 * (g * affineFrame
      Q c w₀ i / (t * lam i + g)) ^ 2 / (h * (t * lam i + g) ^ 2) := by
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have hdiagP := transpose_localisedPrecision_conj (lam := lam) hQ t g
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  rw [Laplace.Sampler.ulaLongRunVar_eq_sampler hQ hdiagP hp hh hev hdiagH]
  simp only [transpose_mulVec_anchoredMean hlam hQ c w₀ hg ht]

end Anchored

/-! ### The β-scaled limits -/

section Scaled

variable {d : ℕ} {lam : Fin d → ℝ} {g η : ℝ}

/-- The main term: `t²∑λᵢ²(1+ρᵢ²)/(4hpᵢ³κᵢ³) → ∑(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)`. -/
theorem ulaScaledStep_longRunVar_main_tendsto (hlam : ∀ i, 0 < lam i) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) (hg : 0 ≤ g) :
    Tendsto (fun t : ℝ => t ^ 2 * (∑ i, lam i ^ 2 * (1 + (1 - (η / t) * (t * lam i + g)) ^ 2) / (4 *
      (η / t) * (t * lam i + g) ^ 3 * (1 - (η / t) * (t * lam i + g) / 2) ^ 3))) atTop (𝓝 (∑ i, (1 +
      (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3))) := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ ∀ i, 0 < 1 - η / t * (t * lam i + g) / 2 :=
    (eventually_gt_atTop 0).and (Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.2))
  have e : (fun t : ℝ => ∑ i, (1 + (1 - (η / t) * (t * lam i + g)) ^ 2) / (4 * η * lam i) * (t * lam
      i / ((t * lam i + g) * (1 - (η / t) * (t * lam i + g) / 2))) ^ 3) =ᶠ[atTop] fun t => t ^ 2 *
      (∑ i, lam i ^ 2 * (1 + (1 - (η / t) * (t * lam i + g)) ^ 2) / (4 * (η / t) * (t * lam i + g) ^
      3 * (1 - (η / t) * (t * lam i + g) / 2) ^ 3)) := by
    filter_upwards [hev] with t ⟨ht, hκ⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : t * lam i + g ≠ 0 := by have := hlam i; positivity
    have := (hlam i).ne'
    have := hη.ne'
    have := ht.ne'
    have := (hκ i).ne'
    field_simp
  refine Tendsto.congr' e (tendsto_finsetSum Finset.univ fun i _ => ?_)
  have hf := ulaScaledStep_factor_tendsto (g := g) (hlam i) (hηl i)
  have hρ := rho_scaled_tendsto (lam i) g η
  have hne : 1 - η * lam i / 2 ≠ 0 := by linarith [hηl i]
  rw [show (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3) =
    (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i) * (1 / (1 - η * lam i / 2)) ^ 3 by
      field_simp]
  exact (((hρ.pow 2).const_add 1).div_const (4 * η * lam i)).mul (hf.pow 3)

/-- The mean term vanishes: `t²·2∑λᵢ²(gŵᵢ/pᵢ)²/(hpᵢ²) → 0`. -/
theorem ulaScaledStep_longRunVar_mean_tendsto (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hg : 0 ≤ g)
    (wh : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * (2 * ∑ i, lam i ^ 2 * (g * wh i / (t * lam i + g)) ^ 2 / ((η / t)
      * (t * lam i + g) ^ 2))) atTop (𝓝 0) := by
  have e : (fun t : ℝ => ∑ i, 2 * g ^ 2 * wh i ^ 2 / η * (t * lam i / (t * lam i + g)) ^ 3 * (1 /
      (lam i * (t * lam i + g)))) =ᶠ[atTop] fun t => t ^ 2 * (2 * ∑ i, lam i ^ 2 * (g * wh i / (t *
      lam i + g)) ^ 2 / ((η / t) * (t * lam i + g) ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : t * lam i + g ≠ 0 := by have := hlam i; positivity
    have := (hlam i).ne'
    have := hη.ne'
    have := ht.ne'
    field_simp
  refine Tendsto.congr' e ?_
  have h : Tendsto (fun t : ℝ => ∑ i, 2 * g ^ 2 * wh i ^ 2 / η * (t * lam i / (t * lam i + g)) ^ 3 *
      (1 / (lam i * (t * lam i + g)))) atTop (𝓝 (∑ i : Fin d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => by
      have := ((tendsto_const_nhds (x := 2 * g ^ 2 * wh i ^ 2 / η)).mul
        ((ratio_scaled_tendsto (g := g) (hlam i)).pow 3)).mul (inv_scaled_tendsto (g := g) (hlam i))
      simpa using this
  simpa using h

/-- **`t²τ²(t, η/t) → L_η`** for the closed form. -/
theorem ulaScaledStep_longRunVar_tendsto (hlam : ∀ i, 0 < lam i) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) (hg : 0 ≤ g) (wh : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * (∑ i, lam i ^ 2 * (1 + (1 - (η / t) * (t * lam i + g)) ^ 2) / (4 *
      (η / t) * (t * lam i + g) ^ 3 * (1 - (η / t) * (t * lam i + g) / 2) ^ 3) + 2 * ∑ i, lam i ^ 2
      * (g * wh i / (t * lam i + g)) ^ 2 / ((η / t) * (t * lam i + g) ^ 2))) atTop (𝓝 (∑ i, (1 + (1
      - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3))) := by
  have h := (ulaScaledStep_longRunVar_main_tendsto hlam hη hηl hg).add
    (ulaScaledStep_longRunVar_mean_tendsto hlam hη hg wh)
  rw [add_zero] at h
  exact h.congr' (Filter.Eventually.of_forall fun t => by ring)

/-- The single-sample variance of the scaled statistic: `t²c₀(t) → ½∑ᵢ(1−ηλᵢ/2)⁻²`. -/
theorem ulaScaledStep_var0_tendsto (hlam : ∀ i, 0 < lam i) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) (hg : 0 ≤ g) (wh : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * (1 / 2 * ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - (η / t) * (t *
      lam i + g) / 2)))) ^ 2 + ∑ i, lam i ^ 2 * (1 / ((t * lam i + g) * (1 - (η / t) * (t * lam i +
      g) / 2))) * (g * wh i / (t * lam i + g)) ^ 2)) atTop (𝓝 (1 / 2 * ∑ i, (1 / (1 - η * lam i /
      2)) ^ 2)) := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ ∀ i, 0 < 1 - η / t * (t * lam i + g) / 2 :=
    (eventually_gt_atTop 0).and (Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.2))
  have e : (fun t : ℝ => t ^ 2 / 2 * ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - (η / t) * (t * lam i
      + g) / 2)))) ^ 2 + ∑ i, g ^ 2 * wh i ^ 2 * (t * lam i / ((t * lam i + g) * (1 - (η / t) * (t *
      lam i + g) / 2))) * (t * lam i / (t * lam i + g)) * (1 / (t * lam i + g))) =ᶠ[atTop] fun t =>
      t ^ 2 * (1 / 2 * ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - (η / t) * (t * lam i + g) / 2))))
      ^ 2 + ∑ i, lam i ^ 2 * (1 / ((t * lam i + g) * (1 - (η / t) * (t * lam i + g) / 2))) * (g * wh
      i / (t * lam i + g)) ^ 2) := by
    filter_upwards [hev] with t ⟨ht, hκ⟩
    rw [mul_add]
    congr 1
    · ring
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : t * lam i + g ≠ 0 := by have := hlam i; positivity
    have := (hlam i).ne'
    have := hη.ne'
    have := ht.ne'
    have := (hκ i).ne'
    field_simp
  refine Tendsto.congr' e ?_
  have h2 : Tendsto (fun t : ℝ => ∑ i, g ^ 2 * wh i ^ 2 * (t * lam i / ((t * lam i + g) *
      (1 - η / t * (t * lam i + g) / 2))) * (t * lam i / (t * lam i + g)) * (1 / (t * lam i + g)))
      atTop (𝓝 (∑ i : Fin d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => by
      have := (((tendsto_const_nhds (x := g ^ 2 * wh i ^ 2)).mul
        (ulaScaledStep_factor_tendsto (g := g) (hlam i) (hηl i))).mul
        (ratio_scaled_tendsto (g := g) (hlam i))).mul (inv_p_tendsto (g := g) (hlam i))
      simpa using this
  have h := (ulaScaledStep_var_main_tendsto (g := g) hlam hηl).add h2
  simpa using h

/-- The anchored-mean contribution decays like `1/t`: `t · t²M(t) → (2g²/η)∑ᵢŵᵢ²/λᵢ²`. -/
theorem ulaScaledStep_longRunVar_mean_rate (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hg : 0 ≤ g)
    (wh : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t * (t ^ 2 * (2 * ∑ i, lam i ^ 2 * (g * wh i / (t * lam i + g)) ^ 2 / ((η
      / t) * (t * lam i + g) ^ 2)))) atTop (𝓝 (2 * g ^ 2 / η * ∑ i, wh i ^ 2 / lam i ^ 2)) := by
  have e : (fun t : ℝ => ∑ i, 2 * g ^ 2 / η * (wh i ^ 2 / lam i ^ 2) * (t * lam i / (t * lam i + g))
      ^ 4) =ᶠ[atTop] fun t => t * (t ^ 2 * (2 * ∑ i, lam i ^ 2 * (g * wh i / (t * lam i + g)) ^ 2 /
      ((η / t) * (t * lam i + g) ^ 2))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : t * lam i + g ≠ 0 := by have := hlam i; positivity
    have := (hlam i).ne'
    have := hη.ne'
    have := ht.ne'
    field_simp
  refine Tendsto.congr' e ?_
  have h : Tendsto (fun t : ℝ => ∑ i, 2 * g ^ 2 / η * (wh i ^ 2 / lam i ^ 2) *
      (t * lam i / (t * lam i + g)) ^ 4) atTop
      (𝓝 (∑ i, 2 * g ^ 2 / η * (wh i ^ 2 / lam i ^ 2) * (1 : ℝ) ^ 4)) :=
    tendsto_finsetSum Finset.univ fun i _ =>
      (tendsto_const_nhds (x := 2 * g ^ 2 / η * (wh i ^ 2 / lam i ^ 2))).mul
        ((ratio_scaled_tendsto (g := g) (hlam i)).pow 4)
  simpa [Finset.mul_sum] using h

/-- Fixed-lag scaled autocovariance: `t²c_ℓ(t) → ½∑ᵢ(1−ηλᵢ/2)⁻²(1−ηλᵢ)^{2ℓ}`. -/
theorem ulaScaledStep_autoCov_tendsto (hlam : ∀ i, 0 < lam i) (hη : 0 < η)
    (hηl : ∀ i, η * lam i < 2) (hg : 0 ≤ g) (wh : Fin d → ℝ) (ℓ : ℕ) :
    Tendsto (fun t : ℝ => t ^ 2 * (1 / 2 * ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - (η / t) * (t *
      lam i + g) / 2)))) ^ 2 * (1 - (η / t) * (t * lam i + g)) ^ (2 * ℓ) + ∑ i, lam i ^ 2 * (1 / ((t
      * lam i + g) * (1 - (η / t) * (t * lam i + g) / 2))) * (g * wh i / (t * lam i + g)) ^ 2 * (1 -
      (η / t) * (t * lam i + g)) ^ ℓ)) atTop (𝓝 (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η
      * lam i) ^ (2 * ℓ))) := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ ∀ i, 0 < 1 - η / t * (t * lam i + g) / 2 :=
    (eventually_gt_atTop 0).and (Filter.eventually_all.2 fun i =>
      ((scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.2))
  have e : (fun t : ℝ => 1 / 2 * ∑ i, (t * lam i / ((t * lam i + g) * (1 - (η / t) * (t * lam i + g)
      / 2))) ^ 2 * (1 - (η / t) * (t * lam i + g)) ^ (2 * ℓ) + ∑ i, g ^ 2 * wh i ^ 2 * (t * lam i /
      ((t * lam i + g) * (1 - (η / t) * (t * lam i + g) / 2))) * (t * lam i / (t * lam i + g)) * (1
      / (t * lam i + g)) * (1 - (η / t) * (t * lam i + g)) ^ ℓ) =ᶠ[atTop] fun t => t ^ 2 * (1 / 2 *
      ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - (η / t) * (t * lam i + g) / 2)))) ^ 2 * (1 - (η /
      t) * (t * lam i + g)) ^ (2 * ℓ) + ∑ i, lam i ^ 2 * (1 / ((t * lam i + g) * (1 - (η / t) * (t *
      lam i + g) / 2))) * (g * wh i / (t * lam i + g)) ^ 2 * (1 - (η / t) * (t * lam i + g)) ^ ℓ) :=
      by
    filter_upwards [hev] with t ⟨ht, hκ⟩
    rw [mul_add]
    congr 1
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hp : t * lam i + g ≠ 0 := by have := hlam i; positivity
      have := (hlam i).ne'
      have := hη.ne'
      have := ht.ne'
      have := (hκ i).ne'
      field_simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hp : t * lam i + g ≠ 0 := by have := hlam i; positivity
      have := (hlam i).ne'
      have := hη.ne'
      have := ht.ne'
      have := (hκ i).ne'
      field_simp
  refine Tendsto.congr' e ?_
  have h1 : Tendsto (fun t : ℝ => 1 / 2 * ∑ i, (t * lam i / ((t * lam i + g) *
      (1 - η / t * (t * lam i + g) / 2))) ^ 2 * (1 - η / t * (t * lam i + g)) ^ (2 * ℓ)) atTop
      (𝓝 (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2 * (1 - η * lam i) ^ (2 * ℓ))) :=
    (tendsto_finsetSum Finset.univ fun i _ =>
      ((ulaScaledStep_factor_tendsto (g := g) (hlam i) (hηl i)).pow 2).mul
        ((rho_scaled_tendsto (lam i) g η).pow (2 * ℓ))).const_mul (1 / 2)
  have h2 : Tendsto (fun t : ℝ => ∑ i, g ^ 2 * wh i ^ 2 * (t * lam i / ((t * lam i + g) *
      (1 - η / t * (t * lam i + g) / 2))) * (t * lam i / (t * lam i + g)) * (1 / (t * lam i + g)) *
      (1 - η / t * (t * lam i + g)) ^ ℓ) atTop (𝓝 (∑ i : Fin d, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => by
      have := ((((tendsto_const_nhds (x := g ^ 2 * wh i ^ 2)).mul
        (ulaScaledStep_factor_tendsto (g := g) (hlam i) (hηl i))).mul
        (ratio_scaled_tendsto (g := g) (hlam i))).mul (inv_p_tendsto (g := g) (hlam i))).mul
        ((rho_scaled_tendsto (lam i) g η).pow ℓ)
      simpa using this
  have h := h1.add h2
  simpa using h

end Scaled

/-! ### The theorem about `ulaLongRunVar` itself -/

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g η : ℝ}

/-- **E5 at the anchored scaling**: with `h = η/t`, `0 < ηλᵢ < 2`, the long-run variance of the
scaled
statistic along the stationary ULA chain on `N(m_t, P_t⁻¹)` tends to `L_η =
    ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)`. -/
theorem ulaAnchored_longRunVar_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.ulaLongRunVar (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ)
      + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c)))) atTop (𝓝 (∑ i, (1 + (1 - η * lam
      i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3))) := by
  refine (ulaScaledStep_longRunVar_tendsto hlam hη hηl hg (affineFrame Q c w₀)).congr' ?_
  have hev : ∀ᶠ t : ℝ in atTop, ∀ i, η / t * (t * lam i + g) < 2 :=
    Filter.eventually_all.2 fun i => (scaledStep_eventually (g := g) (hηl i)).mono fun _ h => h.1
  filter_upwards [eventually_gt_atTop (0 : ℝ), hev] with t ht hev
  rw [ulaAnchored_longRunVar hlam hQ c w₀ hg ht (div_pos hη ht) hev]

end Multi

end Laplace.Multi
