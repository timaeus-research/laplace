/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ULAErrorBudget

/-!
# The fluctuation of the ULA-sampled anchored estimate and the stationary budget (E4/E5)

The expectation-bias budget of `ULAErrorBudget` is completed by the fluctuation of a single sampled
statistic and by its stationary limit. For ULA on `N(m, P⁻¹)` from `x₀`, with `vᵢ = fᵢ/(pᵢκᵢ)` the
burn-in
variances and `μᵢ = (Uᵀm)ᵢ + ρᵢ^k(Uᵀ(x₀ − m))ᵢ` the frame coordinates of the mean after `k` steps,
**`Var_k(½uᵀHu) = ½∑ᵢ(λᵢvᵢ)² + ∑ᵢvᵢ(λᵢμᵢ)²`** (`burnInAnch_var_frame`, from `tiltedVar_quadForm`),
hence
`Var_k(t·½uᵀHu) = (t²/2)∑ᵢ(λᵢvᵢ)² + t²∑ᵢvᵢ(λᵢμᵢ)²` in the E2 frame (`ulaAnchored_llc_var`). As `k →
∞` at
fixed `t`, `h`: the energy tends to `(t/2)∑λᵢ/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²`, the transient to `0` and the
variance to
`(t²/2)∑(λᵢ/(pᵢκᵢ))² + t²∑λᵢ²bᵢ²/(pᵢκᵢ)` (`ulaAnchored_energy_tendsto`, `ulaAnchored_burn_tendsto`,
`ulaAnchored_var_tendsto`), and the budget becomes the stationary statement
**`t⟨L∘A⟩_loc − ((t/2)∑λᵢ/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²) = C₁′/t − (th/4)∑λᵢ/κᵢ + O(t⁻²)`**
(`ulaAnchored_llc_budget_stationary`): at stationarity the ULA anchored estimate exceeds the exact
localised
LLC by the step-size bias minus the anharmonic correction.
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

theorem transpose_mul_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam) :
    Uᵀ * H = diagonal lam * Uᵀ := by
  have hU' := mul_transpose_eq_one_of hU
  calc Uᵀ * H = Uᵀ * H * (U * Uᵀ) := by rw [hU', Matrix.mul_one]
    _ = (Uᵀ * H * U) * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = diagonal lam * Uᵀ := by rw [hdiag]

theorem transpose_mulVec_mulVec_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam)
    (x : ι → ℝ) : Uᵀ *ᵥ (H *ᵥ x) = diagonal lam *ᵥ (Uᵀ *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, transpose_mul_frame hU hdiag, ← Matrix.mulVec_mulVec]

theorem burnInAnch_trace_sq_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0
    < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) {k :
        ℕ}
    (hk : 1 ≤ k) :
    ∑ a, ∑ c, (H * (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹) a c * (H * (ulaCov P h * (1 -
        ulaStep P h ^ (2 * k)))⁻¹⁻¹) c a = ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 -
            h * p i) ^ (2 * k)))) ^ 2 := by
  have e : ∑ a, ∑ c, (H * (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹) a c * (H * (ulaCov P h *
      (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹) c a =
      Matrix.trace ((H * (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹) * (H * (ulaCov P h * (1 -
          ulaStep P h ^ (2 * k)))⁻¹⁻¹)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [e, burnInCov_inv_inv_frame hU hdiag hp hh hev hk, frame_eq_conj hU hdiagH,
      conj_mul_conj_frame hU,
    conj_mul_conj_frame hU, Matrix.trace_mul_cycle, hU, Matrix.one_mul, diagonal_mul_diagonal,
    diagonal_mul_diagonal, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem burnInAnch_cross_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p
    i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) {k : ℕ}
    (hk : 1 ≤ k) (m x₀ : ι → ℝ) :
    (H *ᵥ burnInMeanAnch P h k m x₀) ⬝ᵥ (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹ *ᵥ (H *ᵥ
        burnInMeanAnch P h k m x₀) =
      ∑ i, (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 * k))) * (lam i * ((Uᵀ *ᵥ m) i
          + (1 - h * p i) ^ k * (Uᵀ *ᵥ (x₀ - m)) i)) ^ 2 := by
  rw [burnInCov_inv_inv_frame hU hdiag hp hh hev hk, dotProduct_conj_diagonal_mulVec]
  simp only [transpose_mulVec_mulVec_frame hU hdiagH, Matrix.mulVec_diagonal,
    transpose_mulVec_burnInMeanAnch hU hdiag]

/-- **The variance of the sampled quadratic statistic after `k` ULA steps** on `N(m, P⁻¹)` from
`x₀`,
for `H` in the same frame: `Var_k(½uᵀHu) = ½∑ᵢ(λᵢvᵢ)² + ∑ᵢvᵢ(λᵢμᵢ)²`. -/
theorem burnInAnch_var_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p
    i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 < lam i) {k : ℕ} (hk : 1 ≤ k) (m x₀ : ι → ℝ) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTiltAnch P h k m x₀) (fun
        u => ((1 / 2) * (u ⬝ᵥ H *ᵥ u)) ^ 2) -
      (tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTiltAnch P h k m x₀)
          (fun u => (1 / 2) * (u ⬝ᵥ H *ᵥ u))) ^ 2 =
      1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 * k)))) ^ 2 +
          ∑ i, (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 * k))) * (lam i * ((Uᵀ *ᵥ
              m) i + (1 - h * p i) ^ k * (Uᵀ *ᵥ (x₀ - m)) i)) ^ 2 := by
  have hQ := burnInCov_inv_posDef_frame hU hdiag hp hh hev hk
  have hH : H.IsHermitian := (posDef_frame hU hdiagH hlam).1
  have e1 : (fun u : ι → ℝ => ((1 / 2 : ℝ) * (u ⬝ᵥ H *ᵥ u)) ^ 2) =
      fun u => (1 / 4 : ℝ) * (u ⬝ᵥ H *ᵥ u) ^ 2 := by
    funext u
    ring
  unfold burnInTiltAnch
  rw [e1, tiltedExpectation_const_mul, tiltedExpectation_const_mul]
  have hvar := tiltedVar_quadForm hQ ((ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ *ᵥ
      burnInMeanAnch P h k m x₀) hH
  rw [tiltMean_mulVec_self hQ, burnInAnch_trace_sq_frame hU hdiag hp hh hev hdiagH hk,
    burnInAnch_cross_frame hU hdiag hp hh hev hdiagH hk m x₀] at hvar
  linear_combination (1 / 4 : ℝ) * hvar

end Frame

end Laplace.Sampler

namespace Laplace.Multi

/-! ### Stationary limits at fixed `t`, `h` -/

theorem rho_pow_tendsto_of_stable {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (hev : h * p < 2) :
    Tendsto (fun k : ℕ => (1 - h * p) ^ k) atTop (𝓝 0) := by
  refine tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_
  have := mul_pos hh hp
  rw [abs_lt]
  constructor <;> linarith

theorem rho_pow_two_mul_tendsto {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (hev : h * p < 2) :
    Tendsto (fun k : ℕ => (1 - h * p) ^ (2 * k)) atTop (𝓝 0) := by
  have habs : |1 - h * p| < 1 := by
    have := mul_pos hh hp
    rw [abs_lt]
    constructor <;> linarith
  have hsq : |(1 - h * p) ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg (1 - h * p)]
  simp_rw [pow_mul]
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hsq

section Limits

variable {d : ℕ} (t : ℝ) (lam p b z : Fin d → ℝ) {h : ℝ} (hh : 0 < h) (hp : ∀ i, 0 < p i)
  (hev : ∀ i, h * p i < 2)
include hh hp hev

/-- The `k`-step ULA anchored energy tends to its stationary value `(t/2)∑λᵢ/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²`.
-/
theorem ulaAnchored_energy_tendsto :
    Tendsto (fun k : ℕ => t / 2 * ∑ i, lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i)
        ^ (2 * k))) +
        t / 2 * ∑ i, lam i * (b i + (1 - h * p i) ^ k * (z i - b i)) ^ 2) atTop
      (𝓝 (t / 2 * ∑ i, lam i * (1 / (p i * (1 - h * p i / 2))) + t / 2 * ∑ i, lam i * b i ^ 2)) :=
          by
  have h1 : ∀ i, Tendsto (fun k : ℕ => lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i)
      ^ (2 * k))))
      atTop (𝓝 (lam i * (1 / (p i * (1 - h * p i / 2))))) := fun i => by
    have := rho_pow_two_mul_tendsto hh (hp i) (hev i)
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub this).const_mul
      (1 / (p i * (1 - h * p i / 2)))).const_mul (lam i)
  have h2 : ∀ i, Tendsto (fun k : ℕ => lam i * (b i + (1 - h * p i) ^ k * (z i - b i)) ^ 2) atTop
      (𝓝 (lam i * b i ^ 2)) := fun i => by
    have := rho_pow_tendsto_of_stable hh (hp i) (hev i)
    simpa using (((tendsto_const_nhds (x := b i)).add (this.mul_const (z i - b i))).pow
        2).const_mul (lam i)
  simpa using ((tendsto_finsetSum Finset.univ fun i _ => h1 i).const_mul (t / 2)).add
    ((tendsto_finsetSum Finset.univ fun i _ => h2 i).const_mul (t / 2))

/-- The burn-in transient vanishes as `k → ∞`. -/
theorem ulaAnchored_burn_tendsto :
    Tendsto (fun k : ℕ => t / 2 * ∑ i, lam i * (1 - h * p i) ^ (2 * k) / (p i * (1 - h * p i / 2)) -
        t / 2 * ∑ i, lam i * ((b i + (1 - h * p i) ^ k * (z i - b i)) ^ 2 - b i ^ 2)) atTop (𝓝 0)
            := by
  have h1 : ∀ i, Tendsto (fun k : ℕ => lam i * (1 - h * p i) ^ (2 * k) / (p i * (1 - h * p i / 2)))
      atTop
      (𝓝 0) := fun i => by
    have := rho_pow_two_mul_tendsto hh (hp i) (hev i)
    simpa using (this.const_mul (lam i)).div_const (p i * (1 - h * p i / 2))
  have h2 : ∀ i, Tendsto (fun k : ℕ => lam i * ((b i + (1 - h * p i) ^ k * (z i - b i)) ^ 2 - b i ^
      2))
      atTop (𝓝 0) := fun i => by
    have := rho_pow_tendsto_of_stable hh (hp i) (hev i)
    have h' := ((((tendsto_const_nhds (x := b i)).add (this.mul_const (z i - b i))).pow 2).sub
      (tendsto_const_nhds (x := b i ^ 2))).const_mul (lam i)
    have e0 : lam i * ((b i + 0 * (z i - b i)) ^ 2 - b i ^ 2) = 0 := by ring
    rw [e0] at h'
    exact h'
  simpa using ((tendsto_finsetSum Finset.univ fun i _ => h1 i).const_mul (t / 2)).sub
    ((tendsto_finsetSum Finset.univ fun i _ => h2 i).const_mul (t / 2))

/-- The variance of the sampled statistic tends to its stationary value
`(t²/2)∑(λᵢ/(pᵢκᵢ))² + t²∑λᵢ²bᵢ²/(pᵢκᵢ)`. -/
theorem ulaAnchored_var_tendsto :
    Tendsto (fun k : ℕ => t ^ 2 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h *
        p i) ^ (2 * k)))) ^ 2 +
        t ^ 2 * ∑ i, (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 * k))) *
          (lam i * (b i + (1 - h * p i) ^ k * (z i - b i))) ^ 2) atTop
      (𝓝 (t ^ 2 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 +
        t ^ 2 * ∑ i, (1 / (p i * (1 - h * p i / 2))) * (lam i * b i) ^ 2)) := by
  have hv : ∀ i, Tendsto (fun k : ℕ => 1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 *
      k))) atTop
      (𝓝 (1 / (p i * (1 - h * p i / 2)))) := fun i => by
    have := rho_pow_two_mul_tendsto hh (hp i) (hev i)
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub this).const_mul (1 / (p i * (1 - h * p i /
        2)))
  have hμ : ∀ i, Tendsto (fun k : ℕ => lam i * (b i + (1 - h * p i) ^ k * (z i - b i))) atTop
      (𝓝 (lam i * b i)) := fun i => by
    have := rho_pow_tendsto_of_stable hh (hp i) (hev i)
    simpa using ((tendsto_const_nhds (x := b i)).add (this.mul_const (z i - b i))).const_mul (lam i)
  have h1 : ∀ i, Tendsto (fun k : ℕ => (lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i)
      ^ (2 * k)))) ^ 2)
      atTop (𝓝 ((lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2)) := fun i => ((hv i).const_mul (lam
          i)).pow 2
  have h2 : ∀ i, Tendsto (fun k : ℕ => (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 *
      k))) *
      (lam i * (b i + (1 - h * p i) ^ k * (z i - b i))) ^ 2) atTop
      (𝓝 ((1 / (p i * (1 - h * p i / 2))) * (lam i * b i) ^ 2)) := fun i => (hv i).mul ((hμ i).pow
          2)
  exact ((tendsto_finsetSum Finset.univ fun i _ => h1 i).const_mul (t ^ 2 / 2)).add
    ((tendsto_finsetSum Finset.univ fun i _ => h2 i).const_mul (t ^ 2))

end Limits

/-! ### The β-scaled step: the single-sample fluctuation stays `O(1)` -/

/-- Per mode, `tλ/(pκ) → 1/(1 − ηλ/2)` with `h = η/t`. -/
theorem ulaScaledStep_factor_tendsto {lam g η : ℝ} (hlam : 0 < lam) (hηl : η * lam < 2) :
    Tendsto (fun t : ℝ => t * lam / ((t * lam + g) * (1 - η / t * (t * lam + g) / 2))) atTop
      (𝓝 (1 / (1 - η * lam / 2))) := by
  have hc : 0 < 1 - η * lam / 2 := by linarith
  have e : (fun t : ℝ => lam / ((lam + g / t) * (1 - (η * lam + η * g / t) / 2))) =ᶠ[atTop]
      fun t => t * lam / ((t * lam + g) * (1 - η / t * (t * lam + g) / 2)) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp
  have hz : Tendsto (fun t : ℝ => g / t) atTop (𝓝 0) := (tendsto_const_nhds (x := g)).div_atTop
      tendsto_id
  have hz' : Tendsto (fun t : ℝ => η * g / t) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := η * g)).div_atTop tendsto_id
  have hden : Tendsto (fun t : ℝ => (lam + g / t) * (1 - (η * lam + η * g / t) / 2)) atTop
      (𝓝 (lam * (1 - η * lam / 2))) := by
    simpa using ((tendsto_const_nhds (x := lam)).add hz).mul
      ((((tendsto_const_nhds (x := η * lam)).add hz').div_const 2).const_sub 1)
  have hne : lam * (1 - η * lam / 2) ≠ 0 := by positivity
  have h := (tendsto_const_nhds (x := lam)).div hden hne
  have e2 : lam / (lam * (1 - η * lam / 2)) = 1 / (1 - η * lam / 2) := by
    have := hlam.ne'
    have := hc.ne'
    field_simp
  rw [e2] at h
  exact h.congr' e

/-- **The stationary fluctuation of one β-scaled ULA sample is `O(1)`**: the main variance piece
`(t²/2)∑ᵢ(λᵢ/(pᵢκᵢ))²` tends to `½∑ᵢ1/(1 − ηλᵢ/2)²` (≈ `d/2` for small `η`); the anchor piece is
`O(1/t)`
(prose). -/
theorem ulaScaledStep_var_main_tendsto {d : ℕ} {lam : Fin d → ℝ} {g η : ℝ} (hlam : ∀ i, 0 < lam i)
    (hηl : ∀ i, η * lam i < 2) :
    Tendsto (fun t : ℝ => t ^ 2 / 2 *
        ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) ^ 2) atTop
      (𝓝 (1 / 2 * ∑ i, (1 / (1 - η * lam i / 2)) ^ 2)) := by
  have e : (fun t : ℝ => t ^ 2 / 2 *
      ∑ i, (lam i * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) ^ 2) =
      fun t => 1 / 2 * ∑ i, (t * lam i / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) ^ 2
          := by
    funext t
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact (tendsto_finsetSum Finset.univ fun i _ =>
    (ulaScaledStep_factor_tendsto (hlam i) (hηl i)).pow 2).const_mul (1 / 2)

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- **The variance of the ULA-sampled anchored LLC statistic** after `k` steps, in the E2 frame:
`Var_k(t·½uᵀHu) = (t²/2)∑ᵢ(λᵢvᵢ)² + t²∑ᵢvᵢ(λᵢ(bᵢ + ρᵢ^k(zᵢ − bᵢ)))²`. -/
theorem ulaAnchored_llc_var (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤
    g)
    {t : ℝ} (ht : 0 < t) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * (t * lam i + g) < 2) {k : ℕ} (hk : 1
        ≤ k)
    (x₀ : Fin d → ℝ) :
    t ^ 2 * (tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ) + g • (1 :
      Matrix (Fin d) (Fin d) ℝ)) h * (1 - Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) h ^ (2 * k)))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) h k ((t • (Q * diagonal lam * Qᵀ) + g
      • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => ((1 / 2) * (u ⬝ᵥ (Q *
      diagonal lam * Qᵀ) *ᵥ u)) ^ 2) - (tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal
      lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) h * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) h ^ (2 * k)))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) h k ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ -
      c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u))) ^ 2) = t ^ 2 / 2 * ∑ i,
      (lam i * (1 / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) * (1 - (1 - h * (t * lam i +
      g)) ^ (2 * k)))) ^ 2 + t ^ 2 * ∑ i, (1 / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) *
      (1 - (1 - h * (t * lam i + g)) ^ (2 * k))) * (lam i * (g * affineFrame Q c w₀ i / (t * lam i +
      g) + (1 - h * (t * lam i + g)) ^ k * ((Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t * lam i +
      g)))) ^ 2 := by
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have hdiagP := transpose_localisedPrecision_conj (lam := lam) hQ t g
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  have hV := Laplace.Sampler.burnInAnch_var_frame hQ hdiagP hp hh hev hdiagH hlam hk ((t • (Q *
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
  rw [hV]
  ring

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The stationary error budget**: at `k = ∞` the ULA anchored estimate `(t/2)∑λᵢ/(pᵢκᵢ) +
(t/2)∑λᵢbᵢ²`
exceeds the exact localised LLC by the step-size bias minus the anharmonic correction,
`t⟨L∘A⟩_loc − stationary = C₁′/t − (th/4)∑ᵢλᵢ/κᵢ + O(t⁻²)`. -/
theorem ulaAnchored_llc_budget_stationary (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → ∀ {h : ℝ}, 0 < h → (∀ i, h * (t * lam i + g) < 2)
        →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) - (t / 2 * ∑ i, lam i * (1 / ((t * lam i + g) * (1 -
        h * (t * lam i + g) / 2))) + t / 2 * ∑ i, lam i * (g * affineFrame Q c w₀ i / (t * lam i +
        g)) ^ 2) - (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g /
        (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t + t * h / 4 * ∑ i, lam i /
        (1 - h * (t * lam i + g) / 2)| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ :=
    localisedEnergy_anchoredGap (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀ hg
  refine ⟨K₁, T₁, hK₁, hT₁, fun {t} ht {h} hh hev => ?_⟩
  have ht0 : 0 < t := by linarith
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  have hκ : ∀ i, (1 - h * (t * lam i + g) / 2) ≠ 0 := fun i => by have := hev i; intro h0; linarith
  have e₁ := h₁ ht
  have key : (t / 2 * ∑ i, lam i * (1 / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2))) + t / 2 *
      ∑ i, lam i * (g * affineFrame Q c w₀ i / (t * lam i + g)) ^ 2) - t * h / 4 * ∑ i, lam i / (1 -
      h * (t * lam i + g) / 2) = 1 / 2 * ∑ i, t * lam i / (t * lam i + g) + t / 2 * ∑ i, lam i * ((g
      * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    set pp := t * lam i + g with hpp
    have hpp0 : pp ≠ 0 := (hp i).ne'
    have hκ' : 1 - h * pp / 2 ≠ 0 := hκ i
    have h2 : 2 - h * pp ≠ 0 := by
      have := hev i
      rw [← hpp] at this
      intro h0
      linarith
    have h2' : 2 - pp * h ≠ 0 := by
      rw [mul_comm]
      exact h2
    field_simp
    ring
  have e : t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) - (t / 2 * ∑ i, lam i * (1 / ((t * lam i + g) * (1 - h
      * (t * lam i + g) / 2))) + t / 2 * ∑ i, lam i * (g * affineFrame Q c w₀ i / (t * lam i + g)) ^
      2) - (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 *
      lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t + t * h / 4 * ∑ i, lam i / (1 - h
      * (t * lam i + g) / 2) = t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma
      g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma) - (1 / 2 * ∑ i, t * lam i / (t * lam i + g)
      + t / 2 * ∑ i, lam i * ((g * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2) - (∑ i,
      (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g *
      affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t := by
    rw [← key]
    ring
  rw [e]
  exact e₁

end Multi

end Laplace.Multi
