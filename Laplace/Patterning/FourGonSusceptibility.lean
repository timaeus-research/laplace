/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.FourGon
import Laplace.Patterning.FourGonGibbs
import Laplace.Patterning.FourGonStationary

/-!
# Susceptibilities at the degenerate 4-gon

At the exact 4-gon every per-feature gradient vanishes, so every checkpoint-frozen rule gives zero
force. The patterning pipeline nevertheless moves the dead unit, because the susceptibility of the
dead component under the restricted Gibbs law `∝ e^{-t r⁴/15}` is not zero. This file computes that
susceptibility matrix exactly.

The observables are the dead unit's norm `‖W₄‖`, its projections `d_α = ⟨(cos α, sin α), W₄⟩` on
the feature directions, and the restricted excess loss `K = r⁴/15`; the perturbations are the
per-feature excess losses `ℓᵢ − ℓᵢ(4-gon)`, which are `⅓[⟨e_{θᵢ}, W₄⟩]₊²` for the alive features
(`θᵢ = 0, π/2, π, 3π/2`) and `⅓(r⁴ − r²)` for the dead one. With `χ(φ; hᵢ) = −(t/5) Cov_t(φ, ℓᵢ)`:

* **Direction rows** (`radialCov_dirObs_plusLoss`): for *every* rotationally symmetric law with
  density `G(‖z‖²)`, `Cov(d_α, ℓ_β) = (2/9π) cos(α − β) E[r³]`; so `χ(d_j; h_j) = −c`,
  `χ(d_j; h_{j+2}) = +c`, and `0` for the orthogonal features and for the dead one
  (`deadChi_dir_same`, `deadChi_dir_opposite`, `deadChi_dir_orth`, `deadChi_dir_dead`), with
  `c = (t/5)(2/9π) E_t[r³] > 0`: upweighting a feature pushes the dead unit away from it.
* The angular factor `∫ cos(θ − α)[cos(θ − β)]₊² dθ = (4/3) cos(α − β)` is the whole content; the
  radial law enters only through `E[r³]`, which is why an isotropic Gaussian ensemble reproduces
  the direction rows exactly up to the ratio of third moments (the note's symmetry observation).

The norm and excess-loss rows, which do depend on the radial law, are in
`FourGonSusceptibilityRadial.lean`.
-/

namespace Laplace.Patterning

open Real MeasureTheory Set Laplace.TwoD intervalIntegral

noncomputable section

/-! ### Polar coordinates for separable integrands -/

/-- **Separable integrands in polar coordinates.** If `r f(r cos θ, r sin θ) = R(r) Θ(θ)` then
`∫_{ℝ²} f = (∫₀^∞ R)(∫_{-π}^{π} Θ)`. -/
theorem integral_polar_sep (f : ℝ × ℝ → ℝ) (R Θ : ℝ → ℝ)
    (hf : ∀ r, 0 < r → ∀ θ, θ ∈ Ioo (-π) π → r * f (r * cos θ, r * sin θ) = R r * Θ θ) :
    ∫ z : ℝ × ℝ, f z = (∫ r in Ioi (0 : ℝ), R r) * ∫ θ in (-π)..π, Θ θ := by
  rw [← integral_comp_polarCoord_symm]
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have hcongr : ∀ p ∈ polarCoord.target, p.1 • f (polarCoord.symm p) = R p.1 * Θ p.2 := by
    intro p hp
    rw [htarget] at hp
    change p.1 * f (p.1 * cos p.2, p.1 * sin p.2) = R p.1 * Θ p.2
    exact hf p.1 hp.1 p.2 hp.2
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr, htarget,
    Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_mul,
    intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo]

/-! ### Rotationally symmetric laws and their radial moments -/

/-- The polar-weighted radial moment `∫₀^∞ r^(k+1) G(r²) dr` of the weight `z ↦ G(‖z‖²)`. -/
def polarMoment (G : ℝ → ℝ) (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ (k + 1) * G (r ^ 2)

/-- The normalised expectation of `φ` under the rotationally symmetric weight `z ↦ G(‖z‖²)`. -/
def radialExpectation (G : ℝ → ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  (∫ z : ℝ × ℝ, φ z * G (z.1 ^ 2 + z.2 ^ 2)) / ∫ z : ℝ × ℝ, G (z.1 ^ 2 + z.2 ^ 2)

/-- The covariance under the rotationally symmetric weight `z ↦ G(‖z‖²)`. -/
def radialCov (G : ℝ → ℝ) (φ ψ : ℝ × ℝ → ℝ) : ℝ :=
  radialExpectation G (fun z => φ z * ψ z) - radialExpectation G φ * radialExpectation G ψ

/-- The dead unit's norm `‖W₄‖ = r`. -/
def normObs (z : ℝ × ℝ) : ℝ := √(z.1 ^ 2 + z.2 ^ 2)

/-- The projection of the dead unit on the direction `(cos α, sin α)`. -/
def dirObs (α : ℝ) (z : ℝ × ℝ) : ℝ := cos α * z.1 + sin α * z.2

/-- The excess loss of an alive feature at angle `β`: `⅓ [⟨e_β, W₄⟩]₊²`. -/
def plusLoss (β : ℝ) (z : ℝ × ℝ) : ℝ := (1 / 3) * relu (cos β * z.1 + sin β * z.2) ^ 2

/-- The excess loss of the dead feature: `⅓ (r⁴ − r²)`. -/
def deadLoss (z : ℝ × ℝ) : ℝ := (1 / 3) * ((z.1 ^ 2 + z.2 ^ 2) ^ 2 - (z.1 ^ 2 + z.2 ^ 2))

theorem polar_sq (r θ : ℝ) : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
  have := sin_sq_add_cos_sq θ
  linear_combination r ^ 2 * this

theorem normObs_polar {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : normObs (r * cos θ, r * sin θ) = r := by
  simp only [normObs, polar_sq]
  exact Real.sqrt_sq hr

theorem dirObs_polar (α r θ : ℝ) : dirObs α (r * cos θ, r * sin θ) = r * cos (θ - α) := by
  simp only [dirObs, cos_sub]
  ring

theorem plusLoss_polar (β : ℝ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    plusLoss β (r * cos θ, r * sin θ) = (1 / 3) * r ^ 2 * relu (cos (θ - β)) ^ 2 := by
  have h : cos β * (r * cos θ) + sin β * (r * sin θ) = r * cos (θ - β) := by
    rw [cos_sub]
    ring
  simp only [plusLoss, h, relu_mul_of_nonneg hr]
  ring

theorem deadLoss_polar (r θ : ℝ) : deadLoss (r * cos θ, r * sin θ) = (1 / 3) * (r ^ 4 - r ^ 2) := by
  simp only [deadLoss, polar_sq]
  ring

/-- The normalisation `∫ G(‖z‖²) = 2π ∫₀^∞ r G(r²) dr`. -/
theorem integral_radial_weight (G : ℝ → ℝ) :
    ∫ z : ℝ × ℝ, G (z.1 ^ 2 + z.2 ^ 2) = polarMoment G 0 * (2 * π) := by
  rw [integral_polar_sep (fun z => G (z.1 ^ 2 + z.2 ^ 2)) (fun r => r * G (r ^ 2)) (fun _ => 1)
    (fun r _ θ _ => by simp only [polar_sq]; ring), intervalIntegral.integral_const,
    sub_neg_eq_add, smul_eq_mul, mul_one]
  simp only [polarMoment, zero_add, pow_one]
  ring

/-- `E[r^k] = m_k / m_0` in terms of the polar moments. -/
theorem radialExpectation_normObs_pow (G : ℝ → ℝ) (k : ℕ) :
    radialExpectation G (fun z => normObs z ^ k) = polarMoment G k / polarMoment G 0 := by
  unfold radialExpectation
  rw [integral_radial_weight, integral_polar_sep (fun z => normObs z ^ k * G (z.1 ^ 2 + z.2 ^ 2))
    (fun r => r ^ (k + 1) * G (r ^ 2)) (fun _ => 1)
    (fun r hr θ _ => by rw [normObs_polar hr.le, polar_sq]; ring)]
  rw [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul, mul_one,
    show π + π = 2 * π by ring, show polarMoment G k = ∫ r in Ioi (0 : ℝ), r ^ (k + 1) * G (r ^ 2)
      from rfl]
  exact mul_div_mul_right _ _ (by positivity)

/-! ### Angular integrals -/

theorem integral_cos_sub_eq_zero (α : ℝ) : ∫ θ in (-π)..π, cos (θ - α) = 0 := by
  rw [intervalIntegral.integral_comp_sub_right (fun θ => cos θ) α, integral_cos]
  have : -π - α = (π - α) - 2 * π := by ring
  rw [this, sin_periodic.sub_eq (π - α), sub_self]

/-- `[cos θ]₊ = 0` on `[-π, -π/2]` and `[π/2, π]`, `= cos θ` on `[-π/2, π/2]`. -/
theorem relu_cos_of_mem_left {θ : ℝ} (h : θ ∈ uIcc (-π) (-(π / 2))) : relu (cos θ) = 0 := by
  rw [uIcc_of_le (by linarith [pi_pos])] at h
  refine relu_of_nonpos ?_
  rw [← cos_neg]
  exact cos_nonpos_of_pi_div_two_le_of_le (by linarith [h.2]) (by linarith [h.1, pi_pos])

theorem relu_cos_of_mem_right {θ : ℝ} (h : θ ∈ uIcc (π / 2) π) : relu (cos θ) = 0 := by
  rw [uIcc_of_le (by linarith [pi_pos])] at h
  exact relu_of_nonpos (cos_nonpos_of_pi_div_two_le_of_le h.1 (by linarith [h.2, pi_pos]))

theorem relu_cos_of_mem_mid {θ : ℝ} (h : θ ∈ uIcc (-(π / 2)) (π / 2)) : relu (cos θ) = cos θ := by
  rw [uIcc_of_le (by linarith [pi_pos])] at h
  exact relu_of_nonneg (cos_nonneg_of_neg_pi_div_two_le_of_le h.1 h.2)

theorem continuous_relu : Continuous relu := continuous_id.max continuous_const

/-- Splitting `∫_{-π}^{π}` at `±π/2` for an integrand that vanishes where `cos θ ≤ 0`. -/
theorem integral_split_relu_cos (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ θ in (-π)..π, g θ * relu (cos θ) ^ 2 = ∫ θ in (-(π / 2))..(π / 2), g θ * cos θ ^ 2 := by
  have hc : Continuous fun θ => g θ * relu (cos θ) ^ 2 :=
    hg.mul ((continuous_relu.comp continuous_cos).pow 2)
  rw [← integral_add_adjacent_intervals (hc.intervalIntegrable (-π) (-(π / 2)))
    (hc.intervalIntegrable (-(π / 2)) π),
    ← integral_add_adjacent_intervals (hc.intervalIntegrable (-(π / 2)) (π / 2))
    (hc.intervalIntegrable (π / 2) π)]
  have h1 : ∫ θ in (-π)..(-(π / 2)), g θ * relu (cos θ) ^ 2 = 0 := by
    have : ∫ θ in (-π)..(-(π / 2)), g θ * relu (cos θ) ^ 2 = ∫ θ in (-π)..(-(π / 2)), (0 : ℝ) :=
      integral_congr fun θ hθ => by simp [relu_cos_of_mem_left hθ]
    rw [this, intervalIntegral.integral_zero]
  have h3 : ∫ θ in (π / 2)..π, g θ * relu (cos θ) ^ 2 = 0 := by
    have : ∫ θ in (π / 2)..π, g θ * relu (cos θ) ^ 2 = ∫ θ in (π / 2)..π, (0 : ℝ) :=
      integral_congr fun θ hθ => by simp [relu_cos_of_mem_right hθ]
    rw [this, intervalIntegral.integral_zero]
  have h2 : ∫ θ in (-(π / 2))..(π / 2), g θ * relu (cos θ) ^ 2
      = ∫ θ in (-(π / 2))..(π / 2), g θ * cos θ ^ 2 :=
    integral_congr fun θ hθ => by rw [relu_cos_of_mem_mid hθ]
  rw [h1, h2, h3]
  ring

/-- `∫_{-π}^{π} [cos θ]₊² dθ = π/2`. -/
theorem integral_relu_cos_sq : ∫ θ in (-π)..π, relu (cos θ) ^ 2 = π / 2 := by
  have := integral_split_relu_cos (fun _ => 1) continuous_const
  simp only [one_mul] at this
  rw [this, integral_cos_sq, cos_neg, sin_neg, cos_pi_div_two, sin_pi_div_two]
  ring

/-- `∫_{-π}^{π} cos θ [cos θ]₊² dθ = 4/3`. -/
theorem integral_cos_mul_relu_cos_sq : ∫ θ in (-π)..π, cos θ * relu (cos θ) ^ 2 = 4 / 3 := by
  rw [integral_split_relu_cos cos continuous_cos]
  have : ∫ θ in (-(π / 2))..(π / 2), cos θ * cos θ ^ 2 = ∫ θ in (-(π / 2))..(π / 2), cos θ ^ 3 :=
    integral_congr fun θ _ => by ring
  rw [this, integral_cos_pow_three, sin_neg, sin_pi_div_two]
  norm_num

/-- `∫_{-π}^{π} sin θ [cos θ]₊² dθ = 0` (odd integrand). -/
theorem integral_sin_mul_relu_cos_sq : ∫ θ in (-π)..π, sin θ * relu (cos θ) ^ 2 = 0 := by
  have h := intervalIntegral.integral_comp_neg (fun θ => sin θ * relu (cos θ) ^ 2)
    (a := -π) (b := π)
  simp only [neg_neg, sin_neg, cos_neg, neg_mul] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- Shifting the angle: `∫_{-π}^{π} g(θ − β) = ∫_{-π}^{π} g` for `2π`-periodic `g`. -/
theorem integral_periodic_shift (g : ℝ → ℝ) (hg : Function.Periodic g (2 * π)) (β : ℝ) :
    ∫ θ in (-π)..π, g (θ - β) = ∫ θ in (-π)..π, g θ := by
  rw [intervalIntegral.integral_comp_sub_right g β]
  have h := Function.Periodic.intervalIntegral_add_eq hg (-π - β) (-π)
  rw [show -π - β + 2 * π = π - β by ring, show -π + 2 * π = π by ring] at h
  exact h

/-- **The angular factor of the direction rows**:
`∫_{-π}^{π} cos(θ − α) [cos(θ − β)]₊² dθ = (4/3) cos(α − β)`. -/
theorem integral_cos_sub_mul_relu_cos_sub_sq (α β : ℝ) :
    ∫ θ in (-π)..π, cos (θ - α) * relu (cos (θ - β)) ^ 2 = 4 / 3 * cos (α - β) := by
  have hper : Function.Periodic (fun φ => cos (φ + (β - α)) * relu (cos φ) ^ 2) (2 * π) := by
    intro φ
    simp only
    rw [show φ + 2 * π + (β - α) = (φ + (β - α)) + 2 * π by ring, cos_periodic (φ + (β - α)),
      cos_periodic φ]
  have hshift := integral_periodic_shift _ hper β
  have hfun : (fun θ => cos (θ - α) * relu (cos (θ - β)) ^ 2)
      = fun θ => (fun φ => cos (φ + (β - α)) * relu (cos φ) ^ 2) (θ - β) := by
    funext θ
    simp only
    rw [show θ - β + (β - α) = θ - α by ring]
  rw [hfun, hshift]
  have hc : Continuous fun φ => cos φ * relu (cos φ) ^ 2 :=
    continuous_cos.mul ((continuous_relu.comp continuous_cos).pow 2)
  have hs : Continuous fun φ => sin φ * relu (cos φ) ^ 2 :=
    continuous_sin.mul ((continuous_relu.comp continuous_cos).pow 2)
  have hexp : (fun φ => cos (φ + (β - α)) * relu (cos φ) ^ 2)
      = fun φ => cos (β - α) * (cos φ * relu (cos φ) ^ 2)
        - sin (β - α) * (sin φ * relu (cos φ) ^ 2) := by
    funext φ
    rw [cos_add]
    ring
  have hi1 : IntervalIntegrable (fun φ => cos (β - α) * (cos φ * relu (cos φ) ^ 2)) volume (-π) π :=
    (continuous_const.mul hc).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun φ => sin (β - α) * (sin φ * relu (cos φ) ^ 2)) volume (-π) π :=
    (continuous_const.mul hs).intervalIntegrable _ _
  rw [hexp, integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_mul_relu_cos_sq, integral_sin_mul_relu_cos_sq,
    mul_zero, sub_zero, ← cos_neg (β - α), neg_sub]
  ring

/-! ### The direction rows for every rotationally symmetric law -/

/-- **Direction rows.** For every rotationally symmetric law `G(‖z‖²)`,
`Cov(d_α, ℓ_β) = (2/9π) cos(α − β) E[r³]`. -/
theorem radialCov_dirObs_plusLoss (G : ℝ → ℝ) (α β : ℝ) :
    radialCov G (dirObs α) (plusLoss β)
      = 2 / (9 * π) * cos (α - β) * (polarMoment G 3 / polarMoment G 0) := by
  unfold radialCov radialExpectation
  beta_reduce
  rw [integral_radial_weight]
  rw [integral_polar_sep (fun z => dirObs α z * plusLoss β z * G (z.1 ^ 2 + z.2 ^ 2))
    (fun r => 1 / 3 * (r ^ 4 * G (r ^ 2))) (fun θ => cos (θ - α) * relu (cos (θ - β)) ^ 2)
    (fun r hr θ _ => by rw [dirObs_polar, plusLoss_polar β hr.le, polar_sq]; ring)]
  rw [integral_polar_sep (fun z => dirObs α z * G (z.1 ^ 2 + z.2 ^ 2))
    (fun r => r ^ 2 * G (r ^ 2)) (fun θ => cos (θ - α))
    (fun r _ θ _ => by rw [dirObs_polar, polar_sq]; ring)]
  rw [integral_cos_sub_mul_relu_cos_sub_sq, integral_cos_sub_eq_zero,
    MeasureTheory.integral_const_mul]
  have h3 : ∫ r in Ioi (0 : ℝ), r ^ 4 * G (r ^ 2) = polarMoment G 3 := rfl
  rw [h3, mul_zero, zero_div, zero_mul, sub_zero]
  by_cases hm : polarMoment G 0 = 0
  · simp [hm]
  · field_simp
    ring

/-- Under any rotationally symmetric law the direction row is *antisymmetric under the antipodal
map*: `Cov(d_α, ℓ_{α+π}) = −Cov(d_α, ℓ_α)`, and the orthogonal features do not respond. -/
theorem radialCov_dirObs_plusLoss_add_pi (G : ℝ → ℝ) (α : ℝ) :
    radialCov G (dirObs α) (plusLoss (α + π)) = -radialCov G (dirObs α) (plusLoss α) := by
  rw [radialCov_dirObs_plusLoss, radialCov_dirObs_plusLoss, sub_self, cos_zero,
    show α - (α + π) = -π by ring, cos_neg, cos_pi]
  ring

theorem radialCov_dirObs_plusLoss_add_pi_div_two (G : ℝ → ℝ) (α : ℝ) :
    radialCov G (dirObs α) (plusLoss (α + π / 2)) = 0 := by
  rw [radialCov_dirObs_plusLoss, show α - (α + π / 2) = -(π / 2) by ring, cos_neg, cos_pi_div_two]
  ring

/-! ### The quartic Gibbs law of the dead component -/

/-- The radial weight of the restricted Gibbs law: `e^{-t r⁴/15}` as a function of `r²`. -/
def quarticWeight (t : ℝ) (s : ℝ) : ℝ := exp (-(t / 15) * s ^ 2)

theorem gibbsExpectation_eq_radial (t : ℝ) (φ : ℝ × ℝ → ℝ) :
    Laplace.TwoD.gibbsExpectation deadQuartic t φ = radialExpectation (quarticWeight t) φ := by
  unfold Laplace.TwoD.gibbsExpectation radialExpectation Laplace.TwoD.partitionFunction
    quarticWeight
  simp_rw [exp_neg_deadQuartic]

theorem gibbsCov_eq_radial (t : ℝ) (φ ψ : ℝ × ℝ → ℝ) :
    Laplace.TwoD.gibbsCov deadQuartic t φ ψ = radialCov (quarticWeight t) φ ψ := by
  unfold Laplace.TwoD.gibbsCov radialCov
  rw [gibbsExpectation_eq_radial, gibbsExpectation_eq_radial, gibbsExpectation_eq_radial]

/-- The polar moments of the quartic law: `m_k = (t/15)^{-(k+2)/4} Γ((k+2)/4) / 4`. -/
theorem polarMoment_quartic (t : ℝ) (ht : 0 < t) (k : ℕ) :
    polarMoment (quarticWeight t) k
      = (t / 15) ^ (-((k : ℝ) + 2) / 4) * (1 / 4) * Gamma (((k : ℝ) + 2) / 4) := by
  unfold polarMoment quarticWeight
  have h := integral_Ioi_pow_mul_exp_neg_mul_pow_four (t / 15) (by positivity) (k + 1)
  push_cast at h
  rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [← pow_mul]

theorem polarMoment_quartic_pos (t : ℝ) (ht : 0 < t) (k : ℕ) :
    0 < polarMoment (quarticWeight t) k := by
  rw [polarMoment_quartic t ht]
  have : (0 : ℝ) < ((k : ℝ) + 2) / 4 := by positivity
  exact mul_pos (mul_pos (rpow_pos_of_pos (by positivity) _) (by norm_num)) (Gamma_pos_of_pos this)

/-- `E_t[r³] > 0`. -/
theorem gibbs_normObs_cube_pos (t : ℝ) (ht : 0 < t) :
    0 < Laplace.TwoD.gibbsExpectation deadQuartic t (fun z => normObs z ^ 3) := by
  rw [gibbsExpectation_eq_radial, radialExpectation_normObs_pow]
  exact div_pos (polarMoment_quartic_pos t ht 3) (polarMoment_quartic_pos t ht 0)

/-! ### The susceptibility matrix at the 4-gon -/

/-- The per-feature excess loss with the dead unit at `z`, the other features frozen at the
4-gon. -/
def featureExcess (i : Fin 5) (z : ℝ × ℝ) : ℝ :=
  featureLoss (fourGon z.1 z.2) i - featureLoss (fourGon 0 0) i

/-- **The susceptibility** `χ(φ; hᵢ) = −(t/5) Cov_t(φ, ℓᵢ)` of the observable `φ` of the dead
component to upweighting feature `i`, under the restricted Gibbs law at inverse temperature `t`. -/
def deadChi (t : ℝ) (φ : ℝ × ℝ → ℝ) (i : Fin 5) : ℝ :=
  -(t / 5) * Laplace.TwoD.gibbsCov deadQuartic t φ (featureExcess i)

/-- The feature angles `θⱼ = 0, π/2, π, 3π/2` (the last written as `−π/2`). -/
def featureAngle : Fin 4 → ℝ := ![0, π / 2, π, -(π / 2)]

theorem featureExcess_alive (j : Fin 4) (z : ℝ × ℝ) :
    featureExcess (Fin.castSucc j) z = plusLoss (featureAngle j) z := by
  fin_cases j <;>
    simp [featureExcess, plusLoss, featureAngle, featureLoss_fourGon_0, featureLoss_fourGon_1,
      featureLoss_fourGon_2, featureLoss_fourGon_3, relu_zero]

theorem featureExcess_dead (z : ℝ × ℝ) : featureExcess 4 z = deadLoss z := by
  simp only [featureExcess, deadLoss, featureLoss_fourGon_4]
  ring

/-- The coefficient `c = (t/5)(2/9π) E_t[r³]` of the direction rows. -/
def dirCoeff (t : ℝ) : ℝ :=
  t / 5 * (2 / (9 * π)) * Laplace.TwoD.gibbsExpectation deadQuartic t (fun z => normObs z ^ 3)

theorem dirCoeff_pos (t : ℝ) (ht : 0 < t) : 0 < dirCoeff t :=
  mul_pos (mul_pos (by positivity) (by positivity)) (gibbs_normObs_cube_pos t ht)

/-- **The direction rows of the susceptibility matrix**: `χ(d_α; hⱼ) = −c cos(α − θⱼ)`. -/
theorem deadChi_dirObs_alive (t α : ℝ) (j : Fin 4) :
    deadChi t (dirObs α) (Fin.castSucc j) = -(dirCoeff t * cos (α - featureAngle j)) := by
  unfold deadChi dirCoeff
  rw [show featureExcess (Fin.castSucc j) = plusLoss (featureAngle j) from
    funext (featureExcess_alive j), gibbsCov_eq_radial, radialCov_dirObs_plusLoss,
    gibbsExpectation_eq_radial, radialExpectation_normObs_pow]
  ring

/-- The directions do not respond to the dead feature's own weight: `χ(d_α; h₄) = 0`. -/
theorem deadChi_dirObs_dead (t α : ℝ) : deadChi t (dirObs α) 4 = 0 := by
  unfold deadChi
  rw [show featureExcess 4 = deadLoss from funext featureExcess_dead, gibbsCov_eq_radial]
  unfold radialCov radialExpectation
  beta_reduce
  rw [integral_polar_sep (fun z => dirObs α z * deadLoss z * quarticWeight t (z.1 ^ 2 + z.2 ^ 2))
    (fun r => 1 / 3 * (r ^ 2 * (r ^ 4 - r ^ 2) * quarticWeight t (r ^ 2))) (fun θ => cos (θ - α))
    (fun r _ θ _ => by rw [dirObs_polar, deadLoss_polar, polar_sq]; ring),
    integral_polar_sep (fun z => dirObs α z * quarticWeight t (z.1 ^ 2 + z.2 ^ 2))
    (fun r => r ^ 2 * quarticWeight t (r ^ 2)) (fun θ => cos (θ - α))
    (fun r _ θ _ => by rw [dirObs_polar, polar_sq]; ring), integral_cos_sub_eq_zero]
  simp

/-- **Same feature**: `χ(dⱼ; hⱼ) = −c < 0`. Upweighting a feature pushes the dead unit away from
it. -/
theorem deadChi_dir_same (t : ℝ) (j : Fin 4) :
    deadChi t (dirObs (featureAngle j)) (Fin.castSucc j) = -dirCoeff t := by
  rw [deadChi_dirObs_alive, sub_self, cos_zero, mul_one]

theorem deadChi_dir_same_neg (t : ℝ) (ht : 0 < t) (j : Fin 4) :
    deadChi t (dirObs (featureAngle j)) (Fin.castSucc j) < 0 := by
  rw [deadChi_dir_same]
  exact neg_neg_of_pos (dirCoeff_pos t ht)

/-- **Opposite feature**: `χ(dⱼ; hⱼ₊₂) = +c`. -/
theorem deadChi_dir_opposite (t : ℝ) (j : Fin 4) :
    deadChi t (dirObs (featureAngle j)) (Fin.castSucc (j + 2)) = dirCoeff t := by
  rw [deadChi_dirObs_alive]
  fin_cases j <;>
    simp [featureAngle, cos_sub, cos_add, cos_pi_div_two, sin_pi_div_two, cos_pi, sin_pi]

/-- **Orthogonal features do not respond**: `χ(dⱼ; hⱼ₊₁) = χ(dⱼ; hⱼ₊₃) = 0`. -/
theorem deadChi_dir_orth (t : ℝ) (j : Fin 4) :
    deadChi t (dirObs (featureAngle j)) (Fin.castSucc (j + 1)) = 0 ∧
    deadChi t (dirObs (featureAngle j)) (Fin.castSucc (j + 3)) = 0 := by
  rw [deadChi_dirObs_alive, deadChi_dirObs_alive]
  fin_cases j <;>
    simp [featureAngle, cos_sub, cos_add, cos_pi_div_two, sin_pi_div_two, cos_pi, sin_pi]

/-- **Part (i) restated as a force statement**: the checkpoint-frozen reweighting force vanishes
at the 4-gon for every reweighting `ω` and every direction `V`. -/
theorem frozenForce_fourGon_eq_zero (ω : Fin 5 → ℝ) (V : Fin 5 → Fin 2 → ℝ) :
    HasDerivAt (fun s : ℝ => weightedLoss ω (fourGon 0 0 + s • V)) 0 0 :=
  fourGon_weightedLoss_stationary ω V

end

end Laplace.Patterning
