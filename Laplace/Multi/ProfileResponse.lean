/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.TwoMonomialWall
import Laplace.Multi.ResponseMap

/-!
# The response across a wall: the profile law and its renormalised derivative

At the wall `σ* = 1 − q/p` of the two-monomial phase diagram the finite-`t` posterior of the
scaled observable `ψ(t^{1/p} w)` under `e^{-t(w^p + s w^q)}` with `s = c t^{-σ*}` is exactly the
**profile law** `ρ_c ∝ e^{-(y^p + c y^q)} dy` on `(0, ∞)` (`wall_posterior_eq_profile`): the wall
is a one-parameter family of laws in the crossover variable `c`, the same for every `t`. Its
response to the renormalised parameter `c` (Astra round 21: `∂_c = t^{-σ*} ∂_s`) is the
fluctuation–response identity

  `∂_c ⟨ψ⟩_c = −Cov_c(ψ, y^q)`   (`hasDerivAt_profilePosterior`, `hasDerivAt_wall_posterior`),

proved by dominated differentiation without any boundedness of the score `y^q`: the decay of
the profile `e^{-y^p}` dominates. This is the wall response theorem of the coupled phase diagram:
the loss contrast `w^q` is unbounded on the parameter space, so the exact-layer identity for
bounded contrasts (`ResponseMap`) does not apply directly, but after the wall rescaling the
response is again minus a covariance, with the score `y^q` of the scaled coordinate.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The profile numerator `N_ψ(c) = ∫₀^∞ ψ(y) e^{-(y^p + c y^q)} dy`. -/
noncomputable def profileNum (p q : ℝ) (ψ : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ψ y * Real.exp (-(y ^ p + c * y ^ q))

/-- The profile law `⟨ψ⟩_c = N_ψ(c)/N_1(c)`. -/
noncomputable def profilePosterior (p q : ℝ) (ψ : ℝ → ℝ) (c : ℝ) : ℝ :=
  profileNum p q ψ c / profileNum p q (fun _ ↦ 1) c

theorem integrableOn_rpow_mul_exp_neg_rpow_nonneg {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    IntegrableOn (fun y : ℝ ↦ y ^ q * Real.exp (-(y ^ p))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := p) (s := q) (b := 1) (by linarith) hp
    one_pos
  refine this.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
  simp

/-- `d/dc ∫₀^∞ ψ e^{-(y^p + c y^q)} = −∫₀^∞ ψ y^q e^{-(y^p + c y^q)}` for `c > 0`, bounded
measurable `ψ`. -/
theorem hasDerivAt_profileNum {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {ψ : ℝ → ℝ}
    (hψm : Measurable ψ) {Mψ : ℝ} (hψ : ∀ y, |ψ y| ≤ Mψ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    HasDerivAt (fun c ↦ profileNum p q ψ c)
      (-∫ y in Ioi (0 : ℝ), ψ y * y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q))) c₀ := by
  have hball : Metric.ball c₀ (c₀ / 2) ∈ 𝓝 c₀ := Metric.ball_mem_nhds c₀ (by linarith)
  have hcpos : ∀ c ∈ Metric.ball c₀ (c₀ / 2), 0 < c := fun c hc ↦ by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hc
    linarith [hc.1]
  have hmeasF : ∀ c : ℝ, AEStronglyMeasurable (fun y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) := fun c ↦
    (hψm.mul (Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg)).aestronglyMeasurable
  have hmeasF' : ∀ c : ℝ, AEStronglyMeasurable
      (fun y ↦ ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))) (volume.restrict (Ioi 0)) :=
    fun c ↦ (hψm.mul ((Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg).mul
      (measurable_id.pow_const q).neg)).aestronglyMeasurable
  have hbnd : ∀ c, 0 < c → ∀ y ∈ Ioi (0 : ℝ),
      Real.exp (-(y ^ p + c * y ^ q)) ≤ Real.exp (-(y ^ p)) := fun c hc y hy ↦ by
    rw [Real.exp_le_exp]
    have : 0 ≤ c * y ^ q := mul_nonneg hc.le (Real.rpow_nonneg (le_of_lt hy) q)
    linarith
  have hint : Integrable (fun y ↦ ψ y * Real.exp (-(y ^ p + c₀ * y ^ q)))
      (volume.restrict (Ioi 0)) := by
    refine ((integrableOn_exp_neg_rpow hp).const_mul Mψ).mono' (hmeasF c₀) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_mul (hψ y) (hbnd c₀ hc₀ y hy) (Real.exp_pos _).le
      (le_trans (abs_nonneg _) (hψ y))
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ c ∈ Metric.ball c₀ (c₀ / 2),
      ‖ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))‖ ≤
        Mψ * (y ^ q * Real.exp (-(y ^ p))) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy c hc ↦ ?_)
    have hy0 : (0 : ℝ) < y := hy
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, Real.abs_exp,
      abs_of_pos (Real.rpow_pos_of_pos hy0 q)]
    have := hbnd c (hcpos c hc) y hy
    calc |ψ y| * (Real.exp (-(y ^ p + c * y ^ q)) * y ^ q)
        ≤ Mψ * (Real.exp (-(y ^ p)) * y ^ q) :=
          mul_le_mul (hψ y) (mul_le_mul_of_nonneg_right this (Real.rpow_pos_of_pos hy0 q).le)
            (by positivity) (le_trans (abs_nonneg _) (hψ y))
      _ = Mψ * (y ^ q * Real.exp (-(y ^ p))) := by ring
  have hdiff : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ c ∈ Metric.ball c₀ (c₀ / 2),
      HasDerivAt (fun c ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
        (ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))) c := by
    refine Filter.Eventually.of_forall fun y c _ ↦ ?_
    have h1 : HasDerivAt (fun c ↦ -(y ^ p + c * y ^ q)) (-(y ^ q)) c := by
      have h0 := ((hasDerivAt_id c).mul_const (y ^ q)).const_add (y ^ p)
      simp only [id, one_mul] at h0
      exact h0.neg
    exact h1.exp.const_mul (ψ y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun c y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
    (F' := fun c y ↦ ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q))))
    hball (Filter.Eventually.of_forall hmeasF) hint (hmeasF' c₀) hbound
    ((integrableOn_rpow_mul_exp_neg_rpow_nonneg hp hq).const_mul Mψ) hdiff
  unfold profileNum
  refine key.2.congr_deriv ?_
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  ring

/-- **The wall response**: `∂_c ⟨ψ⟩_c = −Cov_c(ψ, y^q)` for the profile law. -/
theorem hasDerivAt_profilePosterior {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {ψ : ℝ → ℝ}
    (hψm : Measurable ψ) {Mψ : ℝ} (hψ : ∀ y, |ψ y| ≤ Mψ) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hZ : profileNum p q (fun _ ↦ 1) c₀ ≠ 0) :
    HasDerivAt (fun c ↦ profilePosterior p q ψ c)
      (-(profilePosterior p q (fun y ↦ ψ y * y ^ q) c₀ -
        profilePosterior p q ψ c₀ * profilePosterior p q (fun y ↦ y ^ q) c₀)) c₀ := by
  have hN := hasDerivAt_profileNum hp hq hψm hψ hc₀
  have hZ' := hasDerivAt_profileNum hp hq (ψ := fun _ ↦ (1 : ℝ)) measurable_const (Mψ := 1)
    (fun _ ↦ by simp) hc₀
  have hdiv := hN.div hZ' hZ
  refine hdiv.congr_deriv ?_
  unfold profilePosterior profileNum
  simp only [one_mul]
  set N := ∫ y in Ioi (0 : ℝ), ψ y * Real.exp (-(y ^ p + c₀ * y ^ q)) with hN'
  set NS := ∫ y in Ioi (0 : ℝ), ψ y * y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q)) with hNS
  set ZS := ∫ y in Ioi (0 : ℝ), y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q)) with hZS
  set Z := ∫ y in Ioi (0 : ℝ), Real.exp (-(y ^ p + c₀ * y ^ q)) with hZ''
  clear_value N NS ZS Z
  field_simp
  ring

/-- The scaled numerator at the wall: `∫₀^∞ ψ(t^{1/p} w) e^{-t(w^p + c t^{-σ*} w^q)} dw =
t^{-1/p} N_ψ(c)`. -/
theorem wall_numerator_scaled {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (ψ : ℝ → ℝ)
    (c : ℝ) :
    ∫ w in Ioi (0 : ℝ), ψ (t ^ (1 / p) * w) *
        Real.exp (-(t * (w ^ p + c * t ^ (-(1 - q / p)) * w ^ q))) =
      t ^ (-(1 / p)) * profileNum p q ψ c := by
  unfold profileNum
  have ha : 0 < t ^ (1 / p) := Real.rpow_pos_of_pos ht _
  have key := integral_comp_mul_left_Ioi (fun y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
    (0 : ℝ) ha
  rw [mul_zero, smul_eq_mul, ← Real.rpow_neg ht.le] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
  have hw0 : (0 : ℝ) < w := hw
  have hp' : (t ^ (1 / p) * w) ^ p = t * w ^ p := by
    rw [Real.mul_rpow ha.le hw0.le, ← Real.rpow_mul ht.le, one_div_mul_cancel hp.ne',
      Real.rpow_one]
  have hq' : (t ^ (1 / p) * w) ^ q = t ^ (q / p) * w ^ q := by
    rw [Real.mul_rpow ha.le hw0.le, ← Real.rpow_mul ht.le]
    congr 2
    ring
  have hh : t * t ^ (-(1 - q / p)) = t ^ (q / p) := by
    calc t * t ^ (-(1 - q / p)) = t ^ (1 : ℝ) * t ^ (-(1 - q / p)) := by rw [Real.rpow_one]
      _ = t ^ (1 + -(1 - q / p)) := (Real.rpow_add ht _ _).symm
      _ = t ^ (q / p) := by congr 1; ring
  congr 1
  rw [hp', hq']
  congr 1
  linear_combination (-(c * w ^ q)) * hh

/-- **The finite-`t` posterior at the wall is the profile law**: for every `t > 0` the posterior
mean of `ψ(t^{1/p} w)` under `e^{-t(w^p + c t^{-σ*} w^q)}` equals `⟨ψ⟩_c`. -/
theorem wall_posterior_eq_profile {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (ψ : ℝ → ℝ)
    (c : ℝ) :
    priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1) (fun w ↦ w ^ p + c * t ^ (-(1 - q / p)) * w ^ q)
        (fun w ↦ ψ (t ^ (1 / p) * w)) t = profilePosterior p q ψ c := by
  unfold priorExp priorZ profilePosterior
  have h1 := wall_numerator_scaled (q := q) hp ht ψ c
  have h2 := wall_numerator_scaled (q := q) hp ht (fun _ ↦ (1 : ℝ)) c
  simp only [one_mul] at h2
  simp only [mul_one]
  rw [h1, h2, mul_div_mul_left _ _ (Real.rpow_pos_of_pos ht _).ne']

/-- **The renormalised wall response at finite `t`**: the derivative in the crossover variable `c`
of the finite-`t` posterior mean of the scaled observable is `−Cov_c(ψ, y^q)`, for every `t`. -/
theorem hasDerivAt_wall_posterior {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) {t : ℝ} (ht : 0 < t)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {Mψ : ℝ} (hψ : ∀ y, |ψ y| ≤ Mψ) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hZ : profileNum p q (fun _ ↦ 1) c₀ ≠ 0) :
    HasDerivAt (fun c ↦ priorExp (volume.restrict (Ioi 0)) (fun _ ↦ 1)
        (fun w ↦ w ^ p + c * t ^ (-(1 - q / p)) * w ^ q) (fun w ↦ ψ (t ^ (1 / p) * w)) t)
      (-(profilePosterior p q (fun y ↦ ψ y * y ^ q) c₀ -
        profilePosterior p q ψ c₀ * profilePosterior p q (fun y ↦ y ^ q) c₀)) c₀ := by
  have := hasDerivAt_profilePosterior hp hq hψm hψ hc₀ hZ
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun c ↦ ?_)
  exact wall_posterior_eq_profile hp ht ψ c

end Laplace.Multi
