/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.IntegralRemainder
import Laplace.OneD.GaussianMoments
import Laplace.OneD.AnharmonicGibbsRegularity

/-!
# The Laplace scaling of all moments of the anharmonic Gibbs measure

For `ℓ(x) = λx²/2 + αx³/6 + γx⁴/24` (`λ, γ > 0`, `α² < 3λγ`) the rescaled integrals
`J_n(t) = ∫ uⁿ e^{−u²/2} e^{−r(t,u)}` converge to the Gaussian moments as `t → ∞`, by dominated
convergence with the seabed's `t`-uniform Gaussian bound (`tendsto_J_n`). Hence every moment of the
Gibbs measure has the Laplace scaling `√(λt)^n ⟨xⁿ⟩_t → E[gⁿ]` (`moment_anharmonic_asymptotic`):
`(λt)^k ⟨x^{2k}⟩ → (2k−1)‼` and `√(λt)^{2k+1} ⟨x^{2k+1}⟩ → 0` (`evenMoment_anharmonic_asymptotic`,
`oddMoment_anharmonic_tendsto_zero`). The degree-five and -six consequences that the note's E2
fourth prediction (`Cov[K, ψ]`) needs are `sixthMoment_anharmonic_asymptotic` (`t³⟨x⁶⟩ → 15/λ³`),
`sixthMoment_t_sq_tendsto_zero` and `fifthMoment_t_sq_tendsto_zero`.
-/

open MeasureTheory Filter Topology
open scoped Nat

namespace Laplace.OneD

variable {lam alpha gamma : ℝ}

/-- The rescaled perturbation vanishes pointwise as `t → ∞`. -/
theorem tendsto_rescaledPerturbation (lam alpha gamma u : ℝ) :
    Tendsto (fun t : ℝ => rescaledPerturbation lam alpha gamma t u) atTop (𝓝 0) := by
  unfold rescaledPerturbation
  have h1 : Tendsto (fun t : ℝ => cubicScale lam alpha * u ^ 3 / Real.sqrt t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h2 : Tendsto (fun t : ℝ => quarticScale lam gamma * u ^ 4 / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  simpa using h1.add h2

/-- **The rescaled moment integrals converge to the Gaussian moments**:
`J_n(t) → ∫ uⁿ e^{−u²/2}`. -/
theorem tendsto_J_n (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    (n : ℕ) :
    Tendsto (J_n lam alpha gamma n) atTop (𝓝 (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))) := by
  obtain ⟨c₀, hc₀, hboltz⟩ := rescaled_boltzmann_decay hlam hgamma hdisc
  unfold J_n
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => |u| ^ n * Real.exp (-(c₀ * u ^ 2))) ?_ ?_
    (integrable_abs_pow_mul_exp_neg_mul_sq hc₀ n) ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    apply Continuous.aestronglyMeasurable
    unfold rescaledPerturbation cubicScale quarticScale
    fun_prop
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    refine Eventually.of_forall fun u => ?_
    have hprod : Real.exp (-(u ^ 2) / 2) * Real.exp (-rescaledPerturbation lam alpha gamma t u) =
        Real.exp (-(u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _), mul_assoc, hprod]
    exact mul_le_mul_of_nonneg_left (hboltz ht u) (by positivity)
  · refine Eventually.of_forall fun u => ?_
    have h0 := (tendsto_rescaledPerturbation lam alpha gamma u).neg
    rw [neg_zero] at h0
    have h := (Real.continuous_exp.tendsto 0).comp h0
    rw [Real.exp_zero] at h
    have h' := h.const_mul (u ^ n * Real.exp (-(u ^ 2) / 2))
    rw [mul_one] at h'
    exact h'

/-- `√(λt)^n ⟨xⁿ⟩_t = J_n(t)/J_0(t)`. -/
theorem sqrt_pow_mul_moment_eq (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (lam * t) ^ n *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ n) =
      J_n lam alpha gamma n t / J_n lam alpha gamma 0 t := by
  have hn := I_n_J_n_relation lam alpha gamma n hlam ht
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have hZ : (∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x))) ≠ 0 :=
    (integral_exp_pos (integrable_exp_neg_t_anharmonic hlam hgamma hdisc ht)).ne'
  have hs : Real.sqrt (lam * t) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hlam ht)).ne'
  unfold Laplace.gibbsExpectation Laplace.partitionFunction J_n
  simp only [pow_zero, one_mul, zero_add, pow_one] at h0 ⊢
  rw [← hn, ← h0, pow_succ]
  field_simp

/-- **All moments scale as Laplace predicts**: `√(λt)^n ⟨xⁿ⟩_t → (∫ uⁿ e^{−u²/2})/√(2π)`, the `n`-th
moment of the standard Gaussian. -/
theorem moment_anharmonic_asymptotic (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (n : ℕ) :
    Tendsto (fun t : ℝ => Real.sqrt (lam * t) ^ n *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ n)) atTop
      (𝓝 ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2)) / Real.sqrt (2 * Real.pi))) := by
  have h := (tendsto_J_n hlam hgamma hdisc n).div (tendsto_J_0 hlam hgamma hdisc)
    (by positivity : Real.sqrt (2 * Real.pi) ≠ 0)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (sqrt_pow_mul_moment_eq hlam hgamma hdisc n ht).symm

/-- **Even moments**: `(λt)^k ⟨x^{2k}⟩_t → (2k − 1)‼`. -/
theorem evenMoment_anharmonic_asymptotic (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    Tendsto (fun t : ℝ => (lam * t) ^ k *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ (2 * k)))
      atTop (𝓝 ((2 * k - 1)‼ : ℝ)) := by
  have h := moment_anharmonic_asymptotic hlam hgamma hdisc (2 * k)
  rw [integral_pow_mul_exp_neg_sq_half, mul_div_assoc, div_self (by positivity), mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [pow_mul, Real.sq_sqrt (by positivity)]

/-- **Odd moments vanish to leading order**: `√(λt)^{2k+1} ⟨x^{2k+1}⟩_t → 0`. -/
theorem oddMoment_anharmonic_tendsto_zero (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    Tendsto (fun t : ℝ => Real.sqrt (lam * t) ^ (2 * k + 1) *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ (2 * k + 1)))
      atTop (𝓝 0) := by
  have h := moment_anharmonic_asymptotic hlam hgamma hdisc (2 * k + 1)
  rwa [integral_pow_mul_exp_neg_sq_odd, zero_div] at h

/-- `t^k ⟨x^{2k}⟩_t → (2k − 1)‼ / λ^k`. -/
theorem evenMoment_anharmonic_asymptotic' (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    Tendsto (fun t : ℝ => t ^ k *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ (2 * k)))
      atTop (𝓝 (((2 * k - 1)‼ : ℝ) / lam ^ k)) := by
  have h := (evenMoment_anharmonic_asymptotic hlam hgamma hdisc k).div_const (lam ^ k)
  refine h.congr' (Eventually.of_forall fun t => ?_)
  have := (pow_pos hlam k).ne'
  rw [mul_pow]
  field_simp

/-- **The sixth moment**: `t³ ⟨x⁶⟩_t → 15/λ³`. -/
theorem sixthMoment_anharmonic_asymptotic (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Tendsto (fun t : ℝ => t ^ 3 *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6)) atTop
      (𝓝 (15 / lam ^ 3)) := by
  have h := evenMoment_anharmonic_asymptotic' hlam hgamma hdisc 3
  norm_num [Nat.doubleFactorial] at h
  exact h

/-- `t² ⟨x⁶⟩_t → 0`. -/
theorem sixthMoment_t_sq_tendsto_zero (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Tendsto (fun t : ℝ => t ^ 2 *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 6)) atTop
      (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.mul (sixthMoment_anharmonic_asymptotic hlam hgamma hdisc)
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have := ht.ne'
  field_simp

/-- `t² ⟨x⁵⟩_t → 0`. -/
theorem fifthMoment_t_sq_tendsto_zero (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Tendsto (fun t : ℝ => t ^ 2 *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x => x ^ 5)) atTop
      (𝓝 0) := by
  have hodd := oddMoment_anharmonic_tendsto_zero hlam hgamma hdisc 2
  have hsqrt : Tendsto (fun t : ℝ => lam ^ 2 * Real.sqrt (lam * t)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop hlam)).const_mul_atTop
      (by positivity)
  have hpre : Tendsto (fun t : ℝ => 1 / (lam ^ 2 * Real.sqrt (lam * t))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have h := hpre.mul hodd
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr (mul_pos hlam ht)
  have h5 : Real.sqrt (lam * t) ^ (2 * 2 + 1) = (lam * t) ^ 2 * Real.sqrt (lam * t) := by
    rw [pow_succ, pow_mul, Real.sq_sqrt (by positivity)]
  rw [h5]
  have := hlam.ne'
  have := ht.ne'
  field_simp

end Laplace.OneD
