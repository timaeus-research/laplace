/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.MonomialPotential

/-!
# Order-theoretic recovery of a perturbation coefficient

A complement to the asymptotic recovery theorems of
`Laplace.OneD.Recovery`: the partition function is strictly decreasing
under pointwise enlargement of the potential
(`partitionFunction_lt_of_le_of_lt`), hence strictly antitone in the
coefficient of a nonnegative, somewhere-positive perturbation
(`partitionFunction_perturb_strictAntiOn`). Consequently the coefficient
of a subleading term is recoverable from the partition function at a
single temperature (`quartic_coefficient_recovery`): for
`x²/2 + b·x⁴` with `b ≥ 0`, one value of `Z` determines `b`. This is a
different (order-theoretic) mechanism than the expansion pairing of the
germbij note's Section 7.4, and in this instance a stronger conclusion:
one temperature suffices, no asymptotics needed.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- **Measure-theoretic core.** The partition function strictly decreases
under pointwise enlargement of the potential, strict on a set of positive
measure. -/
theorem partitionFunction_lt_of_le_of_measure_lt_pos {L₁ L₂ : ℝ → ℝ}
    {t : ℝ} (ht : 0 < t) (hle : ∀ x, L₁ x ≤ L₂ x)
    (hmeas₂ : AEStronglyMeasurable (fun x ↦ Real.exp (-(t * L₂ x))) volume)
    (h₁ : Integrable fun x ↦ Real.exp (-(t * L₁ x)))
    (hstrict : 0 < volume {x | L₁ x < L₂ x}) :
    partitionFunction L₂ t < partitionFunction L₁ t := by
  have h₂ : Integrable (fun x ↦ Real.exp (-(t * L₂ x))) := by
    apply h₁.mono' hmeas₂
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_left (hle x) ht.le))
  have hnonneg : ∀ x,
      0 ≤ Real.exp (-(t * L₁ x)) - Real.exp (-(t * L₂ x)) := fun x ↦
    sub_nonneg.mpr (Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_left (hle x) ht.le)))
  have hpos : 0 < ∫ x,
      (Real.exp (-(t * L₁ x)) - Real.exp (-(t * L₂ x))) := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg hnonneg
      (h₁.sub h₂)]
    have hsub : {x | L₁ x < L₂ x} ⊆ Function.support
        fun x ↦ Real.exp (-(t * L₁ x)) - Real.exp (-(t * L₂ x)) := by
      intro x hx
      have hlt : Real.exp (-(t * L₂ x)) < Real.exp (-(t * L₁ x)) :=
        Real.exp_lt_exp.mpr (neg_lt_neg (mul_lt_mul_of_pos_left hx ht))
      exact (sub_pos.mpr hlt).ne'
    exact lt_of_lt_of_le hstrict (measure_mono hsub)
  have hsplit := MeasureTheory.integral_sub h₁ h₂
  rw [hsplit] at hpos
  unfold partitionFunction
  linarith

/-- The partition function strictly decreases under pointwise enlargement
of the potential (strict somewhere, by continuity). -/
theorem partitionFunction_lt_of_le_of_lt {L₁ L₂ : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t) (hle : ∀ x, L₁ x ≤ L₂ x)
    (hc₁ : Continuous L₁) (hc₂ : Continuous L₂)
    (h₁ : Integrable fun x ↦ Real.exp (-(t * L₁ x)))
    (hx₀ : ∃ x₀, L₁ x₀ < L₂ x₀) :
    partitionFunction L₂ t < partitionFunction L₁ t := by
  obtain ⟨x₀, hx₀⟩ := hx₀
  exact partitionFunction_lt_of_le_of_measure_lt_pos ht hle
    (Real.continuous_exp.comp
      (continuous_const.mul hc₂).neg).aestronglyMeasurable
    h₁ ((isOpen_lt hc₁ hc₂).measure_pos volume ⟨x₀, hx₀⟩)

/-- The partition function is strictly antitone in the coefficient of a
nonnegative, somewhere-positive perturbation. -/
theorem partitionFunction_perturb_strictAntiOn (V g : ℝ → ℝ) {t : ℝ}
    (ht : 0 < t) (hV : Continuous V) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) {x₀ : ℝ} (hgx₀ : 0 < g x₀)
    (hI : Integrable fun x ↦ Real.exp (-(t * V x))) :
    StrictAntiOn (fun b ↦ partitionFunction (fun x ↦ V x + b * g x) t)
      (Set.Ici 0) := by
  intro b₁ hb₁ b₂ _ hb
  have hb₁0 : (0 : ℝ) ≤ b₁ := hb₁
  apply partitionFunction_lt_of_le_of_lt ht
  · intro x
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.le) (hg0 x)]
  · exact hV.add (continuous_const.mul hg)
  · exact hV.add (continuous_const.mul hg)
  · have hmeas : AEStronglyMeasurable
        (fun x : ℝ ↦ Real.exp (-(t * (V x + b₁ * g x)))) volume := by
      fun_prop
    apply hI.mono' hmeas
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ht.le (mul_nonneg hb₁0 (hg0 x))]
  · exact ⟨x₀, by nlinarith [mul_pos (sub_pos.mpr hb) hgx₀]⟩

/-- **Single-temperature recovery of a subleading coefficient.** For the
quartic-perturbed harmonic potential `x²/2 + b·x⁴` with `b ≥ 0`, the
partition function at one temperature determines `b`. -/
theorem quartic_coefficient_recovery {b₁ b₂ t₀ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (ht₀ : 0 < t₀)
    (h : partitionFunction (fun x ↦ kthPotential 1 x + b₁ * x ^ 4) t₀ =
      partitionFunction (fun x ↦ kthPotential 1 x + b₂ * x ^ 4) t₀) :
    b₁ = b₂ := by
  have hV : Continuous (kthPotential 1) := by
    unfold kthPotential
    fun_prop
  have hI : Integrable fun x : ℝ ↦ Real.exp (-(t₀ * kthPotential 1 x)) := by
    have := kth_integrable_pow_pot (le_refl 1) 0 ht₀
    simpa using this
  have hanti := partitionFunction_perturb_strictAntiOn (kthPotential 1)
    (fun x ↦ x ^ 4) ht₀ hV (by fun_prop) (fun x ↦ by positivity)
    (x₀ := 1) (by norm_num) hI
  exact hanti.injOn hb₁ hb₂ h

end Laplace.OneD
