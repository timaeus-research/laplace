/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.MonomialPotential

/-!
# Dimension-one constructive recovery

The germbij note's Section 7.4 in its smallest form: for pure
even-monomial potentials `a * x^(2k) / (2k)!`, the large-`t` behavior of
the partition function alone recovers both the degree `k` (from the
exponent) and the scale `a` (from the coefficient). The rigidity input is
`eventual_power_eq`: two power functions `α * t ^ β` agreeing on a ray
have equal exponents and equal coefficients; the recovery corollary
`kth_partitionFunction_recovery` combines it with the closed form
`partitionFunction_kthPotential` through the scaling identity
`partitionFunction_smul`.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- Two power functions agreeing on a ray `[T, ∞)` have equal exponents
and equal coefficients. -/
theorem eventual_power_eq {α₁ α₂ β₁ β₂ T : ℝ}
    (hα₁ : 0 < α₁)
    (h : ∀ t : ℝ, T ≤ t → α₁ * t ^ β₁ = α₂ * t ^ β₂) :
    β₁ = β₂ ∧ α₁ = α₂ := by
  set t₀ : ℝ := max T 2 with ht₀_def
  have ht₀1 : (1 : ℝ) < t₀ := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have ht₀0 : (0 : ℝ) < t₀ := lt_trans one_pos ht₀1
  have h1 := h t₀ (le_max_left _ _)
  have h2 := h (t₀ * t₀)
    (le_trans (le_max_left _ _)
      (le_mul_of_one_le_left ht₀0.le ht₀1.le))
  rw [Real.mul_rpow ht₀0.le ht₀0.le, Real.mul_rpow ht₀0.le ht₀0.le] at h2
  set X : ℝ := t₀ ^ β₁ with hX_def
  set Y : ℝ := t₀ ^ β₂ with hY_def
  have hX : 0 < X := Real.rpow_pos_of_pos ht₀0 _
  have hY : 0 < Y := Real.rpow_pos_of_pos ht₀0 _
  have key : (α₁ * X) * (X - Y) = 0 := by linear_combination h2 - Y * h1
  have hXY : X = Y := by
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' (mul_pos hα₁ hX).ne'
    · exact sub_eq_zero.mp h'
  have hβ : β₁ = β₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd hXY (ne_of_lt ((Real.rpow_lt_rpow_left_iff ht₀1).mpr hlt))
    · exact absurd hXY.symm
        (ne_of_lt ((Real.rpow_lt_rpow_left_iff ht₀1).mpr hlt))
  refine ⟨hβ, ?_⟩
  rw [hXY] at h1
  exact mul_right_cancel₀ hY.ne' h1

/-- Scaling the potential rescales the temperature:
`Z_{aL}(t) = Z_L(at)`. -/
lemma partitionFunction_smul (L : ℝ → ℝ) (a t : ℝ) :
    partitionFunction (fun x ↦ a * L x) t = partitionFunction L (a * t) := by
  unfold partitionFunction
  congr 1
  ext x
  congr 1
  ring

/-- **Dimension-one recovery** (germbij Section 7.4, smallest instance).
For pure even-monomial potentials `a * x^(2k) / (2k)!` with `a > 0`,
`k ≥ 1`, eventual equality of the partition functions forces equality of
the degrees and of the scales: the exponent recovers `k` and the
coefficient recovers `a`. -/
theorem kth_partitionFunction_recovery
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    {a₁ a₂ T : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hT : 0 < T)
    (h : ∀ t : ℝ, T ≤ t →
      partitionFunction (fun x ↦ a₁ * kthPotential k₁ x) t =
      partitionFunction (fun x ↦ a₂ * kthPotential k₂ x) t) :
    k₁ = k₂ ∧ a₁ = a₂ := by
  -- Repackage each side as `α * t ^ (-(1/(2k)))`.
  have hform : ∀ (k : ℕ), 1 ≤ k → ∀ (a : ℝ), 0 < a → ∀ t : ℝ, T ≤ t →
      partitionFunction (fun x ↦ a * kthPotential k x) t =
        ((1 / (k : ℝ)) *
          ((Nat.factorial (2 * k) : ℝ) / a) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
          Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) *
        t ^ (-((1 : ℝ) / ((2 * k : ℕ) : ℝ))) := by
    intro k hk a ha t ht
    have ht0 : 0 < t := lt_of_lt_of_le hT ht
    rw [partitionFunction_smul, partitionFunction_kthPotential hk
      (mul_pos ha ht0)]
    have hsplit : (Nat.factorial (2 * k) : ℝ) / (a * t) =
        ((Nat.factorial (2 * k) : ℝ) / a) * t⁻¹ := by
      field_simp
    rw [hsplit, Real.mul_rpow
      (div_nonneg (Nat.cast_nonneg _) ha.le) (inv_nonneg.mpr ht0.le),
      Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le]
    ring
  -- Positivity of the coefficients.
  have hcoef : ∀ (k : ℕ), 1 ≤ k → ∀ (a : ℝ), 0 < a →
      0 < (1 / (k : ℝ)) *
        ((Nat.factorial (2 * k) : ℝ) / a) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
        Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
    intro k hk a ha
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h2k0 : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by positivity
    have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hΓ : 0 < Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by positivity)
    positivity
  -- Rigidity.
  obtain ⟨hβ, hα⟩ := eventual_power_eq
    (α₂ := (1 / (k₂ : ℝ)) *
      ((Nat.factorial (2 * k₂) : ℝ) / a₂) ^ ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
      Real.Gamma ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))
    (β₁ := -((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)))
    (β₂ := -((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))
    (hcoef k₁ hk₁ a₁ ha₁)
    (fun t ht ↦ by
      rw [← hform k₁ hk₁ a₁ ha₁ t ht, ← hform k₂ hk₂ a₂ ha₂ t ht]
      exact h t ht)
  -- Exponents give `k₁ = k₂`.
  have h2k₁0 : (0 : ℝ) < ((2 * k₁ : ℕ) : ℝ) := by positivity
  have h2k₂0 : (0 : ℝ) < ((2 * k₂ : ℕ) : ℝ) := by positivity
  have hk : k₁ = k₂ := by
    have hcast : ((2 * k₁ : ℕ) : ℝ) = ((2 * k₂ : ℕ) : ℝ) := by
      have h' : (1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) = 1 / ((2 * k₂ : ℕ) : ℝ) :=
        neg_injective hβ
      field_simp at h'
      linarith
    have h2 : 2 * k₁ = 2 * k₂ := by exact_mod_cast hcast
    omega
  refine ⟨hk, ?_⟩
  -- Coefficients give `a₁ = a₂`.
  subst hk
  have hpos : (0 : ℝ) < (1 / (k₁ : ℝ)) := by
    have : (0 : ℝ) < (k₁ : ℝ) := by exact_mod_cast hk₁
    positivity
  have hΓ : 0 < Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hrpow_eq :
      ((Nat.factorial (2 * k₁) : ℝ) / a₁) ^ ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) =
      ((Nat.factorial (2 * k₁) : ℝ) / a₂) ^ ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) :=
    mul_left_cancel₀ hpos.ne' (mul_right_cancel₀ hΓ.ne' hα)
  have hbase : (Nat.factorial (2 * k₁) : ℝ) / a₁ =
      (Nat.factorial (2 * k₁) : ℝ) / a₂ := by
    have hexp : ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) ≠ 0 := by positivity
    exact Real.rpow_left_injOn hexp
      (Set.mem_setOf_eq ▸ div_nonneg (Nat.cast_nonneg _) ha₁.le)
      (Set.mem_setOf_eq ▸ div_nonneg (Nat.cast_nonneg _) ha₂.le) hrpow_eq
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k₁) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hmul := (div_eq_div_iff ha₁.ne' ha₂.ne').mp hbase
  exact (mul_left_cancel₀ hfac.ne' hmul).symm

end Laplace.OneD
