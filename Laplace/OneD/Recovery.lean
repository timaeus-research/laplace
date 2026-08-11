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
exponent) and the scale `a` (from the coefficient). The rigidity inputs
are `eventual_power_eq` (exact equality of two power functions on a ray)
and its asymptotic strengthening `power_asymptote_unique` (uniqueness of
power-law asymptotes); the recovery theorems
`kth_partitionFunction_recovery` (exact hypothesis) and
`kth_partitionFunction_recovery_of_isEquivalent` (asymptotic hypothesis,
the form matching the note, where the data is an expansion) combine them
with the closed form `partitionFunction_kthPotential` through the scaling
identity `partitionFunction_smul`.
-/

open Real MeasureTheory Asymptotics Filter

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

/-- **Uniqueness of power-law asymptotes.** Two power functions that are
asymptotically equivalent at infinity have equal exponents and equal
coefficients. This is the rigidity input matching expansion-level data:
agreement of asymptotic expansions, not exact equality. -/
theorem power_asymptote_unique {α₁ α₂ β₁ β₂ : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (h : (fun t : ℝ ↦ α₁ * t ^ β₁) ~[atTop] fun t : ℝ ↦ α₂ * t ^ β₂) :
    β₁ = β₂ ∧ α₁ = α₂ := by
  have hev : ∀ᶠ t : ℝ in atTop, (0 : ℝ) < t := eventually_gt_atTop 0
  have hz : ∀ᶠ t : ℝ in atTop, α₂ * t ^ β₂ ≠ 0 :=
    hev.mono fun t ht ↦ (mul_pos hα₂ (Real.rpow_pos_of_pos ht _)).ne'
  have h1 := (isEquivalent_iff_tendsto_one hz).mp h
  have h2 : Tendsto (fun t : ℝ ↦ (α₁ / α₂) * t ^ (β₁ - β₂)) atTop (nhds 1) := by
    apply h1.congr'
    filter_upwards [hev] with t ht
    simp only [Pi.div_apply]
    rw [Real.rpow_sub ht]
    have hne₁ : t ^ β₂ ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    field_simp
  have hδ : β₁ - β₂ = 0 := by
    rcases lt_trichotomy (β₁ - β₂) 0 with hlt | heq | hgt
    · have h3 : Tendsto (fun t : ℝ ↦ (α₁ / α₂) * t ^ (β₁ - β₂))
          atTop (nhds 0) := by
        have h4 : Tendsto (fun t : ℝ ↦ t ^ (β₁ - β₂)) atTop (nhds 0) := by
          have := tendsto_rpow_neg_atTop (neg_pos.mpr hlt)
          simpa using this
        simpa using h4.const_mul (α₁ / α₂)
      have := tendsto_nhds_unique h2 h3
      exact absurd this one_ne_zero
    · exact heq
    · have h3 : Tendsto (fun t : ℝ ↦ (α₁ / α₂) * t ^ (β₁ - β₂))
          atTop atTop :=
        (tendsto_rpow_atTop hgt).const_mul_atTop (div_pos hα₁ hα₂)
      exact absurd h2 (not_tendsto_nhds_of_tendsto_atTop h3 1)
  have hβ : β₁ = β₂ := sub_eq_zero.mp hδ
  refine ⟨hβ, ?_⟩
  have h4 : Tendsto (fun _ : ℝ ↦ α₁ / α₂) atTop (nhds 1) := by
    have h5 := h2
    rw [hδ] at h5
    simpa [Real.rpow_zero] using h5
  have h7 : Tendsto (fun _ : ℝ ↦ α₁ / α₂) atTop (nhds (α₁ / α₂)) :=
    tendsto_const_nhds
  have h6 : α₁ / α₂ = 1 := tendsto_nhds_unique h7 h4
  exact (div_eq_one_iff_eq hα₂.ne').mp h6

/-- Scaling the potential rescales the temperature:
`Z_{aL}(t) = Z_L(at)`. -/
lemma partitionFunction_smul (L : ℝ → ℝ) (a t : ℝ) :
    partitionFunction (fun x ↦ a * L x) t = partitionFunction L (a * t) := by
  unfold partitionFunction
  congr 1
  ext x
  congr 1
  ring

/-- The scaled even-monomial partition function as an explicit power
function of `t`. -/
lemma partitionFunction_kth_smul_rpow {k : ℕ} (hk : 1 ≤ k)
    {a : ℝ} (ha : 0 < a) {t : ℝ} (ht0 : 0 < t) :
    partitionFunction (fun x ↦ a * kthPotential k x) t =
      ((1 / (k : ℝ)) *
        ((Nat.factorial (2 * k) : ℝ) / a) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
        Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) *
      t ^ (-((1 : ℝ) / ((2 * k : ℕ) : ℝ))) := by
  rw [partitionFunction_smul, partitionFunction_kthPotential hk
    (mul_pos ha ht0)]
  have hsplit : (Nat.factorial (2 * k) : ℝ) / (a * t) =
      ((Nat.factorial (2 * k) : ℝ) / a) * t⁻¹ := by
    field_simp
  rw [hsplit, Real.mul_rpow
    (div_nonneg (Nat.cast_nonneg _) ha.le) (inv_nonneg.mpr ht0.le),
    Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le]
  ring

/-- Positivity of the coefficient in
`partitionFunction_kth_smul_rpow`. -/
lemma kth_coeff_pos {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) :
    0 < (1 / (k : ℝ)) *
      ((Nat.factorial (2 * k) : ℝ) / a) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
      Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h2k0 : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by positivity
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hΓ : 0 < Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- Matched exponents and coefficients of the closed forms determine the
degree and the scale. -/
lemma kth_recovery_of_data {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hβ : -((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) = -((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))
    (hα : (1 / (k₁ : ℝ)) *
        ((Nat.factorial (2 * k₁) : ℝ) / a₁) ^ ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) *
        Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) =
      (1 / (k₂ : ℝ)) *
        ((Nat.factorial (2 * k₂) : ℝ) / a₂) ^ ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
        Real.Gamma ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))) :
    k₁ = k₂ ∧ a₁ = a₂ := by
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
  obtain ⟨hβ, hα⟩ := eventual_power_eq
    (α₂ := (1 / (k₂ : ℝ)) *
      ((Nat.factorial (2 * k₂) : ℝ) / a₂) ^ ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
      Real.Gamma ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))
    (β₁ := -((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)))
    (β₂ := -((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))
    (kth_coeff_pos hk₁ ha₁)
    (fun t ht ↦ by
      have ht0 : 0 < t := lt_of_lt_of_le hT ht
      rw [← partitionFunction_kth_smul_rpow hk₁ ha₁ ht0,
        ← partitionFunction_kth_smul_rpow hk₂ ha₂ ht0]
      exact h t ht)
  exact kth_recovery_of_data hk₁ hk₂ ha₁ ha₂ hβ hα

/-- **Dimension-one recovery from asymptotic data** (germbij Section
7.4). Asymptotic equivalence of the partition functions at `t → ∞` (the
expansion-level hypothesis of the note) already forces equality of the
degrees and of the scales. -/
theorem kth_partitionFunction_recovery_of_isEquivalent
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (h : (fun t : ℝ ↦ partitionFunction (fun x ↦ a₁ * kthPotential k₁ x) t)
      ~[atTop] fun t : ℝ ↦
        partitionFunction (fun x ↦ a₂ * kthPotential k₂ x) t) :
    k₁ = k₂ ∧ a₁ = a₂ := by
  have he : ∀ (k : ℕ), 1 ≤ k → ∀ {a : ℝ}, 0 < a →
      (fun t : ℝ ↦ partitionFunction (fun x ↦ a * kthPotential k x) t)
        =ᶠ[atTop] fun t : ℝ ↦
          ((1 / (k : ℝ)) *
            ((Nat.factorial (2 * k) : ℝ) / a) ^
              ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
            Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) *
          t ^ (-((1 : ℝ) / ((2 * k : ℕ) : ℝ))) := by
    intro k hk a ha
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact partitionFunction_kth_smul_rpow hk ha ht
  obtain ⟨hβ, hα⟩ := power_asymptote_unique
    (kth_coeff_pos hk₁ ha₁) (kth_coeff_pos hk₂ ha₂)
    ((h.congr_left (he k₁ hk₁ ha₁)).congr_right (he k₂ hk₂ ha₂))
  exact kth_recovery_of_data hk₁ hk₂ ha₁ ha₂ hβ hα

end Laplace.OneD
