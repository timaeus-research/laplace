/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SeparableRecovery
import Laplace.Anchoring

/-!
# Separable monomial losses are identifiable from their coordinate second moments,
# beyond all orders

`SeparableRecovery` recovers the degrees and scales of a separable monomial loss
`L(x) = ∑ᵢ aᵢ xᵢ^{2kᵢ}` from exact ray equality of the normalized coordinate
second moments `⟨xᵢ²⟩_t`. The germbij note's data are asymptotic expansions, so
the honest hypothesis is agreement beyond all orders: for each coordinate,
`⟨xᵢ²⟩^{(1)}_t − ⟨xᵢ²⟩^{(2)}_t = o(t^{-N})` for every `N`. Since each side is an
exact power law `c t^{-1/k}`, superpolynomial agreement forces asymptotic
equivalence and then equality of exponents and coefficients
(`power_asymptote_unique`). Hence the `d` observables `xᵢ²` form a sufficient
family for this singular class, in the note's sense
(`separableMonomial_recovery_of_superPoly`): a complete singular
identifiability-and-recovery statement with a fixed finite family of tests.
-/

open Asymptotics Filter Real

namespace Laplace

/-- Superpolynomial closeness of a function to a positive power law forces
asymptotic equivalence. -/
theorem isEquivalent_of_superPoly_sub_power {f : ℝ → ℝ} {α β : ℝ} (hα : 0 < α)
    (h : SuperPoly fun t ↦ f t - α * t ^ β) :
    f ~[atTop] fun t : ℝ ↦ α * t ^ β := by
  set N : ℕ := ⌈-β⌉₊ with hN_def
  have hNβ : -(N : ℝ) ≤ β := by
    have := Nat.le_ceil (-β)
    linarith
  have hO : (fun t : ℝ ↦ t ^ (-(N : ℝ))) =O[atTop] fun t : ℝ ↦ α * t ^ β := by
    refine IsBigO.of_bound α⁻¹ ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _), Real.norm_of_nonneg
      (mul_nonneg hα.le (Real.rpow_nonneg htpos.le _)), ← mul_assoc, inv_mul_cancel₀ hα.ne',
      one_mul]
    exact Real.rpow_le_rpow_of_exponent_le ht hNβ
  exact (h N).trans_isBigO hO

namespace OneD

/-- **Second-moment recovery beyond all orders**: superpolynomial agreement of the
normalized second moments of two monomial potentials forces equal degrees and scales. -/
theorem kth_secondMoment_recovery_of_superPoly {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (h : SuperPoly fun t ↦
      gibbsExpectation (fun x ↦ a₁ * kthPotential k₁ x) t (fun x ↦ x ^ 2) -
        gibbsExpectation (fun x ↦ a₂ * kthPotential k₂ x) t (fun x ↦ x ^ 2)) :
    k₁ = k₂ ∧ a₁ = a₂ := by
  -- the two power laws
  set c₁ : ℝ := ((Nat.factorial (2 * k₁) : ℝ) / a₁) ^ ((1 : ℝ) / (k₁ : ℝ)) *
    (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) /
      Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ))) with hc₁_def
  set c₂ : ℝ := ((Nat.factorial (2 * k₂) : ℝ) / a₂) ^ ((1 : ℝ) / (k₂ : ℝ)) *
    (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) /
      Real.Gamma ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))) with hc₂_def
  have hc₁ : 0 < c₁ := secondMoment_coeff_pos hk₁ ha₁
  have hc₂ : 0 < c₂ := secondMoment_coeff_pos hk₂ ha₂
  have hlaw₁ : (fun t : ℝ ↦ gibbsExpectation (fun x ↦ a₁ * kthPotential k₁ x) t
      (fun x ↦ x ^ 2)) =ᶠ[atTop] fun t : ℝ ↦ c₁ * t ^ (-(1 : ℝ) / (k₁ : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact secondMoment_smul_kthPotential hk₁ ha₁ ht
  have hlaw₂ : (fun t : ℝ ↦ gibbsExpectation (fun x ↦ a₂ * kthPotential k₂ x) t
      (fun x ↦ x ^ 2)) =ᶠ[atTop] fun t : ℝ ↦ c₂ * t ^ (-(1 : ℝ) / (k₂ : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact secondMoment_smul_kthPotential hk₂ ha₂ ht
  -- superpolynomial closeness of the first power law to the second
  have hsub : SuperPoly fun t : ℝ ↦ c₁ * t ^ (-(1 : ℝ) / (k₁ : ℝ)) -
      c₂ * t ^ (-(1 : ℝ) / (k₂ : ℝ)) := by
    intro N
    refine (h N).congr' ?_ EventuallyEq.rfl
    filter_upwards [hlaw₁, hlaw₂] with t h1 h2
    simp only [h1, h2]
  have hequiv := isEquivalent_of_superPoly_sub_power hc₂ hsub
  obtain ⟨hβ, hα⟩ := power_asymptote_unique hc₁ hc₂ hequiv
  -- equal exponents give equal degrees, then equal coefficients give equal scales
  have hk₁0 : (0 : ℝ) < (k₁ : ℝ) := by exact_mod_cast hk₁
  have hk₂0 : (0 : ℝ) < (k₂ : ℝ) := by exact_mod_cast hk₂
  have hk : k₁ = k₂ := by
    have : (k₁ : ℝ) = k₂ := by
      have h' := hβ
      rw [div_eq_div_iff hk₁0.ne' hk₂0.ne'] at h'
      linarith
    exact_mod_cast this
  subst hk
  refine ⟨rfl, ?_⟩
  -- with equal degrees the coefficient is strictly decreasing in `a`
  have hΓ : 0 < Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) /
      Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) :=
    div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  have hpow : ((Nat.factorial (2 * k₁) : ℝ) / a₁) ^ ((1 : ℝ) / (k₁ : ℝ)) =
      ((Nat.factorial (2 * k₁) : ℝ) / a₂) ^ ((1 : ℝ) / (k₁ : ℝ)) := by
    have := hα
    simp only [hc₁_def, hc₂_def] at this
    exact mul_right_cancel₀ hΓ.ne' this
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k₁) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hbase : (Nat.factorial (2 * k₁) : ℝ) / a₁ = (Nat.factorial (2 * k₁) : ℝ) / a₂ := by
    have hr : (0 : ℝ) < (1 : ℝ) / (k₁ : ℝ) := by positivity
    have hx := div_nonneg hfac.le ha₁.le
    have hy := div_nonneg hfac.le ha₂.le
    exact le_antisymm ((Real.rpow_le_rpow_iff hx hy hr).mp hpow.le)
      ((Real.rpow_le_rpow_iff hy hx hr).mp hpow.ge)
  rw [div_eq_div_iff ha₁.ne' ha₂.ne'] at hbase
  exact (mul_left_cancel₀ hfac.ne' hbase).symm

end OneD

namespace Multi

variable {ι : Type*} [Fintype ι]

/-- **Separable monomial losses are identifiable beyond all orders from the `d`
coordinate second moments.** If for every coordinate the normalized second moments
of `∑ᵢ a₁ᵢ xᵢ^{2k₁ᵢ}` and `∑ᵢ a₂ᵢ xᵢ^{2k₂ᵢ}` agree beyond all orders in `t`, the
degrees and the scales coincide. -/
theorem separableMonomial_recovery_of_superPoly {a₁ a₂ : ι → ℝ} {k₁ k₂ : ι → ℕ}
    (ha₁ : ∀ i, 0 < a₁ i) (ha₂ : ∀ i, 0 < a₂ i) (hk₁ : ∀ i, 1 ≤ k₁ i) (hk₂ : ∀ i, 1 ≤ k₂ i)
    (h : ∀ i : ι, SuperPoly fun t ↦
      gibbsExpectation (separableMonomial a₁ k₁) t (fun w ↦ (w i) ^ 2) -
        gibbsExpectation (separableMonomial a₂ k₂) t (fun w ↦ (w i) ^ 2)) :
    k₁ = k₂ ∧ a₁ = a₂ := by
  have hcoord : ∀ i : ι, k₁ i = k₂ i ∧ a₁ i = a₂ i := by
    intro i
    refine OneD.kth_secondMoment_recovery_of_superPoly (hk₁ i) (hk₂ i) (ha₁ i) (ha₂ i) ?_
    intro N
    refine (h i N).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [gibbsExpectation_coordSq_separableMonomial ha₁ hk₁ ht i,
      gibbsExpectation_coordSq_separableMonomial ha₂ hk₂ ht i]
  exact ⟨funext fun i ↦ (hcoord i).1, funext fun i ↦ (hcoord i).2⟩

end Multi

end Laplace
