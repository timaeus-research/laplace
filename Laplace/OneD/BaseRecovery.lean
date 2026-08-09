/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.JetRecovery

/-!
# Base-coefficient recovery from the second moment

Stages B1-B2 of the unequal-base programme: the second moment of the
jet Gibbs measure converges to the reference ratio `M₂(a)` as
`q → 0⁺` (`jet_secondMoment_tendsto`), the ratio has the Gamma closed
form `(1/a)^(1/k)·Γ(3/(2k))/Γ(1/(2k))`
(`reference_secondMoment_gamma`), which is strictly decreasing in the
base coefficient, so eventually-equal second moments force equal
bases (`base_recovery`). The limit-based variant
(`base_recovery_of_tendsto`) is the designed bridge to the later
smooth-germ programme, whose Taylor data is only order-controlled,
never exactly equal.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- The envelope forces a positive base coefficient: the profile at
`y = 0` is `a` itself. -/
theorem HasPositiveJetProfile.base_pos
    {R : ℕ} {a ρ : ℝ} {c : Fin R → ℝ}
    (h : HasPositiveJetProfile R a ρ c) : 0 < a := by
  have h0 := h.2 0
  unfold jetProfile at h0
  rw [Finset.sum_eq_zero fun i _ ↦ by
    rw [zero_pow (Nat.succ_ne_zero _)]
    ring] at h0
  linarith [h.1]

/-- **B1, limit half**: the normalized second moment of the jet Gibbs
measure converges to the reference ratio as `q → 0⁺`. -/
theorem jet_secondMoment_tendsto
    {k R : ℕ} {a ρ : ℝ} {c : Fin R → ℝ} (hk : 1 ≤ k)
    (h : HasPositiveJetProfile R a ρ c) :
    Tendsto (fun q : ℝ ↦ normalizedJetMoment k R 2 a q c) (𝓝[>] 0)
      (𝓝 ((∫ u : ℝ, u ^ 2 * Real.exp (-(a * u ^ (2 * k)))) /
        ∫ u : ℝ, Real.exp (-(a * u ^ (2 * k))))) := by
  have ha : 0 < a := h.base_pos
  have hint0 : Integrable (fun u : ℝ ↦
      Real.exp (-(a * u ^ (2 * k)))) := by
    have := integrable_abs_pow_mul_exp_neg_kth hk 0 ha
    exact this.congr (Filter.Eventually.of_forall fun u ↦ by simp)
  have hA0pos : 0 < ∫ u : ℝ, Real.exp (-(a * u ^ (2 * k))) := by
    rw [integral_pos_iff_support_of_nonneg
      (fun u ↦ (Real.exp_pos _).le) hint0]
    have hs : Function.support (fun u : ℝ ↦
        Real.exp (-(a * u ^ (2 * k)))) = Set.univ := by
      ext u
      simp [(Real.exp_pos _).ne']
    rw [hs]
    simp
  have hzero_ref : (∫ u : ℝ, Real.exp (-(a * u ^ (2 * k)))) =
      ∫ u : ℝ, u ^ 0 * Real.exp (-(a * u ^ (2 * k))) :=
    integral_congr_ae (Filter.Eventually.of_forall fun u ↦ by simp)
  have hden : Tendsto (fun q : ℝ ↦
      ∫ u : ℝ, Real.exp (-jetPotential k R a q c u)) (𝓝[>] 0)
      (𝓝 (∫ u : ℝ, Real.exp (-(a * u ^ (2 * k))))) := by
    have hlim := jet_integral_tendsto hk 0 h
    rw [← hzero_ref] at hlim
    have heq : (fun q : ℝ ↦ ∫ u : ℝ, u ^ 0 *
        Real.exp (-jetPotential k R a q c u)) = fun q : ℝ ↦
        ∫ u : ℝ, Real.exp (-jetPotential k R a q c u) := by
      funext q
      exact (integral_congr_ae
        (Filter.Eventually.of_forall fun u ↦ by simp)).symm
    rwa [heq] at hlim
  have hnum := jet_integral_tendsto hk 2 h
  have := hnum.div hden hA0pos.ne'
  exact this.congr fun q ↦ rfl

/-- **B1, closed-form half**: the reference second-moment ratio in
Gamma form, `(1/a)^(1/k)·Γ(3/(2k))/Γ(1/(2k))`, via the
`t = a·(2k)!` bridge to the monomial-potential API. -/
theorem reference_secondMoment_gamma
    {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) :
    (∫ u : ℝ, u ^ 2 * Real.exp (-(a * u ^ (2 * k)))) /
      (∫ u : ℝ, Real.exp (-(a * u ^ (2 * k)))) =
    ((1 : ℝ) / a) ^ ((1 : ℝ) / (k : ℝ)) *
      Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
      Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have ht : (0 : ℝ) < a * (Nat.factorial (2 * k) : ℝ) := by
    positivity
  have hmom := gibbsExpectation_kthPotential_even hk 1
    (t := a * (Nat.factorial (2 * k) : ℝ)) ht
  have harg : ∀ u : ℝ,
      -(a * (Nat.factorial (2 * k) : ℝ) * kthPotential k u) =
      -(a * u ^ (2 * k)) := by
    intro u
    rw [kthPotential_apply]
    field_simp
  simp only [gibbsExpectation, partitionFunction, harg] at hmom
  have h21 : (∫ x : ℝ, x ^ (2 * 1) * Real.exp (-(a * x ^ (2 * k)))) =
      ∫ u : ℝ, u ^ 2 * Real.exp (-(a * u ^ (2 * k))) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      norm_num)
  rw [h21] at hmom
  rw [hmom]
  have hbase : (Nat.factorial (2 * k) : ℝ) /
      (a * (Nat.factorial (2 * k) : ℝ)) = 1 / a := by
    field_simp
  rw [hbase]
  norm_num

/-- **B2, injectivity**: the reference second-moment ratio is
injective in the base coefficient (strict monotonicity of
`a ↦ (1/a)^(1/k)`). -/
theorem reference_secondMoment_injective
    {k : ℕ} (hk : 1 ≤ k) {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (heq : (∫ u : ℝ, u ^ 2 * Real.exp (-(a₁ * u ^ (2 * k)))) /
        (∫ u : ℝ, Real.exp (-(a₁ * u ^ (2 * k)))) =
      (∫ u : ℝ, u ^ 2 * Real.exp (-(a₂ * u ^ (2 * k)))) /
        (∫ u : ℝ, Real.exp (-(a₂ * u ^ (2 * k))))) :
    a₁ = a₂ := by
  rw [reference_secondMoment_gamma hk ha₁,
    reference_secondMoment_gamma hk ha₂] at heq
  have h2k_pos : 0 < ((2 * k : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * k := by omega
    exact_mod_cast this
  have hΓ3 : 0 < Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hΓ1 : 0 < Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hpow_eq : ((1 : ℝ) / a₁) ^ ((1 : ℝ) / (k : ℝ)) =
      ((1 : ℝ) / a₂) ^ ((1 : ℝ) / (k : ℝ)) := by
    have hΓratio : (0 : ℝ) < Real.Gamma
        ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
      positivity
    refine mul_right_cancel₀ hΓratio.ne' ?_
    calc ((1 : ℝ) / a₁) ^ ((1 : ℝ) / (k : ℝ)) *
          (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
            Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)))
        = ((1 : ℝ) / a₁) ^ ((1 : ℝ) / (k : ℝ)) *
            Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
            Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
          ring
      _ = ((1 : ℝ) / a₂) ^ ((1 : ℝ) / (k : ℝ)) *
            Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
            Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := heq
      _ = ((1 : ℝ) / a₂) ^ ((1 : ℝ) / (k : ℝ)) *
            (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
              Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) := by
          ring
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hinv : (1 : ℝ) / a₁ = 1 / a₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := Real.rpow_lt_rpow (by positivity) hlt
        (by positivity : (0 : ℝ) < 1 / (k : ℝ))
      linarith [hpow_eq]
    · have := Real.rpow_lt_rpow (by positivity) hgt
        (by positivity : (0 : ℝ) < 1 / (k : ℝ))
      linarith [hpow_eq]
  field_simp at hinv
  linarith [hinv]

/-- **B2, limit-based form** (the bridge interface for the later
smooth-germ programme): if the difference of normalized second
moments has limit `0` along `q → 0⁺`, the bases agree. -/
theorem base_recovery_of_tendsto
    {k R : ℕ} {a₁ a₂ ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ} (hk : 1 ≤ k)
    (h1 : HasPositiveJetProfile R a₁ ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a₂ ρ₂ c₂)
    (hdata : Tendsto (fun q : ℝ ↦
      normalizedJetMoment k R 2 a₁ q c₁ -
        normalizedJetMoment k R 2 a₂ q c₂) (𝓝[>] 0) (𝓝 0)) :
    a₁ = a₂ := by
  have hlim := (jet_secondMoment_tendsto hk h1).sub
    (jet_secondMoment_tendsto hk h2)
  have huniq := tendsto_nhds_unique hlim hdata
  exact reference_secondMoment_injective hk h1.base_pos h2.base_pos
    (by linarith [huniq])

/-- **B2**: eventually-equal normalized second moments force equal
base coefficients. -/
theorem base_recovery
    {k R : ℕ} {a₁ a₂ ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ} (hk : 1 ≤ k)
    (h1 : HasPositiveJetProfile R a₁ ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a₂ ρ₂ c₂)
    (hdata : ∀ᶠ q in 𝓝[>] (0 : ℝ),
      normalizedJetMoment k R 2 a₁ q c₁ =
        normalizedJetMoment k R 2 a₂ q c₂) :
    a₁ = a₂ := by
  apply base_recovery_of_tendsto hk h1 h2
  have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦ normalizedJetMoment k R 2 a₁ q c₁ -
        normalizedJetMoment k R 2 a₂ q c₂ := by
    filter_upwards [hdata] with q h
    rw [h, sub_self]
  exact tendsto_const_nhds.congr' hzero

end Laplace.OneD
