/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.SmoothChart

/-!
# Canonical identification of the 1D jet coefficients (grammar §4.2)

The jet coefficients `F_j(s) = e^{βs x₀} P_j(s)` (`chartJet`) were defined by finite polynomial
algebra from the Taylor data of `ξ, η`. Here they are identified with the normalised derivatives

  `F_j(s) = (1/j!) ∂_u^j (η(u) e^{βsξ(u)})|_{u=0}`,   `j < R`,   `s ≥ 0`,

by uniqueness of Taylor coefficients: two polynomial approximations of the same function with
`O(u^R)` errors on `(0, b]` have the same coefficients below `R` (`taylor_coeff_unique`), and the
amplitude jet remainder (unit 95) and Mathlib's Taylor theorem (unit 97) supply the two
approximations. Consequently the jets are independent of the truncation order
(`chartJet_indep`). No chain rule or Faà di Bruno formula is needed. Zero `sorry`/`axiom`.
-/

open Real Finset Filter Topology Set

namespace Laplace.Grammar

/-- A polynomial `∑_{n<R} d_n u^n` that is `O(u^R)` on `(0, b]` vanishes identically below `R`. -/
theorem coeff_eq_zero_of_isBigO (b : ℝ) (hb : 0 < b) (R : ℕ) :
    ∀ (d : ℕ → ℝ) (K : ℝ), (∀ u ∈ Ioc (0 : ℝ) b, |∑ n ∈ range R, d n * u ^ n| ≤ K * u ^ R) →
      ∀ n, n < R → d n = 0 := by
  induction R with
  | zero => intro d K _ n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ R ih =>
    intro d K h n hn
    -- the constant term vanishes by a limit argument
    have hcont : Continuous fun u : ℝ => ∑ n ∈ range (R + 1), d n * u ^ n :=
      continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_pow n)
    have hlim₁ : Tendsto (fun u : ℝ => ∑ n ∈ range (R + 1), d n * u ^ n) (𝓝[>] 0) (𝓝 (d 0)) := by
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rwa [Finset.sum_range_succ', Finset.sum_eq_zero fun n _ => by simp, zero_add, pow_zero,
        mul_one] at this
    have hlim₂ : Tendsto (fun u : ℝ => ∑ n ∈ range (R + 1), d n * u ^ n) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun u => K * u ^ (R + 1)) ?_ ?_
      · filter_upwards [Ioc_mem_nhdsGT hb] with u hu
        rw [Real.norm_eq_abs]
        exact h u hu
      · have hc : Continuous fun u : ℝ => K * u ^ (R + 1) := continuous_const.mul (continuous_pow _)
        have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
    have hd0 : d 0 = 0 := tendsto_nhds_unique hlim₁ hlim₂
    -- the shifted coefficients satisfy the hypothesis one order lower
    have hshift : ∀ u ∈ Ioc (0 : ℝ) b, |∑ n ∈ range R, d (n + 1) * u ^ n| ≤ K * u ^ R := by
      intro u hu
      have hu0 : 0 < u := hu.1
      have h1 := h u hu
      rw [Finset.sum_range_succ', hd0, zero_mul, add_zero] at h1
      have : ∑ n ∈ range R, d (n + 1) * u ^ (n + 1) = u * ∑ n ∈ range R, d (n + 1) * u ^ n := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [this, abs_mul, abs_of_pos hu0, pow_succ, mul_comm (u ^ R) u, ← mul_assoc] at h1
      exact le_of_mul_le_mul_left (by linarith [h1]) hu0
    rcases n with _ | n
    · exact hd0
    · exact ih (fun n => d (n + 1)) K hshift n (Nat.lt_of_succ_lt_succ hn)

/-- **Uniqueness of Taylor coefficients**: two order-`R` polynomial approximations of `f` with
`O(u^R)` errors on `(0, b]` agree below `R`. -/
theorem taylor_coeff_unique (b K₁ K₂ : ℝ) (hb : 0 < b) (R : ℕ) (f : ℝ → ℝ) (a a' : ℕ → ℝ)
    (h₁ : ∀ u ∈ Ioc (0 : ℝ) b, |f u - ∑ n ∈ range R, a n * u ^ n| ≤ K₁ * u ^ R)
    (h₂ : ∀ u ∈ Ioc (0 : ℝ) b, |f u - ∑ n ∈ range R, a' n * u ^ n| ≤ K₂ * u ^ R) :
    ∀ n, n < R → a n = a' n := by
  have h : ∀ u ∈ Ioc (0 : ℝ) b, |∑ n ∈ range R, (a n - a' n) * u ^ n| ≤ (K₁ + K₂) * u ^ R := by
    intro u hu
    have : ∑ n ∈ range R, (a n - a' n) * u ^ n
        = (f u - ∑ n ∈ range R, a' n * u ^ n) - (f u - ∑ n ∈ range R, a n * u ^ n) := by
      rw [show (f u - ∑ n ∈ range R, a' n * u ^ n) - (f u - ∑ n ∈ range R, a n * u ^ n)
          = ∑ n ∈ range R, a n * u ^ n - ∑ n ∈ range R, a' n * u ^ n by ring,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [this]
    calc |(f u - ∑ n ∈ range R, a' n * u ^ n) - (f u - ∑ n ∈ range R, a n * u ^ n)|
        ≤ |f u - ∑ n ∈ range R, a' n * u ^ n| + |f u - ∑ n ∈ range R, a n * u ^ n| := abs_sub _ _
      _ ≤ K₂ * u ^ R + K₁ * u ^ R := add_le_add (h₂ u hu) (h₁ u hu)
      _ = _ := by ring
  intro n hn
  exact sub_eq_zero.1 (coeff_eq_zero_of_isBigO b hb R (fun n => a n - a' n) (K₁ + K₂) h n hn)

/-- The chart amplitude `u ↦ η(u) e^{βsξ(u)}` is `C^R` when `ξ, η` are. -/
theorem chartAmp_contDiff (β s : ℝ) (R : ℕ) (ξ η : ℝ → ℝ) (hξ : ContDiff ℝ R ξ)
    (hη : ContDiff ℝ R η) : ContDiff ℝ R fun u => η u * Real.exp (β * s * ξ u) :=
  hη.mul (ContDiff.exp (contDiff_const.mul hξ))

/-- **Canonical identification of the jet coefficients.** For `ξ, η ∈ C^R` and `s ≥ 0`, the jet
coefficient `chartJet β (taylorData ξ) (taylorData η) R j s` is the normalised `j`-th derivative
`(1/j!) ∂_u^j (η(u) e^{βsξ(u)})|_{u=0}` for every `j < R`. -/
theorem chartJet_eq_taylorData (β b : ℝ) (hβ : 0 < β) (hb : 0 < b) (R : ℕ) (hR : 0 < R)
    (ξ η : ℝ → ℝ) (hξ : ContDiff ℝ R ξ) (hη : ContDiff ℝ R η) (s : ℝ) (hs : 0 ≤ s) :
    ∀ j, j < R →
      chartJet β (taylorData ξ) (taylorData η) R j s
        = taylorData (fun u => η u * Real.exp (β * s * ξ u)) j := by
  obtain ⟨n, rfl⟩ : ∃ n, R = n + 1 := ⟨R - 1, by omega⟩
  -- Taylor remainders of the data
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_taylor_remainder_bound ξ n b hb hξ
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_taylor_remainder_bound η n b hb hη
  have h1 : (1 : WithTop ℕ∞) ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.succ_le_succ n.zero_le
  obtain ⟨L₁, hL₁0, hL₁⟩ := exists_lipschitz_bound ξ b hb (hξ.of_le h1)
  have hξT : ∀ u ∈ Icc (0 : ℝ) b,
      |ξ u - ∑ i ∈ range (n + 1), taylorData ξ i * u ^ i| ≤ max K₁ K₂ * u ^ (n + 1) := fun u hu =>
    (hK₁ u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hu.1 _))
  have hηT : ∀ u ∈ Icc (0 : ℝ) b,
      |η u - ∑ i ∈ range (n + 1), taylorData η i * u ^ i| ≤ max K₁ K₂ * u ^ (n + 1) := fun u hu =>
    (hK₂ u hu).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hu.1 _))
  have hξL : ∀ u ∈ Icc (0 : ℝ) b, |ξ u - taylorData ξ 0| ≤ L₁ * u := by
    rw [taylorData_zero]; exact hL₁
  -- the jet approximation
  obtain ⟨C, hC0, hC⟩ := amp_jet_remainder β b (max K₁ K₂) L₁ hβ hb (le_max_of_le_left hK₁0) hL₁0
    (taylorData ξ) (taylorData η) (n + 1) hR ξ η hξT hηT hξL
  have hjet : ∀ u ∈ Ioc (0 : ℝ) b,
      |η u * Real.exp (β * s * ξ u)
        - ∑ j ∈ range (n + 1), chartJet β (taylorData ξ) (taylorData η) (n + 1) j s * u ^ j|
        ≤ (C * (1 + s) ^ (n + 1) * Real.exp (β * s * (taylorData ξ 0 + L₁ * b)))
          * u ^ (n + 1) := by
    intro u hu
    have := hC u (Ioc_subset_Icc_self hu) s hs
    unfold chartJet
    rw [show ∑ j ∈ range (n + 1), Real.exp (β * s * taylorData ξ 0)
          * ampJet β (taylorData ξ) (taylorData η) (n + 1) j s * u ^ j
        = ∑ j ∈ range (n + 1), u ^ j * (Real.exp (β * s * taylorData ξ 0)
          * ampJet β (taylorData ξ) (taylorData η) (n + 1) j s)
        from Finset.sum_congr rfl fun j _ => by ring]
    refine this.trans (le_of_eq ?_)
    ring
  -- the Taylor approximation
  obtain ⟨K₃, hK₃0, hK₃⟩ := exists_taylor_remainder_bound
    (fun u => η u * Real.exp (β * s * ξ u)) n b hb (chartAmp_contDiff β s (n + 1) ξ η hξ hη)
  exact taylor_coeff_unique b _ K₃ hb (n + 1) (fun u => η u * Real.exp (β * s * ξ u)) _ _ hjet
    (fun u hu => hK₃ u (Ioc_subset_Icc_self hu))

/-- **Independence of the truncation order**: the jets of orders `R ≤ R'` agree below `R`. -/
theorem chartJet_indep (β b : ℝ) (hβ : 0 < β) (hb : 0 < b) (R R' : ℕ) (hR : 0 < R) (hRR' : R ≤ R')
    (ξ η : ℝ → ℝ) (hξ : ContDiff ℝ R' ξ) (hη : ContDiff ℝ R' η) (s : ℝ) (hs : 0 ≤ s) :
    ∀ j, j < R →
      chartJet β (taylorData ξ) (taylorData η) R j s
        = chartJet β (taylorData ξ) (taylorData η) R' j s := by
  intro j hj
  have hle : (R : WithTop ℕ∞) ≤ R' := by exact_mod_cast hRR'
  rw [chartJet_eq_taylorData β b hβ hb R hR ξ η (hξ.of_le hle) (hη.of_le hle) s hs j hj,
    chartJet_eq_taylorData β b hβ hb R' (lt_of_lt_of_le hR hRR') ξ η hξ hη s hs j
      (lt_of_lt_of_le hj hRR')]

end Laplace.Grammar
