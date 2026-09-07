/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MixedRatioCounterexample

/-!
# Conditional finite chart assembly

Unit 207 (Astra #22 programme B2, step 1). The paper's expectation expansion sums per-chart
(per-stratum) normal-block integrals; at leading order only the charts attaining the **minimum
exponent** and, among those, the **maximum logarithmic multiplicity** survive. This file proves that
selection rule abstractly, for any finite family of functions with power–log asymptotics:

* `leadExp p = min_a p_a`, `leadMult p m = max {m_a : p_a = leadExp p}`;
* `scale_ratio_tendsto`: `N^{-p_a}(log N)^{m_a-1} / (N^{-p_*}(log N)^{m_*-1}) → 1` if
  `(p_a, m_a) = (p_*, m_*)`, `→ 0` otherwise;
* `assembly_tendsto`: if `I_a(N)/(N^{-p_a}(log N)^{m_a-1}) → L_a` for every `a`, then
  `∑_a I_a(N) / (N^{-p_*}(log N)^{m_*-1}) → ∑_{a : (p_a,m_a)=(p_*,m_*)} L_a`. This is convergence at
  the *selected normalisation*; the limiting coefficient may vanish by cancellation between charts
  (signed `L_a`), in which case the actual leading order of the sum is smaller and not determined
  here;
* `assembly_ratio_tendsto`: numerator and denominator families assembled **separately**; if the
  selected denominator sum is positive, the quotient of the two sums converges to the quotient of
  the selected sums (the posterior limit is a ratio of sums, not a sum of chart ratios).

The family is finite and nonempty (`[Fintype ι] [Nonempty ι]`); the multiplicities satisfy
`m_a ≥ 1`. Everything about resolution, charts, Jacobians and partitions of unity enters only
through the hypotheses `hI`; this is a *conditional* assembly theorem. Non-chart remainders are not
modelled (they may be added as `o(N^{-p_*}(log N)^{m_*-1})` terms); zero chart coefficients are
allowed, only the selected denominator sum must be positive. The instantiation with the phase-dressed
chart integrals of Headlines XIII–XIV is unit 208. Zero `sorry`/`axiom`.
-/

open Filter Topology Real Asymptotics

namespace Laplace.Grammar

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The leading exponent of a finite family: the minimum. -/
noncomputable def leadExp (p : ι → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty p

/-- The leading logarithmic multiplicity: the maximum of `m` over the charts attaining the minimum
exponent. -/
noncomputable def leadMult (p : ι → ℝ) (m : ι → ℕ) : ℕ :=
  Finset.univ.sup fun a => if p a = leadExp p then m a else 0

theorem leadExp_le (p : ι → ℝ) (a : ι) : leadExp p ≤ p a :=
  Finset.inf'_le _ (Finset.mem_univ a)

theorem exists_leadExp (p : ι → ℝ) : ∃ a, p a = leadExp p := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p
  exact ⟨a, ha.symm⟩

theorem le_leadMult (p : ι → ℝ) (m : ι → ℕ) (a : ι) (ha : p a = leadExp p) :
    m a ≤ leadMult p m := by
  have := Finset.le_sup (f := fun a => if p a = leadExp p then m a else 0) (Finset.mem_univ a)
  rwa [if_pos ha] at this

theorem exists_leadMult (p : ι → ℝ) (m : ι → ℕ) (hm : ∀ a, 1 ≤ m a) :
    ∃ a, p a = leadExp p ∧ m a = leadMult p m := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun a => if p a = leadExp p then m a else 0)
  by_cases hp : p a = leadExp p
  · exact ⟨a, hp, by rw [leadMult, ha, if_pos hp]⟩
  · exfalso
    obtain ⟨b, hb⟩ := exists_leadExp p
    have h1 := le_leadMult p m b hb
    have h2 : leadMult p m = 0 := by rw [leadMult, ha, if_neg hp]
    have := hm b
    omega

theorem one_le_leadMult (p : ι → ℝ) (m : ι → ℕ) (hm : ∀ a, 1 ≤ m a) : 1 ≤ leadMult p m := by
  obtain ⟨a, -, hma⟩ := exists_leadMult p m hm
  rw [← hma]
  exact hm a

/-- **Scale comparison**: `N^{-p_a}(log N)^{m_a-1} / (N^{-p_*}(log N)^{m_*-1})` tends to `1` on the
selected charts and to `0` on the others. -/
theorem scale_ratio_tendsto (p : ι → ℝ) (m : ι → ℕ) (hm : ∀ a, 1 ≤ m a) (a : ι) :
    Tendsto (fun N : ℝ => (N ^ (-(p a)) * Real.log N ^ (m a - 1)) /
        (N ^ (-(leadExp p)) * Real.log N ^ (leadMult p m - 1))) atTop
      (𝓝 (if p a = leadExp p ∧ m a = leadMult p m then 1 else 0)) := by
  by_cases hp : p a = leadExp p
  · by_cases hmm : m a = leadMult p m
    · rw [if_pos ⟨hp, hmm⟩]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hN0 : 0 < N := by linarith
      rw [hp, hmm, div_self (mul_pos (Real.rpow_pos_of_pos hN0 _)
        (pow_pos (Real.log_pos hN) _)).ne']
    · rw [if_neg fun h => hmm h.2]
      have hlt : m a < leadMult p m := lt_of_le_of_ne (le_leadMult p m a hp) hmm
      have h0 : Tendsto (fun N : ℝ => (Real.log N)⁻¹ ^ (leadMult p m - m a)) atTop (𝓝 0) := by
        have := (Real.tendsto_log_atTop.inv_tendsto_atTop).pow (leadMult p m - m a)
        rwa [zero_pow (by omega)] at this
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      have hM : leadMult p m - 1 = (m a - 1) + (leadMult p m - m a) := by
        have := hm a
        omega
      rw [hp, hM, pow_add, inv_pow]
      field_simp
  · rw [if_neg fun h => hp h.1]
    have hlt : leadExp p < p a := lt_of_le_of_ne (leadExp_le p a) (Ne.symm hp)
    have hc0 : 0 < p a - leadExp p := by linarith
    have hlim : Tendsto (fun N : ℝ => Real.log N ^ ((m a - 1 : ℕ) : ℝ) / N ^ (p a - leadExp p))
        atTop (𝓝 0) :=
      (isLittleO_log_rpow_rpow_atTop ((m a - 1 : ℕ) : ℝ) hc0).tendsto_div_nhds_zero
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hN0 : 0 < N := by linarith
      have hlog : 0 < Real.log N := Real.log_pos hN
      positivity
    · filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
      have hN1 : 1 < N := lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos) hN
      have hN0 : 0 < N := by linarith
      have hlog1 : 1 ≤ Real.log N := by rwa [Real.le_log_iff_exp_le hN0]
      have hpow : N ^ (-(p a)) = N ^ (-(leadExp p)) * (N ^ (p a - leadExp p))⁻¹ := by
        rw [show -(p a) = -(leadExp p) + (-(p a - leadExp p)) by ring, Real.rpow_add hN0,
          Real.rpow_neg hN0.le (p a - leadExp p)]
      have hL : 1 ≤ Real.log N ^ (leadMult p m - 1) := one_le_pow₀ hlog1
      have hA : N ^ (-(leadExp p)) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
      have hB : N ^ (p a - leadExp p) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
      have hnn : 0 ≤ Real.log N ^ (m a - 1) / N ^ (p a - leadExp p) := by positivity
      rw [hpow, Real.rpow_natCast]
      calc N ^ (-(leadExp p)) * (N ^ (p a - leadExp p))⁻¹ * Real.log N ^ (m a - 1) /
            (N ^ (-(leadExp p)) * Real.log N ^ (leadMult p m - 1))
          = (Real.log N ^ (m a - 1) / N ^ (p a - leadExp p)) /
            Real.log N ^ (leadMult p m - 1) := by
            field_simp
        _ ≤ (Real.log N ^ (m a - 1) / N ^ (p a - leadExp p)) / 1 :=
            div_le_div_of_nonneg_left hnn one_pos hL
        _ = Real.log N ^ (m a - 1) / N ^ (p a - leadExp p) := div_one _

/-- **Conditional chart assembly**: if every chart integral has a power–log leading asymptotic
`I_a(N)/(N^{-p_a}(log N)^{m_a-1}) → L_a`, then the sum, normalised at `p_* = min p_a` and
`m_* = max {m_a : p_a = p_*}`, converges to the sum of the `L_a` over the charts attaining both
(possibly `0` by cancellation). -/
theorem assembly_tendsto (I : ι → ℝ → ℝ) (p : ι → ℝ) (m : ι → ℕ) (hm : ∀ a, 1 ≤ m a) (L : ι → ℝ)
    (hI : ∀ a, Tendsto (fun N : ℝ => I a N / (N ^ (-(p a)) * Real.log N ^ (m a - 1))) atTop
      (𝓝 (L a))) :
    Tendsto (fun N : ℝ => (∑ a, I a N) /
        (N ^ (-(leadExp p)) * Real.log N ^ (leadMult p m - 1))) atTop
      (𝓝 (∑ a ∈ Finset.univ.filter (fun a => p a = leadExp p ∧ m a = leadMult p m), L a)) := by
  have hT := tendsto_finsetSum Finset.univ fun a _ => (hI a).mul (scale_ratio_tendsto p m hm a)
  rw [Finset.sum_filter]
  have hlim : ∑ a, L a * (if p a = leadExp p ∧ m a = leadMult p m then (1 : ℝ) else 0) =
      ∑ a, if p a = leadExp p ∧ m a = leadMult p m then L a else 0 :=
    Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
  rw [← hlim]
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog := Real.log_pos hN
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hSa : N ^ (-(p a)) * Real.log N ^ (m a - 1) ≠ 0 := by positivity
  rw [div_mul_div_comm, mul_comm (N ^ (-(p a)) * Real.log N ^ (m a - 1))
    (N ^ (-(leadExp p)) * Real.log N ^ (leadMult p m - 1)), mul_div_mul_right _ _ hSa]

/-- **Assembled posterior quotient**: numerator and denominator families assembled separately; the
quotient of the sums converges to the quotient of the selected sums when the latter denominator is
positive. -/
theorem assembly_ratio_tendsto (Iφ Ic : ι → ℝ → ℝ) (p : ι → ℝ) (m : ι → ℕ) (hm : ∀ a, 1 ≤ m a)
    (Lφ Lc : ι → ℝ)
    (hφ : ∀ a, Tendsto (fun N : ℝ => Iφ a N / (N ^ (-(p a)) * Real.log N ^ (m a - 1))) atTop
      (𝓝 (Lφ a)))
    (hc : ∀ a, Tendsto (fun N : ℝ => Ic a N / (N ^ (-(p a)) * Real.log N ^ (m a - 1))) atTop
      (𝓝 (Lc a)))
    (hpos : 0 < ∑ a ∈ Finset.univ.filter (fun a => p a = leadExp p ∧ m a = leadMult p m), Lc a) :
    Tendsto (fun N : ℝ => (∑ a, Iφ a N) / ∑ a, Ic a N) atTop
      (𝓝 ((∑ a ∈ Finset.univ.filter (fun a => p a = leadExp p ∧ m a = leadMult p m), Lφ a) /
        ∑ a ∈ Finset.univ.filter (fun a => p a = leadExp p ∧ m a = leadMult p m), Lc a)) := by
  have h1 := assembly_tendsto Iφ p m hm Lφ hφ
  have h2 := assembly_tendsto Ic p m hm Lc hc
  refine (h1.div h2 hpos.ne').congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hS : N ^ (-(leadExp p)) * Real.log N ^ (leadMult p m - 1) ≠ 0 :=
    (mul_pos (Real.rpow_pos_of_pos hN0 _) (pow_pos (Real.log_pos hN) _)).ne'
  exact div_div_div_cancel_right₀ hS _ _

end Laplace.Grammar
