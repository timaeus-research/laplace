/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.JnThirdOrder
import Laplace.OneD.MomentSecondOrder
import Laplace.OneD.MomentsAllOrders

/-!
# Gibbs moment rates with `t⁻²` remainders

The parity-improved `J_n` expansion of `JnThirdOrder` upgrades the seabed's second-moment rate from
`O(t^{-3/2})` to `O(t⁻²)` (`secondMoment_anharmonic_order3_rate`), with the same coefficient
`C₂ = (45A² − 12B)/λ`. The assembly goes through two small ratio lemmas instead of the inline
cancellation of `MomentSecondOrder`:

* `ratio_rate_order2`: `X = a + b/t + O(t⁻²)`, `Y = c + d/t + O(t⁻²)`, `Y ≥ c/2 > 0` give
  `X/Y = a/c + (bc − ad)/(c²t) + O(t⁻²)` (the exact identity
  `X − (p + q/t)Y = e_X − (p + q/t)e_Y − qd/t²`);
* `ratio_rate_order1`: the zeroth-order version, `X/Y = a/c + O(1/t)`.

The third and fourth moments need no new expansion: `thirdMoment_anharmonic_rate_sharp`
(`|t²⟨x³⟩ + 5α/(2λ³)| ≤ K/t`) comes from the existing `J₃` delta after multiplying by `√t`, and
`fourthMoment_anharmonic_t_rate` (`|t⟨x⁴⟩ − 3/(λ²t)| ≤ K/t²`) is the existing fourth-moment rate
divided by `t`.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-! ## Ratio lemmas -/

/-- **Ratio of two first-order expansions with `t⁻²` remainders.** -/
theorem ratio_rate_order2 {X Y a b c d KX KY t : ℝ} (ht : 1 ≤ t) (hc : 0 < c) (hY : c / 2 ≤ Y)
    (hX : |X - (a + b / t)| ≤ KX / t ^ 2) (hYe : |Y - (c + d / t)| ≤ KY / t ^ 2) :
    |X / Y - a / c - (b * c - a * d) / c ^ 2 / t| ≤
      2 / c * (KX + (|a / c| + |(b * c - a * d) / c ^ 2|) * KY +
        |(b * c - a * d) / c ^ 2 * d|) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hYpos : 0 < Y := lt_of_lt_of_le (by positivity) hY
  have hcne : c ≠ 0 := hc.ne'
  have hYne : Y ≠ 0 := hYpos.ne'
  have htne : t ≠ 0 := ht0.ne'
  set p := a / c with hp
  set q := (b * c - a * d) / c ^ 2 with hq
  have key : X / Y - p - q / t =
      ((X - (a + b / t)) - (p + q / t) * (Y - (c + d / t)) - q * d / t ^ 2) / Y := by
    rw [hp, hq]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hYpos]
  have hpq : |p + q / t| ≤ |p| + |q| := by
    calc |p + q / t| ≤ |p| + |q / t| := abs_add_le _ _
      _ = |p| + |q| / t := by rw [abs_div q t, abs_of_pos ht0]
      _ ≤ |p| + |q| := by
          have : |q| / t ≤ |q| := div_le_self (abs_nonneg _) ht
          linarith
  have hqd : |q * d / t ^ 2| = |q * d| / t ^ 2 := by rw [abs_div (q * d) (t ^ 2), abs_of_pos ht2]
  have hnum : |(X - (a + b / t)) - (p + q / t) * (Y - (c + d / t)) - q * d / t ^ 2| ≤
      (KX + (|p| + |q|) * KY + |q * d|) / t ^ 2 := by
    calc |(X - (a + b / t)) - (p + q / t) * (Y - (c + d / t)) - q * d / t ^ 2|
        ≤ |(X - (a + b / t)) - (p + q / t) * (Y - (c + d / t))| + |q * d / t ^ 2| := abs_sub _ _
      _ ≤ (|X - (a + b / t)| + |p + q / t| * |Y - (c + d / t)|) + |q * d / t ^ 2| := by
          gcongr
          calc |(X - (a + b / t)) - (p + q / t) * (Y - (c + d / t))|
              ≤ |X - (a + b / t)| + |(p + q / t) * (Y - (c + d / t))| := abs_sub _ _
            _ = |X - (a + b / t)| + |p + q / t| * |Y - (c + d / t)| := by rw [abs_mul]
      _ ≤ (KX / t ^ 2 + (|p| + |q|) * (KY / t ^ 2)) + |q * d| / t ^ 2 :=
          add_le_add (add_le_add hX (mul_le_mul hpq hYe (abs_nonneg _) (by positivity))) hqd.le
      _ = (KX + (|p| + |q|) * KY + |q * d|) / t ^ 2 := by ring
  calc |(X - (a + b / t)) - (p + q / t) * (Y - (c + d / t)) - q * d / t ^ 2| / Y
      ≤ |(X - (a + b / t)) - (p + q / t) * (Y - (c + d / t)) - q * d / t ^ 2| / (c / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hY
    _ ≤ ((KX + (|p| + |q|) * KY + |q * d|) / t ^ 2) / (c / 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 / c * (KX + (|p| + |q|) * KY + |q * d|) / t ^ 2 := by
        field_simp

/-- **Ratio of two zeroth-order expansions with `t⁻¹` remainders.** -/
theorem ratio_rate_order1 {X Y a c KX KY t : ℝ} (ht : 0 < t) (hc : 0 < c) (hY : c / 2 ≤ Y)
    (hX : |X - a| ≤ KX / t) (hYe : |Y - c| ≤ KY / t) :
    |X / Y - a / c| ≤ 2 / c * (KX + |a / c| * KY) / t := by
  have hYpos : 0 < Y := lt_of_lt_of_le (by positivity) hY
  have hcne : c ≠ 0 := hc.ne'
  have hYne : Y ≠ 0 := hYpos.ne'
  have key : X / Y - a / c = ((X - a) - a / c * (Y - c)) / Y := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hYpos]
  have hnum : |(X - a) - a / c * (Y - c)| ≤ (KX + |a / c| * KY) / t := by
    calc |(X - a) - a / c * (Y - c)| ≤ |X - a| + |a / c * (Y - c)| := abs_sub _ _
      _ = |X - a| + |a / c| * |Y - c| := by rw [abs_mul]
      _ ≤ KX / t + |a / c| * (KY / t) :=
          add_le_add hX (mul_le_mul_of_nonneg_left hYe (abs_nonneg _))
      _ = (KX + |a / c| * KY) / t := by ring
  calc |(X - a) - a / c * (Y - c)| / Y ≤ |(X - a) - a / c * (Y - c)| / (c / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hY
    _ ≤ ((KX + |a / c| * KY) / t) / (c / 2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 / c * (KX + |a / c| * KY) / t := by
        field_simp

/-! ## `J_n` deltas with evaluated Gaussian constants -/

variable {lam alpha gamma : ℝ}

/-- `J₀` delta at `t⁻²`: `|J₀ − (√(2π) + √(2π)(15A²/2 − 3B)/t)| ≤ K/t²`. -/
theorem J0_delta_order3 (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 0 t - (Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) *
        (15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam gamma) / t)| ≤ K / t ^ 2 := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic_order3 hlam hgamma hdisc 0
  refine ⟨K, hK, fun {t} ht ↦ ?_⟩
  have h := hb ht
  have hm0 : (∫ u : ℝ, u ^ 0 * Real.exp (-(u ^ 2) / 2)) = Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 0
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm3 : (∫ u : ℝ, u ^ (0 + 3) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd 1
  have hm4 : (∫ u : ℝ, u ^ (0 + 4) * Real.exp (-(u ^ 2) / 2)) = 3 * Real.sqrt (2 * Real.pi) :=
    integral_pow_mul_exp_neg_sq_half 2
  have hm6 : (∫ u : ℝ, u ^ (0 + 6) * Real.exp (-(u ^ 2) / 2)) = 15 * Real.sqrt (2 * Real.pi) :=
    integral_pow_mul_exp_neg_sq_half 3
  have hm7 : (∫ u : ℝ, u ^ (0 + 7) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd 3
  have hm9 : (∫ u : ℝ, u ^ (0 + 9) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd 4
  rw [hm0, hm3, hm4, hm6, hm7, hm9] at h
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have harg : Real.sqrt (2 * Real.pi) - cubicScale lam alpha / Real.sqrt t * 0 -
        quarticScale lam gamma / t * (3 * Real.sqrt (2 * Real.pi)) +
        cubicScale lam alpha ^ 2 / (2 * t) * (15 * Real.sqrt (2 * Real.pi)) +
        cubicScale lam alpha * quarticScale lam gamma / (t * Real.sqrt t) * 0 -
        cubicScale lam alpha ^ 3 / (6 * (t * Real.sqrt t)) * 0 =
      Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) *
        (15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam gamma) / t := by
    field_simp
    ring
  rw [harg] at h
  exact h

/-- `J₂` delta at `t⁻²`: `|J₂ − (√(2π) + √(2π)(105A²/2 − 15B)/t)| ≤ K/t²`. -/
theorem J2_delta_order3 (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 2 t - (Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) *
        (105 * cubicScale lam alpha ^ 2 / 2 - 15 * quarticScale lam gamma) / t)| ≤ K / t ^ 2 := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic_order3 hlam hgamma hdisc 2
  refine ⟨K, hK, fun {t} ht ↦ ?_⟩
  have h := hb ht
  have hm2 : (∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2)) = Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 1
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm5 : (∫ u : ℝ, u ^ (2 + 3) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd 2
  have hm6 : (∫ u : ℝ, u ^ (2 + 4) * Real.exp (-(u ^ 2) / 2)) = 15 * Real.sqrt (2 * Real.pi) :=
    integral_pow_mul_exp_neg_sq_half 3
  have hm8 : (∫ u : ℝ, u ^ (2 + 6) * Real.exp (-(u ^ 2) / 2)) = 105 * Real.sqrt (2 * Real.pi) :=
    integral_pow_mul_exp_neg_sq_half 4
  have hm9 : (∫ u : ℝ, u ^ (2 + 7) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd 4
  have hm11 : (∫ u : ℝ, u ^ (2 + 9) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd 5
  rw [hm2, hm5, hm6, hm8, hm9, hm11] at h
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have harg : Real.sqrt (2 * Real.pi) - cubicScale lam alpha / Real.sqrt t * 0 -
        quarticScale lam gamma / t * (15 * Real.sqrt (2 * Real.pi)) +
        cubicScale lam alpha ^ 2 / (2 * t) * (105 * Real.sqrt (2 * Real.pi)) +
        cubicScale lam alpha * quarticScale lam gamma / (t * Real.sqrt t) * 0 -
        cubicScale lam alpha ^ 3 / (6 * (t * Real.sqrt t)) * 0 =
      Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) *
        (105 * cubicScale lam alpha ^ 2 / 2 - 15 * quarticScale lam gamma) / t := by
    field_simp
    ring
  rw [harg] at h
  exact h

/-- `J₃` delta: `|J₃ + 15A√(2π)/√t| ≤ K/(t√t)` (from the second-order expansion; the `1/t` terms
vanish by parity). -/
theorem J3_delta_order2 (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 3 t + 15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
        Real.sqrt t| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic_order2 hlam hgamma hdisc 3
  refine ⟨K, hK, fun {t} ht ↦ ?_⟩
  have h := hb ht
  have hm3 : (∫ u : ℝ, u ^ 3 * Real.exp (-(u ^ 2) / 2)) = 0 := integral_pow_mul_exp_neg_sq_odd 1
  have hm6 : (∫ u : ℝ, u ^ (3 + 3) * Real.exp (-(u ^ 2) / 2)) = 15 * Real.sqrt (2 * Real.pi) :=
    integral_pow_mul_exp_neg_sq_half 3
  have hm7 : (∫ u : ℝ, u ^ (3 + 4) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd 3
  have hm9 : (∫ u : ℝ, u ^ (3 + 6) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd 4
  rw [hm3, hm6, hm7, hm9] at h
  have harg : (0 : ℝ) - cubicScale lam alpha / Real.sqrt t * (15 * Real.sqrt (2 * Real.pi)) -
        quarticScale lam gamma / t * 0 + cubicScale lam alpha ^ 2 / (2 * t) * 0 =
      -(15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) / Real.sqrt t) := by
    ring
  rw [harg, sub_neg_eq_add] at h
  exact h

/-- `J₀` at zeroth order: `|J₀ − √(2π)| ≤ K/t`. -/
theorem J0_delta_order1 (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 0 t - Real.sqrt (2 * Real.pi)| ≤ K / t := by
  obtain ⟨K, hK, hb⟩ := J0_delta_order3 hlam hgamma hdisc
  set c := Real.sqrt (2 * Real.pi) with hc
  set q₀ : ℝ := 15 * cubicScale lam alpha ^ 2 / 2 - 3 * quarticScale lam gamma with hq₀
  refine ⟨|c * q₀| + K, by positivity, fun {t} ht ↦ ?_⟩
  have ht0 : (0 : ℝ) < t := by linarith
  have h := hb ht
  calc |J_n lam alpha gamma 0 t - c|
      = |(J_n lam alpha gamma 0 t - (c + c * q₀ / t)) + c * q₀ / t| := by ring_nf
    _ ≤ |J_n lam alpha gamma 0 t - (c + c * q₀ / t)| + |c * q₀ / t| := abs_add_le _ _
    _ ≤ K / t ^ 2 + |c * q₀| / t := by
        gcongr
        rw [abs_div, abs_of_pos ht0]
    _ ≤ K / t + |c * q₀| / t := by
        gcongr
        calc t = t * 1 := (mul_one t).symm
          _ ≤ t * t := by gcongr
          _ = t ^ 2 := (sq t).symm
    _ = (|c * q₀| + K) / t := by ring

/-! ## The moment rates -/

/-- **Second-moment rate at `t⁻²`**: with `C₂ = (45A² − 12B)/λ`,
`|t⟨x²⟩ − 1/λ − C₂/t| ≤ K/t²` eventually. -/
theorem secondMoment_anharmonic_order3_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 2) -
        1 / lam - (45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma) / (lam * t)| ≤
      K / t ^ 2 := by
  obtain ⟨T, hT1, hJ0bd⟩ := J_0_eventually_bounded hlam hgamma hdisc
  obtain ⟨K₀, hK₀, hd0⟩ := J0_delta_order3 hlam hgamma hdisc
  obtain ⟨K₂, hK₂, hd2⟩ := J2_delta_order3 hlam hgamma hdisc
  set c := Real.sqrt (2 * Real.pi) with hc_def
  have hc_pos : 0 < c := Real.sqrt_pos.mpr two_pi_pos
  set A := cubicScale lam alpha with hA_def
  set B := quarticScale lam gamma with hB_def
  set q₀ : ℝ := 15 * A ^ 2 / 2 - 3 * B with hq₀
  set q₂ : ℝ := 105 * A ^ 2 / 2 - 15 * B with hq₂
  set c₂ : ℝ := 45 * A ^ 2 - 12 * B with hc₂
  refine ⟨2 / c * (K₂ + (|(1 : ℝ)| + |c₂|) * K₀ + |c₂ * (c * q₀)|) / lam, T, by positivity, hT1,
    fun {t} ht ↦ ?_⟩
  have ht1 : 1 ≤ t := hT1.trans ht
  have ht0 : 0 < t := by linarith
  have hlne : lam ≠ 0 := hlam.ne'
  have htne : t ≠ 0 := ht0.ne'
  obtain ⟨hJ0_lo, _⟩ := hJ0bd ht
  have hJ0_pos : 0 < J_n lam alpha gamma 0 t := lt_of_lt_of_le (by positivity) hJ0_lo
  set E := Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 2) with hE
  set J0 := J_n lam alpha gamma 0 t with hJ0
  set J2 := J_n lam alpha gamma 2 t with hJ2
  have hbridge : t * E = J2 / J0 / lam := by
    have h := sqrt_pow_mul_moment_eq hlam hgamma hdisc 2 ht0
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ lam * t)] at h
    rw [eq_div_iff hlne, ← h]
    ring
  have hratio := ratio_rate_order2 ht1 hc_pos hJ0_lo (hd2 ht1) (hd0 ht1)
  have hpc : c / c = 1 := div_self hc_pos.ne'
  have hq : (c * q₂ * c - c * (c * q₀)) / c ^ 2 = c₂ := by
    rw [hq₂, hq₀, hc₂]
    field_simp
    ring
  rw [hpc, hq] at hratio
  rw [hbridge]
  have key : J2 / J0 / lam - 1 / lam - c₂ / (lam * t) = (J2 / J0 - 1 - c₂ / t) / lam := by
    field_simp
  rw [key, abs_div, abs_of_pos hlam]
  calc |J2 / J0 - 1 - c₂ / t| / lam
      ≤ (2 / c * (K₂ + (|(1 : ℝ)| + |c₂|) * K₀ + |c₂ * (c * q₀)|) / t ^ 2) / lam :=
        div_le_div_of_nonneg_right hratio hlam.le
    _ = 2 / c * (K₂ + (|(1 : ℝ)| + |c₂|) * K₀ + |c₂ * (c * q₀)|) / lam / t ^ 2 := by ring

/-- **Third-moment rate, sharp**: `|t²⟨x³⟩ + 5α/(2λ³)| ≤ K/t` eventually. -/
theorem thirdMoment_anharmonic_rate_sharp (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 3) +
        5 * alpha / (2 * lam ^ 3)| ≤ K / t := by
  -- replace `λ` by `s²` so that `√λ = s` is rational
  set s := Real.sqrt lam with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hlam
  have hs : lam = s ^ 2 := (Real.sq_sqrt hlam.le).symm
  clear_value s
  subst hs
  obtain ⟨T, hT1, hJ0bd⟩ := J_0_eventually_bounded hlam hgamma hdisc
  obtain ⟨K₃, hK₃, hd3⟩ := J3_delta_order2 hlam hgamma hdisc
  obtain ⟨K₀, hK₀, hd0⟩ := J0_delta_order1 hlam hgamma hdisc
  set c := Real.sqrt (2 * Real.pi) with hc_def
  have hc_pos : 0 < c := Real.sqrt_pos.mpr two_pi_pos
  set A := cubicScale (s ^ 2) alpha with hA_def
  refine ⟨2 / c * (K₃ + |-(15 * A)| * K₀) / (s ^ 2 * s), T, by positivity, hT1,
    fun {t} ht ↦ ?_⟩
  have ht1 : 1 ≤ t := hT1.trans ht
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsne : s ≠ 0 := hs_pos.ne'
  have hcne : c ≠ 0 := hc_pos.ne'
  obtain ⟨hJ0_lo, _⟩ := hJ0bd ht
  have hJ0_pos : 0 < J_n (s ^ 2) alpha gamma 0 t := lt_of_lt_of_le (by positivity) hJ0_lo
  have hmom := sqrt_pow_mul_moment_eq hlam hgamma hdisc 3 ht0
  have hsq : Real.sqrt (s ^ 2 * t) = s * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs_pos.le]
  rw [hsq, eq_div_iff hJ0_pos.ne'] at hmom
  set E := Laplace.gibbsExpectation (anharmonicPotential (s ^ 2) alpha gamma) t (fun x ↦ x ^ 3)
    with hE
  set J0 := J_n (s ^ 2) alpha gamma 0 t with hJ0
  set J3 := J_n (s ^ 2) alpha gamma 3 t with hJ3
  have hbridge : t ^ 2 * E = (Real.sqrt t * J3 / J0) / (s ^ 2 * s) := by
    rw [eq_div_iff (by positivity), eq_div_iff hJ0_pos.ne', ← hmom]
    have hss := Real.mul_self_sqrt ht0.le
    linear_combination (-(s ^ 3 * E * J0 * (t + Real.sqrt t * Real.sqrt t))) * hss
  have hX : |Real.sqrt t * J3 - (-(15 * A * c))| ≤ K₃ / t := by
    have h := hd3 ht1
    rw [sub_neg_eq_add]
    have hfac : Real.sqrt t * J3 + 15 * A * c = Real.sqrt t * (J3 + 15 * A * c / Real.sqrt t) := by
      field_simp
    rw [hfac, abs_mul, abs_of_pos hst]
    calc Real.sqrt t * |J3 + 15 * A * c / Real.sqrt t|
        ≤ Real.sqrt t * (K₃ / (t * Real.sqrt t)) := mul_le_mul_of_nonneg_left h hst.le
      _ = K₃ / t := by
          field_simp
  have hratio := ratio_rate_order1 ht0 hc_pos hJ0_lo hX (hd0 ht1)
  have hpc : -(15 * A * c) / c = -(15 * A) := by field_simp
  rw [hpc] at hratio
  rw [hbridge]
  have key : Real.sqrt t * J3 / J0 / (s ^ 2 * s) + 5 * alpha / (2 * (s ^ 2) ^ 3) =
      (Real.sqrt t * J3 / J0 - -(15 * A)) / (s ^ 2 * s) := by
    rw [hA_def]
    unfold cubicScale
    rw [Real.sqrt_sq hs_pos.le]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < s ^ 2 * s)]
  calc |Real.sqrt t * J3 / J0 - -(15 * A)| / (s ^ 2 * s)
      ≤ (2 / c * (K₃ + |-(15 * A)| * K₀) / t) / (s ^ 2 * s) :=
        div_le_div_of_nonneg_right hratio (by positivity)
    _ = 2 / c * (K₃ + |-(15 * A)| * K₀) / (s ^ 2 * s) / t := by ring

/-- **Fourth moment divided by `t`**: `|t⟨x⁴⟩ − 3/(λ²t)| ≤ K/t²` eventually. -/
theorem fourthMoment_anharmonic_t_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 4) -
        3 / (lam ^ 2 * t)| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := fourthMoment_anharmonic_order2_rate hlam hgamma hdisc
  set C₄ : ℝ := (450 * cubicScale lam alpha ^ 2 - 96 * quarticScale lam gamma) / lam ^ 2 with hC₄
  refine ⟨|C₄| + K, T, by positivity, hT, fun {t} ht ↦ ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have hst1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
  have hlne : lam ≠ 0 := hlam.ne'
  have htne : t ≠ 0 := ht0.ne'
  set M4 := Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 4)
    with hM4
  have e4 : |t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t| ≤ K / (t * Real.sqrt t) := by
    rw [hC₄, div_div]
    exact h ht
  have key : t * M4 - 3 / (lam ^ 2 * t) = (t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t + C₄ / t ^ 2 := by
    field_simp
    ring
  rw [key]
  have ht2 : t * t ≤ t * (t * Real.sqrt t) := by
    have : t ≤ t * Real.sqrt t := le_mul_of_one_le_right ht0.le hst1
    exact mul_le_mul_of_nonneg_left this ht0.le
  calc |(t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t + C₄ / t ^ 2|
      ≤ |(t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t) / t| + |C₄ / t ^ 2| := abs_add_le _ _
    _ = |t ^ 2 * M4 - 3 / lam ^ 2 - C₄ / t| / t + |C₄| / t ^ 2 := by
        rw [abs_div, abs_of_pos ht0, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    _ ≤ K / (t * Real.sqrt t) / t + |C₄| / t ^ 2 := by
        gcongr
    _ ≤ K / t ^ 2 + |C₄| / t ^ 2 := by
        have hK' : K / (t * Real.sqrt t) / t ≤ K / t ^ 2 := by
          rw [div_div]
          apply div_le_div_of_nonneg_left hK (by positivity)
          calc t ^ 2 = t * 1 * t := by ring
            _ ≤ t * Real.sqrt t * t := by gcongr
        exact add_le_add hK' le_rfl
    _ = (|C₄| + K) / t ^ 2 := by ring

end Laplace.OneD
