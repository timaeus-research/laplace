/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.MomentThirdOrder
import Laplace.OneD.MomentsAllOrders

/-!
# All moments of the anharmonic Gibbs law, sharply

The parity-sharp `J_n` layer (`JnThirdOrder`) and the two ratio lemmas (`MomentThirdOrder`) give
every moment of `ℓ(x) = λx²/2 + αx³/6 + γx⁴/24` at once. With `A = α/(6λ^{3/2})`, `B = γ/(24λ²)`:

* **even moments to second order** (`evenMoment_anharmonic_order2_rate`):
  `|t^k ⟨x^{2k}⟩ − (2k−1)‼/λ^k − C_k/(λ^k t)| ≤ K/t²` with
  `C_k = (A²/2)((2k+5)‼ − 15(2k−1)‼) − B((2k+3)‼ − 3(2k−1)‼)` (`evenMomentCoeff`; `C₁ = 45A² − 12B`,
  `C₂ = 450A² − 96B` are the seabed's second- and fourth-moment coefficients);
* **odd moments at their leading order, with a rate** (`oddMoment_anharmonic_rate`,
  `oddMoment_anharmonic_asymptotic`): `|t^{k+1} ⟨x^{2k+1}⟩ + α(2k+3)‼/(6λ^{k+2})| ≤ K/t`, so
  `t^{k+1}⟨x^{2k+1}⟩ → −α(2k+3)‼/(6λ^{k+2})` (`k = 0`: `−α/(2λ²)`, `k = 1`: `−5α/(2λ³)`).

The `(2k−1)‼` at `k = 0` is Lean's `0‼ = 1` (truncated subtraction), consistent with `⟨1⟩ = 1`.
-/

open Real MeasureTheory Filter Topology
open scoped Nat

namespace Laplace.OneD

variable {lam alpha gamma : ℝ}

/-! ## Gaussian moments with shifted indices -/

theorem gaussian_even_moment (j : ℕ) :
    (∫ u : ℝ, u ^ (2 * j) * Real.exp (-(u ^ 2) / 2)) =
      ((2 * j - 1)‼ : ℝ) * Real.sqrt (2 * Real.pi) :=
  integral_pow_mul_exp_neg_sq_half j

theorem gaussian_moment_shift (k j : ℕ) :
    (∫ u : ℝ, u ^ (2 * k + 2 * j) * Real.exp (-(u ^ 2) / 2)) =
      ((2 * k + 2 * j - 1)‼ : ℝ) * Real.sqrt (2 * Real.pi) := by
  have h := gaussian_even_moment (k + j)
  rwa [show 2 * (k + j) = 2 * k + 2 * j by ring] at h

/-! ## Even moments -/

/-- The second-order coefficient `C_k` of the `2k`-th moment (before division by `λ^k`). -/
noncomputable def evenMomentCoeff (lam alpha gamma : ℝ) (k : ℕ) : ℝ :=
  cubicScale lam alpha ^ 2 / 2 * (((2 * k + 5)‼ : ℝ) - 15 * ((2 * k - 1)‼ : ℝ)) -
    quarticScale lam gamma * (((2 * k + 3)‼ : ℝ) - 3 * ((2 * k - 1)‼ : ℝ))

theorem evenMomentCoeff_one (lam alpha gamma : ℝ) :
    evenMomentCoeff lam alpha gamma 1 =
      45 * cubicScale lam alpha ^ 2 - 12 * quarticScale lam gamma := by
  unfold evenMomentCoeff
  norm_num [Nat.doubleFactorial]
  ring

theorem evenMomentCoeff_two (lam alpha gamma : ℝ) :
    evenMomentCoeff lam alpha gamma 2 =
      450 * cubicScale lam alpha ^ 2 - 96 * quarticScale lam gamma := by
  unfold evenMomentCoeff
  norm_num [Nat.doubleFactorial]
  ring

/-- `J_{2k}` delta at `t⁻²`, with the Gaussian constants evaluated. -/
theorem J_even_delta (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma (2 * k) t - (((2 * k - 1)‼ : ℝ) * Real.sqrt (2 * Real.pi) +
        Real.sqrt (2 * Real.pi) * (cubicScale lam alpha ^ 2 / 2 * ((2 * k + 5)‼ : ℝ) -
          quarticScale lam gamma * ((2 * k + 3)‼ : ℝ)) / t)| ≤ K / t ^ 2 := by
  obtain ⟨K, hK, hb⟩ := J_n_even_asymptotic_order3 hlam hgamma hdisc k
  refine ⟨K, hK, fun {t} ht ↦ ?_⟩
  have h := hb ht
  have hm0 := gaussian_even_moment k
  have hm4 : (∫ u : ℝ, u ^ (2 * k + 4) * Real.exp (-(u ^ 2) / 2)) =
      ((2 * k + 3)‼ : ℝ) * Real.sqrt (2 * Real.pi) := by
    have h' := gaussian_moment_shift k 2
    rwa [show 2 * k + 2 * 2 = 2 * k + 4 by ring, show 2 * k + 4 - 1 = 2 * k + 3 by omega] at h'
  have hm6 : (∫ u : ℝ, u ^ (2 * k + 6) * Real.exp (-(u ^ 2) / 2)) =
      ((2 * k + 5)‼ : ℝ) * Real.sqrt (2 * Real.pi) := by
    have h' := gaussian_moment_shift k 3
    rwa [show 2 * k + 2 * 3 = 2 * k + 6 by ring, show 2 * k + 6 - 1 = 2 * k + 5 by omega] at h'
  rw [hm0, hm4, hm6] at h
  have ht0 : (0 : ℝ) < t := by linarith
  have harg : ((2 * k - 1)‼ : ℝ) * Real.sqrt (2 * Real.pi) -
        quarticScale lam gamma / t * (((2 * k + 3)‼ : ℝ) * Real.sqrt (2 * Real.pi)) +
        cubicScale lam alpha ^ 2 / (2 * t) * (((2 * k + 5)‼ : ℝ) * Real.sqrt (2 * Real.pi)) =
      ((2 * k - 1)‼ : ℝ) * Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) *
        (cubicScale lam alpha ^ 2 / 2 * ((2 * k + 5)‼ : ℝ) -
          quarticScale lam gamma * ((2 * k + 3)‼ : ℝ)) / t := by
    field_simp
    ring
  rw [harg] at h
  exact h

/-- **Even moments to second order with a `t⁻²` remainder**:
`|t^k ⟨x^{2k}⟩ − (2k−1)‼/λ^k − C_k/(λ^k t)| ≤ K/t²` eventually. -/
theorem evenMoment_anharmonic_order2_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ k * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x ↦ x ^ (2 * k)) - ((2 * k - 1)‼ : ℝ) / lam ^ k -
        evenMomentCoeff lam alpha gamma k / (lam ^ k * t)| ≤ K / t ^ 2 := by
  obtain ⟨T, hT1, hJ0bd⟩ := J_0_eventually_bounded hlam hgamma hdisc
  obtain ⟨K₀, hK₀, hd0⟩ := J0_delta_order3 hlam hgamma hdisc
  obtain ⟨K₂, hK₂, hd2⟩ := J_even_delta hlam hgamma hdisc k
  set c := Real.sqrt (2 * Real.pi) with hc_def
  have hc_pos : 0 < c := Real.sqrt_pos.mpr two_pi_pos
  set A := cubicScale lam alpha with hA_def
  set B := quarticScale lam gamma with hB_def
  set D : ℝ := ((2 * k - 1)‼ : ℝ) with hD
  set q₀ : ℝ := 15 * A ^ 2 / 2 - 3 * B with hq₀
  set q₂ : ℝ := A ^ 2 / 2 * ((2 * k + 5)‼ : ℝ) - B * ((2 * k + 3)‼ : ℝ) with hq₂
  set Ck := evenMomentCoeff lam alpha gamma k with hCk
  have hcne : c ≠ 0 := hc_pos.ne'
  have hCk' : (c * q₂ * c - D * c * (c * q₀)) / c ^ 2 = Ck := by
    rw [hCk, evenMomentCoeff, hq₂, hq₀, hD, ← hA_def, ← hB_def]
    field_simp
    ring
  have hDc : D * c / c = D := by field_simp
  refine ⟨2 / c * (K₂ + (|D| + |Ck|) * K₀ + |Ck * (c * q₀)|) / lam ^ k, T, by positivity, hT1,
    fun {t} ht ↦ ?_⟩
  have ht1 : 1 ≤ t := hT1.trans ht
  have ht0 : 0 < t := by linarith
  have hlne : lam ≠ 0 := hlam.ne'
  have hlk : lam ^ k ≠ 0 := pow_ne_zero k hlne
  have htne : t ≠ 0 := ht0.ne'
  obtain ⟨hJ0_lo, _⟩ := hJ0bd ht
  have hJ0_pos : 0 < J_n lam alpha gamma 0 t := lt_of_lt_of_le (by positivity) hJ0_lo
  have hmom := sqrt_pow_mul_moment_eq hlam hgamma hdisc (2 * k) ht0
  rw [pow_mul, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ lam * t), mul_pow] at hmom
  set E := Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ (2 * k))
    with hE
  set J0 := J_n lam alpha gamma 0 t with hJ0
  set J2 := J_n lam alpha gamma (2 * k) t with hJ2
  have hbridge : t ^ k * E = J2 / J0 / lam ^ k := by
    rw [eq_div_iff hlk, ← hmom]
    ring
  have hratio := ratio_rate_order2 ht1 hc_pos hJ0_lo (hd2 ht1) (hd0 ht1)
  rw [hDc, hCk'] at hratio
  rw [hbridge]
  have key : J2 / J0 / lam ^ k - D / lam ^ k - Ck / (lam ^ k * t) =
      (J2 / J0 - D - Ck / t) / lam ^ k := by
    field_simp
  rw [key, abs_div, abs_of_pos (pow_pos hlam k)]
  calc |J2 / J0 - D - Ck / t| / lam ^ k
      ≤ (2 / c * (K₂ + (|D| + |Ck|) * K₀ + |Ck * (c * q₀)|) / t ^ 2) / lam ^ k :=
        div_le_div_of_nonneg_right hratio (by positivity)
    _ = 2 / c * (K₂ + (|D| + |Ck|) * K₀ + |Ck * (c * q₀)|) / lam ^ k / t ^ 2 := by ring

/-- **Even moments at leading order, with a rate**: `|t^k ⟨x^{2k}⟩ − (2k−1)‼/λ^k| ≤ K/t`. -/
theorem evenMoment_anharmonic_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ k * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x ↦ x ^ (2 * k)) - ((2 * k - 1)‼ : ℝ) / lam ^ k| ≤ K / t := by
  obtain ⟨K, T, hK, hT, h⟩ := evenMoment_anharmonic_order2_rate hlam hgamma hdisc k
  set Ck := evenMomentCoeff lam alpha gamma k with hCk
  refine ⟨K + |Ck / lam ^ k|, T, by positivity, hT, fun {t} ht ↦ ?_⟩
  have ht1 : 1 ≤ t := hT.trans ht
  have ht0 : 0 < t := by linarith
  have hlk : lam ^ k ≠ 0 := pow_ne_zero k hlam.ne'
  have e := h ht
  set X := t ^ k * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
    (fun x ↦ x ^ (2 * k)) with hX
  set D : ℝ := ((2 * k - 1)‼ : ℝ) with hD
  have hsplit : X - D / lam ^ k = (X - D / lam ^ k - Ck / (lam ^ k * t)) + Ck / lam ^ k / t := by
    field_simp
    ring
  rw [hsplit]
  calc |(X - D / lam ^ k - Ck / (lam ^ k * t)) + Ck / lam ^ k / t|
      ≤ |X - D / lam ^ k - Ck / (lam ^ k * t)| + |Ck / lam ^ k / t| := abs_add_le _ _
    _ ≤ K / t ^ 2 + |Ck / lam ^ k| / t := by
        gcongr
        rw [abs_div, abs_of_pos ht0]
    _ ≤ K / t + |Ck / lam ^ k| / t := by
        gcongr
        calc t = t * 1 := (mul_one t).symm
          _ ≤ t * t := by gcongr
          _ = t ^ 2 := (sq t).symm
    _ = (K + |Ck / lam ^ k|) / t := by ring

/-! ## Odd moments -/

/-- `√t J_{2k+1}` delta: `|√t J_{2k+1} + A (2k+3)‼ √(2π)| ≤ K/t`. -/
theorem J_odd_delta (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |Real.sqrt t * J_n lam alpha gamma (2 * k + 1) t +
        cubicScale lam alpha * ((2 * k + 3)‼ : ℝ) * Real.sqrt (2 * Real.pi)| ≤ K / t := by
  obtain ⟨K, hK, hb⟩ := J_n_odd_asymptotic_order3 hlam hgamma hdisc k
  set c := Real.sqrt (2 * Real.pi) with hc
  set A := cubicScale lam alpha with hA
  set B := quarticScale lam gamma with hB
  have hm4 : (∫ u : ℝ, u ^ (2 * k + 4) * Real.exp (-(u ^ 2) / 2)) = ((2 * k + 3)‼ : ℝ) * c := by
    have h' := gaussian_moment_shift k 2
    rwa [show 2 * k + 2 * 2 = 2 * k + 4 by ring, show 2 * k + 4 - 1 = 2 * k + 3 by omega] at h'
  have hm8 : (∫ u : ℝ, u ^ (2 * k + 8) * Real.exp (-(u ^ 2) / 2)) = ((2 * k + 7)‼ : ℝ) * c := by
    have h' := gaussian_moment_shift k 4
    rwa [show 2 * k + 2 * 4 = 2 * k + 8 by ring, show 2 * k + 8 - 1 = 2 * k + 7 by omega] at h'
  have hm10 : (∫ u : ℝ, u ^ (2 * k + 10) * Real.exp (-(u ^ 2) / 2)) =
      ((2 * k + 9)‼ : ℝ) * c := by
    have h' := gaussian_moment_shift k 5
    rwa [show 2 * k + 2 * 5 = 2 * k + 10 by ring, show 2 * k + 10 - 1 = 2 * k + 9 by omega] at h'
  set R : ℝ := A * B * (((2 * k + 7)‼ : ℝ) * c) - A ^ 3 / 6 * (((2 * k + 9)‼ : ℝ) * c) with hR
  refine ⟨K + |R|, by positivity, fun {t} ht ↦ ?_⟩
  have h := hb ht
  rw [hm4, hm8, hm10] at h
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
  have hst_le : Real.sqrt t ≤ t := by nlinarith [Real.mul_self_sqrt ht0.le, hst1]
  set J := J_n lam alpha gamma (2 * k + 1) t with hJ
  set X := J - (-(A / Real.sqrt t * (((2 * k + 3)‼ : ℝ) * c)) +
    A * B / (t * Real.sqrt t) * (((2 * k + 7)‼ : ℝ) * c) -
    A ^ 3 / (6 * (t * Real.sqrt t)) * (((2 * k + 9)‼ : ℝ) * c)) with hXdef
  have key : Real.sqrt t * J + A * ((2 * k + 3)‼ : ℝ) * c = Real.sqrt t * X + R / t := by
    rw [hXdef, hR]
    field_simp
    ring
  rw [key]
  calc |Real.sqrt t * X + R / t| ≤ |Real.sqrt t * X| + |R / t| := abs_add_le _ _
    _ = Real.sqrt t * |X| + |R| / t := by
        rw [abs_mul, abs_of_pos hst, abs_div, abs_of_pos ht0]
    _ ≤ Real.sqrt t * (K / t ^ 2) + |R| / t := by gcongr
    _ ≤ t * (K / t ^ 2) + |R| / t := by gcongr
    _ = (K + |R|) / t := by
        field_simp

/-- **All odd moments at their leading order, with a rate**:
`|t^{k+1} ⟨x^{2k+1}⟩ + α(2k+3)‼/(6λ^{k+2})| ≤ K/t` eventually. -/
theorem oddMoment_anharmonic_rate (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ (k + 1) * Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x ↦ x ^ (2 * k + 1)) + alpha * ((2 * k + 3)‼ : ℝ) / (6 * lam ^ (k + 2))| ≤
        K / t := by
  set s := Real.sqrt lam with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hlam
  have hs : lam = s ^ 2 := (Real.sq_sqrt hlam.le).symm
  clear_value s
  subst hs
  obtain ⟨T, hT1, hJ0bd⟩ := J_0_eventually_bounded hlam hgamma hdisc
  obtain ⟨K₁, hK₁, hd1⟩ := J_odd_delta hlam hgamma hdisc k
  obtain ⟨K₀, hK₀, hd0⟩ := J0_delta_order1 hlam hgamma hdisc
  set c := Real.sqrt (2 * Real.pi) with hc_def
  have hc_pos : 0 < c := Real.sqrt_pos.mpr two_pi_pos
  set A := cubicScale (s ^ 2) alpha with hA_def
  set D : ℝ := ((2 * k + 3)‼ : ℝ) with hD
  refine ⟨2 / c * (K₁ + |-(A * D)| * K₀) / s ^ (2 * k + 1), T, by positivity, hT1,
    fun {t} ht ↦ ?_⟩
  have ht1 : 1 ≤ t := hT1.trans ht
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsne : s ≠ 0 := hs_pos.ne'
  have hcne : c ≠ 0 := hc_pos.ne'
  obtain ⟨hJ0_lo, _⟩ := hJ0bd ht
  have hJ0_pos : 0 < J_n (s ^ 2) alpha gamma 0 t := lt_of_lt_of_le (by positivity) hJ0_lo
  have hmom := sqrt_pow_mul_moment_eq hlam hgamma hdisc (2 * k + 1) ht0
  have hsq : Real.sqrt (s ^ 2 * t) = s * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs_pos.le]
  rw [hsq, eq_div_iff hJ0_pos.ne'] at hmom
  set E := Laplace.gibbsExpectation (anharmonicPotential (s ^ 2) alpha gamma) t
    (fun x ↦ x ^ (2 * k + 1)) with hE
  set J0 := J_n (s ^ 2) alpha gamma 0 t with hJ0
  set J := J_n (s ^ 2) alpha gamma (2 * k + 1) t with hJ
  have hbridge : t ^ (k + 1) * E = (Real.sqrt t * J / J0) / s ^ (2 * k + 1) := by
    rw [eq_div_iff (by positivity), eq_div_iff hJ0_pos.ne', ← hmom]
    have hsq2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
    conv_lhs => rw [← hsq2]
    ring
  have hX : |Real.sqrt t * J - (-(A * D * c))| ≤ K₁ / t := by
    have := hd1 ht1
    rwa [sub_neg_eq_add]
  have hratio := ratio_rate_order1 ht0 hc_pos hJ0_lo hX (hd0 ht1)
  have hpc : -(A * D * c) / c = -(A * D) := by field_simp
  rw [hpc] at hratio
  rw [hbridge]
  have key : Real.sqrt t * J / J0 / s ^ (2 * k + 1) + alpha * D / (6 * (s ^ 2) ^ (k + 2)) =
      (Real.sqrt t * J / J0 - -(A * D)) / s ^ (2 * k + 1) := by
    rw [hA_def]
    unfold cubicScale
    rw [Real.sqrt_sq hs_pos.le]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < s ^ (2 * k + 1))]
  calc |Real.sqrt t * J / J0 - -(A * D)| / s ^ (2 * k + 1)
      ≤ (2 / c * (K₁ + |-(A * D)| * K₀) / t) / s ^ (2 * k + 1) :=
        div_le_div_of_nonneg_right hratio (by positivity)
    _ = 2 / c * (K₁ + |-(A * D)| * K₀) / s ^ (2 * k + 1) / t := by ring

/-- **All odd moments at their leading order**: `t^{k+1}⟨x^{2k+1}⟩ → −α(2k+3)‼/(6λ^{k+2})`. -/
theorem oddMoment_anharmonic_asymptotic (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    Tendsto (fun t : ℝ => t ^ (k + 1) *
        Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
          (fun x ↦ x ^ (2 * k + 1))) atTop
      (𝓝 (-(alpha * ((2 * k + 3)‼ : ℝ) / (6 * lam ^ (k + 2))))) := by
  obtain ⟨K, T, hK, hT, h⟩ := oddMoment_anharmonic_rate hlam hgamma hdisc k
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hK0 : Tendsto (fun t : ℝ => K / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hK0
  filter_upwards [eventually_ge_atTop T] with t ht
  rw [Real.norm_eq_abs, sub_neg_eq_add]
  exact h ht

end Laplace.OneD
