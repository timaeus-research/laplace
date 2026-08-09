/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.IntegralRemainder
import Laplace.OneD.JnSecondOrder

/-!
# Second-order Gibbs moment rates (gamma-rung programme, stage 3)

The moment expansions feeding the fourth-cumulant assembly. From the
second-order `J_n` asymptotics and the bridge identities
`t^(r/2)·⟨x^r⟩ = J_r/(√λ^r·J_0)`, the third moment's leading rate
(`thirdMoment_anharmonic_rate`) follows from the first-order machinery,
while the second and fourth moments get their `1/t`-relative corrections
(`secondMoment_anharmonic_order2_rate`,
`fourthMoment_anharmonic_order2_rate`) whose coefficients
`(45A² - 12B)/λ` and `(450A² - 96B)/λ²` carry the gamma-rung's payload.
The key algebraic fact in each assembly is the exact cancellation of the
`1/t` term in `J_r - (leading + coeff/t)·J_0`, leaving an error of order
`1/(t√t)` by the stage-2 bounds.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- Bridge: `t·⟨x²⟩ = J₂/(λ·J₀)`. -/
private lemma secondMoment_J_form_exact
    {lam alpha gamma : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht : 0 < t)
    (hJ0_ne : J_n lam alpha gamma 0 t ≠ 0) :
    t * Laplace.gibbsExpectation
      (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 2) =
    J_n lam alpha gamma 2 t / (lam * J_n lam alpha gamma 0 t) := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 :=
    (Real.sqrt_pos.mpr hlamt).ne'
  unfold Laplace.gibbsExpectation Laplace.partitionFunction
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x))
    with hZ_def
  set I2 := ∫ x : ℝ, x ^ 2 *
    Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hI2_def
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have h2 := I_n_J_n_relation lam alpha gamma 2 hlam ht
  rw [show (0 + 1 : ℕ) = 1 from rfl, pow_one] at h0
  simp only [pow_zero, one_mul] at h0
  have hZ_eq : Real.sqrt (lam * t) * Z = J_n lam alpha gamma 0 t := by
    unfold J_n; simp only [pow_zero, one_mul]; exact h0
  have hI2_eq : Real.sqrt (lam * t) ^ (2 + 1) * I2 =
      J_n lam alpha gamma 2 t := by
    unfold J_n; exact h2
  have hsq : Real.sqrt (lam * t) ^ 2 = lam * t := Real.sq_sqrt hlamt.le
  have hZ_sub : Z = J_n lam alpha gamma 0 t / Real.sqrt (lam * t) := by
    rw [eq_div_iff hsqrt_lamt_ne, mul_comm]; exact hZ_eq
  have hI2_sub : I2 = J_n lam alpha gamma 2 t /
      (Real.sqrt (lam * t) ^ 3) := by
    rw [eq_div_iff (by positivity : Real.sqrt (lam * t) ^ 3 ≠ 0), mul_comm]
    exact hI2_eq
  rw [hZ_sub, hI2_sub]
  set slt : ℝ := Real.sqrt (lam * t) with hslt_def
  have hslt2 : slt ^ 2 = lam * t := hsq
  have hslt_ne : slt ≠ 0 := hsqrt_lamt_ne
  rw [show slt ^ 3 = (lam * t) * slt from by rw [← hslt2]; ring]
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  field_simp

/-- Bridge: `t²·⟨x⁴⟩ = J₄/(λ²·J₀)`. -/
private lemma fourthMoment_J_form_exact
    {lam alpha gamma : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht : 0 < t)
    (hJ0_ne : J_n lam alpha gamma 0 t ≠ 0) :
    t ^ 2 * Laplace.gibbsExpectation
      (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 4) =
    J_n lam alpha gamma 4 t / (lam ^ 2 * J_n lam alpha gamma 0 t) := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 :=
    (Real.sqrt_pos.mpr hlamt).ne'
  unfold Laplace.gibbsExpectation Laplace.partitionFunction
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x))
    with hZ_def
  set I4 := ∫ x : ℝ, x ^ 4 *
    Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hI4_def
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have h4 := I_n_J_n_relation lam alpha gamma 4 hlam ht
  rw [show (0 + 1 : ℕ) = 1 from rfl, pow_one] at h0
  simp only [pow_zero, one_mul] at h0
  have hZ_eq : Real.sqrt (lam * t) * Z = J_n lam alpha gamma 0 t := by
    unfold J_n; simp only [pow_zero, one_mul]; exact h0
  have hI4_eq : Real.sqrt (lam * t) ^ (4 + 1) * I4 =
      J_n lam alpha gamma 4 t := by
    unfold J_n; exact h4
  have hsq : Real.sqrt (lam * t) ^ 2 = lam * t := Real.sq_sqrt hlamt.le
  have hZ_sub : Z = J_n lam alpha gamma 0 t / Real.sqrt (lam * t) := by
    rw [eq_div_iff hsqrt_lamt_ne, mul_comm]; exact hZ_eq
  have hI4_sub : I4 = J_n lam alpha gamma 4 t /
      (Real.sqrt (lam * t) ^ 5) := by
    rw [eq_div_iff (by positivity : Real.sqrt (lam * t) ^ 5 ≠ 0), mul_comm]
    exact hI4_eq
  rw [hZ_sub, hI4_sub]
  set slt : ℝ := Real.sqrt (lam * t) with hslt_def
  have hslt2 : slt ^ 2 = lam * t := hsq
  have hslt_ne : slt ≠ 0 := hsqrt_lamt_ne
  rw [show slt ^ 5 = ((lam * t) * (lam * t)) * slt from by
    rw [show ((lam * t) * (lam * t) : ℝ) = slt ^ 2 * slt ^ 2 from by
      rw [hslt2]]
    ring]
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  field_simp

/-- Bridge: `t²·⟨x³⟩ = √t·J₃/(√λ³·J₀)`. -/
private lemma thirdMoment_J_form_exact
    {lam alpha gamma : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht : 0 < t)
    (hJ0_ne : J_n lam alpha gamma 0 t ≠ 0) :
    t ^ 2 * Laplace.gibbsExpectation
      (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 3) =
    Real.sqrt t * J_n lam alpha gamma 3 t /
      (Real.sqrt lam ^ 3 * J_n lam alpha gamma 0 t) := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 :=
    (Real.sqrt_pos.mpr hlamt).ne'
  have hsl_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hst_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  unfold Laplace.gibbsExpectation Laplace.partitionFunction
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x))
    with hZ_def
  set I3 := ∫ x : ℝ, x ^ 3 *
    Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hI3_def
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have h3 := I_n_J_n_relation lam alpha gamma 3 hlam ht
  rw [show (0 + 1 : ℕ) = 1 from rfl, pow_one] at h0
  simp only [pow_zero, one_mul] at h0
  have hZ_eq : Real.sqrt (lam * t) * Z = J_n lam alpha gamma 0 t := by
    unfold J_n; simp only [pow_zero, one_mul]; exact h0
  have hI3_eq : Real.sqrt (lam * t) ^ (3 + 1) * I3 =
      J_n lam alpha gamma 3 t := by
    unfold J_n; exact h3
  have hZ_sub : Z = J_n lam alpha gamma 0 t / Real.sqrt (lam * t) := by
    rw [eq_div_iff hsqrt_lamt_ne, mul_comm]; exact hZ_eq
  have hI3_sub : I3 = J_n lam alpha gamma 3 t /
      (Real.sqrt (lam * t) ^ 4) := by
    rw [eq_div_iff (by positivity : Real.sqrt (lam * t) ^ 4 ≠ 0), mul_comm]
    exact hI3_eq
  rw [hZ_sub, hI3_sub, Real.sqrt_mul hlam.le t]
  set sl : ℝ := Real.sqrt lam with hsl_def
  set st : ℝ := Real.sqrt t with hst_def2
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  have hst2 : st ^ 2 = t := Real.sq_sqrt ht.le
  have hsl_ne : sl ≠ 0 := hsl_pos.ne'
  have hst_ne : st ≠ 0 := hst_pos.ne'
  have hT : t = st * st := by rw [← sq]; exact hst2.symm
  rw [hT]
  have hL : lam = sl * sl := by rw [← sq]; exact hsl2.symm
  rw [hL]
  field_simp

/-! ## Deltas: `J_n` expansions with evaluated Gaussian constants -/

/-- `J₀` delta: `|J₀ - c·(1 + (15A²/2 - 3B)/t)| ≤ K/(t√t)` with
`c = √(2π)`. -/
private lemma J0_delta_order2 {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 0 t - Real.sqrt (2 * Real.pi) *
        (1 + (15 * cubicScale lam alpha ^ 2 / 2 -
          3 * quarticScale lam gamma) / t)| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic_order2 hlam hgamma hdisc 0
  refine ⟨K, hK, ?_⟩
  intro t ht
  have h := hb ht
  have hm0 : (∫ u : ℝ, u ^ 0 * Real.exp (-(u ^ 2) / 2)) =
      Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 0
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm3 : (∫ u : ℝ, u ^ (0 + 3) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd 1
    norm_num at h' ⊢
    exact h'
  have hm4 : (∫ u : ℝ, u ^ (0 + 4) * Real.exp (-(u ^ 2) / 2)) =
      3 * Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 2
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm6 : (∫ u : ℝ, u ^ (0 + 6) * Real.exp (-(u ^ 2) / 2)) =
      15 * Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 3
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  rw [hm0, hm3, hm4, hm6] at h
  have harg : Real.sqrt (2 * Real.pi) - cubicScale lam alpha /
        Real.sqrt t * 0 - quarticScale lam gamma / t *
        (3 * Real.sqrt (2 * Real.pi)) + cubicScale lam alpha ^ 2 /
        (2 * t) * (15 * Real.sqrt (2 * Real.pi)) =
      Real.sqrt (2 * Real.pi) * (1 + (15 * cubicScale lam alpha ^ 2 / 2 -
        3 * quarticScale lam gamma) / t) := by
    field_simp
    ring
  rw [harg] at h
  have hJ : J_n lam alpha gamma 0 t = ∫ u : ℝ, u ^ 0 *
      Real.exp (-(u ^ 2) / 2) *
      Real.exp (-rescaledPerturbation lam alpha gamma t u) := rfl
  rw [hJ]
  exact h

/-- `J₂` delta: `|J₂ - c·(1 + (105A²/2 - 15B)/t)| ≤ K/(t√t)`. -/
private lemma J2_delta_order2 {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 2 t - Real.sqrt (2 * Real.pi) *
        (1 + (105 * cubicScale lam alpha ^ 2 / 2 -
          15 * quarticScale lam gamma) / t)| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic_order2 hlam hgamma hdisc 2
  refine ⟨K, hK, ?_⟩
  intro t ht
  have h := hb ht
  have hm2 : (∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2)) =
      Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 1
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm5 : (∫ u : ℝ, u ^ (2 + 3) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd 2
    norm_num at h' ⊢
    exact h'
  have hm6 : (∫ u : ℝ, u ^ (2 + 4) * Real.exp (-(u ^ 2) / 2)) =
      15 * Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 3
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm8 : (∫ u : ℝ, u ^ (2 + 6) * Real.exp (-(u ^ 2) / 2)) =
      105 * Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 4
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  rw [hm2, hm5, hm6, hm8] at h
  have harg : Real.sqrt (2 * Real.pi) - cubicScale lam alpha /
        Real.sqrt t * 0 - quarticScale lam gamma / t *
        (15 * Real.sqrt (2 * Real.pi)) + cubicScale lam alpha ^ 2 /
        (2 * t) * (105 * Real.sqrt (2 * Real.pi)) =
      Real.sqrt (2 * Real.pi) * (1 + (105 * cubicScale lam alpha ^ 2 / 2 -
        15 * quarticScale lam gamma) / t) := by
    field_simp
    ring
  rw [harg] at h
  exact h

/-- `J₄` delta: `|J₄ - c·(3 + (945A²/2 - 105B)/t)| ≤ K/(t√t)`. -/
private lemma J4_delta_order2 {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 4 t - Real.sqrt (2 * Real.pi) *
        (3 + (945 * cubicScale lam alpha ^ 2 / 2 -
          105 * quarticScale lam gamma) / t)| ≤ K / (t * Real.sqrt t) := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic_order2 hlam hgamma hdisc 4
  refine ⟨K, hK, ?_⟩
  intro t ht
  have h := hb ht
  have hm4 : (∫ u : ℝ, u ^ 4 * Real.exp (-(u ^ 2) / 2)) =
      3 * Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 2
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm7 : (∫ u : ℝ, u ^ (4 + 3) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd 3
    norm_num at h' ⊢
    exact h'
  have hm8 : (∫ u : ℝ, u ^ (4 + 4) * Real.exp (-(u ^ 2) / 2)) =
      105 * Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 4
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm10 : (∫ u : ℝ, u ^ (4 + 6) * Real.exp (-(u ^ 2) / 2)) =
      945 * Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 5
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  rw [hm4, hm7, hm8, hm10] at h
  have harg : 3 * Real.sqrt (2 * Real.pi) - cubicScale lam alpha /
        Real.sqrt t * 0 - quarticScale lam gamma / t *
        (105 * Real.sqrt (2 * Real.pi)) + cubicScale lam alpha ^ 2 /
        (2 * t) * (945 * Real.sqrt (2 * Real.pi)) =
      Real.sqrt (2 * Real.pi) * (3 + (945 * cubicScale lam alpha ^ 2 / 2 -
        105 * quarticScale lam gamma) / t) := by
    field_simp
    ring
  rw [harg] at h
  exact h

/-- `J₃` delta (first order suffices):
`|J₃ + 15A·c/√t| ≤ K/t`. -/
private lemma J3_delta {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 3 t + 15 * cubicScale lam alpha *
        Real.sqrt (2 * Real.pi) / Real.sqrt t| ≤ K / t := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic hlam hgamma hdisc 3
  refine ⟨K, hK, ?_⟩
  intro t ht
  have h := hb ht
  have hm3 : (∫ u : ℝ, u ^ 3 * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd 1
    norm_num at h' ⊢
    exact h'
  have hm6 : (∫ u : ℝ, u ^ (3 + 3) * Real.exp (-(u ^ 2) / 2)) =
      15 * Real.sqrt (2 * Real.pi) := by
    have h' := integral_pow_mul_exp_neg_sq_half 3
    norm_num [Nat.doubleFactorial] at h' ⊢
    exact h'
  have hm7 : (∫ u : ℝ, u ^ (3 + 4) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd 3
    norm_num at h' ⊢
    exact h'
  rw [hm3, hm6, hm7] at h
  have harg : (0 : ℝ) - cubicScale lam alpha / Real.sqrt t *
        (15 * Real.sqrt (2 * Real.pi)) - quarticScale lam gamma / t * 0 =
      -(15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
        Real.sqrt t) := by
    ring
  rw [harg, sub_neg_eq_add] at h
  exact h

end Laplace.OneD
