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

end Laplace.OneD
