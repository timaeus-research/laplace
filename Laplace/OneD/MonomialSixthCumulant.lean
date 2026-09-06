/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.MonomialPotential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Sixth cumulant of the even-monomial Gibbs weight

The next rung of the monomial cumulant ladder (`MonomialVariance` = κ₂,
`MonomialKurtosis` = κ₄). Against the symmetric weight `exp(-t·x^(2k)/(2k)!)` the
mean of `x` and all odd moments vanish, so the sixth cumulant of `x` is
`κ₆ = ⟨x⁶⟩ - 15⟨x⁴⟩⟨x²⟩ + 30⟨x²⟩³`. In Gamma closed form it is a common power of
`(2k)!/t` times a `k`-dependent constant:

`κ₆ = ((2k)!/t)^(3/k) · (r₃ - 15·r₂·r₁ + 30·r₁³)`,   `rⱼ := Γ((2j+1)/(2k))/Γ(1/(2k))`.

For the Gaussian reference (`k = 1`) the bracket is `15 - 15·3·1 + 30·1 = 0`, recovering
the vanishing sixth cumulant of a Gaussian. The file also packages the `t^(-3/k)` asymptotic
scaling, following the four-step lift pattern. The proof mirrors `MonomialKurtosis`, folding
the two extra powers `((2k)!/t)^(2/k) = (·)²` and `((2k)!/t)^(3/k) = (·)³` into the common base.
-/

open Real MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.OneD

open Laplace

/-- **Sixth cumulant of the pure even-monomial Gibbs weight.** For a symmetric weight
`κ₆ = ⟨x⁶⟩ - 15⟨x⁴⟩⟨x²⟩ + 30⟨x²⟩³`, as a `Gamma`-ratio constant scaled by the common
power `((2k)!/t)^(3/k)`. Vanishes for the Gaussian reference `k = 1`. -/
theorem monomial_sixth_cumulant
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 6)
        - 15 * (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
              * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2))
        + 30 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 3 =
      ((Nat.factorial (2 * k) : ℝ) / t) ^ ((3 : ℝ) / (k : ℝ)) *
        (Real.Gamma ((2 * 3 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
              Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
            - 15 * (Real.Gamma ((2 * 2 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
                  Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
                * (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
                  Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))))
            + 30 * (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
                  Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) ^ 3) := by
  rw [show (fun x : ℝ ↦ x ^ 6) = (fun x : ℝ ↦ x ^ (2 * 3)) from rfl,
    show (fun x : ℝ ↦ x ^ 4) = (fun x : ℝ ↦ x ^ (2 * 2)) from rfl,
    show (fun x : ℝ ↦ x ^ 2) = (fun x : ℝ ↦ x ^ (2 * 1)) from rfl,
    gibbsExpectation_kthPotential_even hk 3 ht,
    gibbsExpectation_kthPotential_even hk 2 ht,
    gibbsExpectation_kthPotential_even hk 1 ht]
  have hfac_t_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) / t :=
    div_pos (by exact_mod_cast Nat.factorial_pos _) ht
  have hpow2 : ((Nat.factorial (2 * k) : ℝ) / t) ^ ((2 : ℝ) / (k : ℝ)) =
      (((Nat.factorial (2 * k) : ℝ) / t) ^ ((1 : ℝ) / (k : ℝ))) ^ 2 := by
    rw [sq, ← Real.rpow_add hfac_t_pos]
    congr 1
    ring
  have hpow3 : ((Nat.factorial (2 * k) : ℝ) / t) ^ ((3 : ℝ) / (k : ℝ)) =
      (((Nat.factorial (2 * k) : ℝ) / t) ^ ((1 : ℝ) / (k : ℝ))) ^ 3 := by
    rw [← Real.rpow_natCast (((Nat.factorial (2 * k) : ℝ) / t) ^ ((1 : ℝ) / (k : ℝ))) 3,
      ← Real.rpow_mul hfac_t_pos.le]
    congr 1
    push_cast
    ring
  push_cast
  rw [hpow2, hpow3]
  ring

/-- Constant prefactor of the sixth-cumulant power law:
`K₆(k) := (2k)!^(3/k) · (r₃ - 15·r₂·r₁ + 30·r₁³)`. -/
noncomputable def sixthCumulantConst (k : ℕ) : ℝ :=
  ((Nat.factorial (2 * k) : ℝ)) ^ ((3 : ℝ) / (k : ℝ)) *
    (Real.Gamma ((2 * 3 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
          Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
        - 15 * (Real.Gamma ((2 * 2 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
              Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))
            * (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
              Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))))
        + 30 * (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
              Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) ^ 3)

/-- **Sixth cumulant in `const × t^(-...)` form.** For `k ≥ 1` and `t > 0`, `κ₆` equals
`K₆(k) · t^(-3/k)` exactly. -/
theorem monomial_sixth_cumulant_eq_const_mul_rpow
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 6)
        - 15 * (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
              * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2))
        + 30 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 3 =
      sixthCumulantConst k * t ^ (-((3 : ℝ) / (k : ℝ))) := by
  rw [monomial_sixth_cumulant hk ht]
  unfold sixthCumulantConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  have hfac_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k) : ℝ)) := by positivity
  rw [Real.div_rpow hfac_nonneg ht_le, Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` for the sixth cumulant.** Multiplied by `t^(3/k)`, `κ₆` tends to
`K₆(k)` as `t → ∞`. -/
theorem monomial_sixth_cumulant_rescaled_tendsto
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun t : ℝ =>
        t ^ ((3 : ℝ) / (k : ℝ)) *
        (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 6)
            - 15 * (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
                  * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2))
            + 30 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 3))
      atTop (𝓝 (sixthCumulantConst k)) := by
  have hEq : (fun t : ℝ =>
      t ^ ((3 : ℝ) / (k : ℝ)) *
      (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 6)
          - 15 * (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
                * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2))
          + 30 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 3))
    =ᶠ[atTop] fun _ => sixthCumulantConst k := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [monomial_sixth_cumulant_eq_const_mul_rpow hk ht]
    rw [show t ^ ((3 : ℝ) / (k : ℝ)) *
            (sixthCumulantConst k * t ^ (-((3 : ℝ) / (k : ℝ))))
          = sixthCumulantConst k *
            (t ^ ((3 : ℝ) / (k : ℝ)) * t ^ (-((3 : ℝ) / (k : ℝ)))) by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact tendsto_const_nhds.congr' hEq.symm

/-- **Asymptotic equivalence for the sixth cumulant.** `κ₆` is asymptotically equivalent at
`atTop` to `K₆(k) · t^(-3/k)` — indeed exactly equal to it for every `t > 0`. -/
theorem monomial_sixth_cumulant_isEquivalent_rpow
    {k : ℕ} (hk : 1 ≤ k) :
    (fun t : ℝ =>
        gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 6)
          - 15 * (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
                * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2))
          + 30 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 3)
      ~[atTop]
      (fun t : ℝ => sixthCumulantConst k * t ^ (-((3 : ℝ) / (k : ℝ)))) := by
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (monomial_sixth_cumulant_eq_const_mul_rpow hk ht).symm

end Laplace.OneD
