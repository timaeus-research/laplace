/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.MonomialPotential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Excess kurtosis (connected 4-point function) of the even-monomial Gibbs weight

The fourth-cumulant analogue of `monomial_variance_even`. Against the symmetric
reference weight `exp(-t·x^(2k)/(2k)!)` the mean of `x` vanishes, so the excess
kurtosis of `x` is the connected four-point function `⟨x⁴⟩ - 3⟨x²⟩²`. In Gamma
closed form it is a common power of `(2k)!/t` times a `k`-dependent constant:

`⟨x⁴⟩ - 3⟨x²⟩² = ((2k)!/t)^(2/k) · (Γ(5/(2k))/Γ(1/(2k)) - 3·(Γ(3/(2k))/Γ(1/(2k)))²)`.

For the Gaussian reference (`k = 1`) the bracket is `3/4 - 3·(1/2)² = 0`, recovering
the vanishing excess kurtosis of a Gaussian. The proof mirrors `monomial_variance_even`:
substitute the even-moment closed form `gibbsExpectation_kthPotential_even` at `j = 2`
and `j = 1`, split the common power via `Real.rpow_add`, and finish by `ring`.
-/

open Real MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.OneD

open Laplace

/-- **Excess kurtosis of the pure even-monomial Gibbs weight.** The connected
four-point function `⟨x⁴⟩ - 3⟨x²⟩²` of `x` against `exp(-t·x^(2k)/(2k)!)`, as a
`Gamma`-ratio constant scaled by the common power `((2k)!/t)^(2/k)`. Vanishes for
the Gaussian reference `k = 1`. -/
theorem monomial_excess_kurtosis
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
        - 3 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 2 =
      ((Nat.factorial (2 * k) : ℝ) / t) ^ ((2 : ℝ) / (k : ℝ)) *
        (Real.Gamma ((2 * 2 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
              Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) -
            3 * (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
              Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) ^ 2) := by
  rw [show (fun x : ℝ ↦ x ^ 4) = (fun x : ℝ ↦ x ^ (2 * 2)) from rfl,
    show (fun x : ℝ ↦ x ^ 2) = (fun x : ℝ ↦ x ^ (2 * 1)) from rfl,
    gibbsExpectation_kthPotential_even hk 2 ht,
    gibbsExpectation_kthPotential_even hk 1 ht]
  have hfac_t_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) / t :=
    div_pos (by exact_mod_cast Nat.factorial_pos _) ht
  have hpow : ((Nat.factorial (2 * k) : ℝ) / t) ^ ((2 : ℝ) / (k : ℝ)) =
      (((Nat.factorial (2 * k) : ℝ) / t) ^ ((1 : ℝ) / (k : ℝ))) ^ 2 := by
    rw [sq, ← Real.rpow_add hfac_t_pos]
    congr 1
    ring
  push_cast
  rw [hpow]
  ring

/-- Constant prefactor of the excess-kurtosis power law:
`K(k) := (2k)!^(2/k) · (Γ(5/(2k))/Γ(1/(2k)) - 3(Γ(3/(2k))/Γ(1/(2k)))²)`. -/
noncomputable def kurtosisConst (k : ℕ) : ℝ :=
  ((Nat.factorial (2 * k) : ℝ)) ^ ((2 : ℝ) / (k : ℝ)) *
    (Real.Gamma ((2 * 2 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
          Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) -
        3 * (Real.Gamma ((2 * 1 + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
          Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) ^ 2)

/-- **Excess kurtosis in `const × t^(-...)` form.** For `k ≥ 1` and `t > 0`, the
connected four-point function equals `K(k) · t^(-2/k)` exactly. -/
theorem monomial_excess_kurtosis_eq_const_mul_rpow
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
        - 3 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 2 =
      kurtosisConst k * t ^ (-((2 : ℝ) / (k : ℝ))) := by
  rw [monomial_excess_kurtosis hk ht]
  unfold kurtosisConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  have hfac_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k) : ℝ)) := by positivity
  rw [Real.div_rpow hfac_nonneg ht_le, Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` for the excess kurtosis.** Multiplied by `t^(2/k)`, the
connected four-point function tends to `K(k)` as `t → ∞`. -/
theorem monomial_excess_kurtosis_rescaled_tendsto
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun t : ℝ =>
        t ^ ((2 : ℝ) / (k : ℝ)) *
        (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
          - 3 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 2))
      atTop (𝓝 (kurtosisConst k)) := by
  have hEq : (fun t : ℝ =>
      t ^ ((2 : ℝ) / (k : ℝ)) *
      (gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
        - 3 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 2))
    =ᶠ[atTop] fun _ => kurtosisConst k := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [monomial_excess_kurtosis_eq_const_mul_rpow hk ht]
    rw [show t ^ ((2 : ℝ) / (k : ℝ)) *
            (kurtosisConst k * t ^ (-((2 : ℝ) / (k : ℝ))))
          = kurtosisConst k *
            (t ^ ((2 : ℝ) / (k : ℝ)) * t ^ (-((2 : ℝ) / (k : ℝ)))) by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact tendsto_const_nhds.congr' hEq.symm

/-- **Asymptotic equivalence for the excess kurtosis.** The connected four-point
function is asymptotically equivalent at `atTop` to `K(k) · t^(-2/k)` — indeed
exactly equal to it for every `t > 0`. -/
theorem monomial_excess_kurtosis_isEquivalent_rpow
    {k : ℕ} (hk : 1 ≤ k) :
    (fun t : ℝ =>
        gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 4)
          - 3 * gibbsExpectation (kthPotential k) t (fun x ↦ x ^ 2) ^ 2)
      ~[atTop]
      (fun t : ℝ => kurtosisConst k * t ^ (-((2 : ℝ) / (k : ℝ)))) := by
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (monomial_excess_kurtosis_eq_const_mul_rpow hk ht).symm

end Laplace.OneD
