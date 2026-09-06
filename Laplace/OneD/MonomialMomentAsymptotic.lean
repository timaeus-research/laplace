/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.MonomialPotential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# 1D even-monomial Gibbs-moment asymptotic

The one-dimensional base of the generic-`(k₁, k₂)` 2D moment lift
(`Laplace/TwoD/KthKthMomentAsymptotic.lean`), which assumed this fact implicitly.
For the symmetric reference weight `exp(-t·x^(2k)/(2k)!)` the even moment
`⟨x^(2j)⟩_t` is *exactly* a pure power law in `t`:

`⟨x^(2j)⟩_t = C(k, j) · t^(-j/k)`,   `C(k, j) := (2k)!^(j/k) · Γ((2j+1)/(2k)) / Γ(1/(2k))`.

so its asymptotic equivalence at `atTop` to that power law is immediate. This is
the single-factor version of `KthKthMomentAsymptotic`, following the same four-step
lift pattern (closed form → `const × t^(-...)` → rescaled `Tendsto` → `IsEquivalent`).
-/

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.OneD

open Laplace

/-- Constant prefactor of the 1D even-monomial moment asymptotic:
`C(k, j) := (2k)!^(j/k) · Γ((2j+1)/(2k)) / Γ(1/(2k))`. -/
noncomputable def kthMomentConst (k j : ℕ) : ℝ :=
  ((Nat.factorial (2 * k) : ℝ)) ^ ((j : ℝ) / (k : ℝ)) *
    (Real.Gamma ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
      Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)))

/-- **Exact closed form of the 1D even moment in `const × t^(-...)` form.**
For `k ≥ 1` and `t > 0`, `⟨x^(2j)⟩_t = C(k, j) · t^(-j/k)`. -/
theorem gibbsExpectation_kthPotential_even_eq_const_mul_rpow
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (kthPotential k) t (fun x : ℝ => x ^ (2 * j)) =
      kthMomentConst k j * t ^ (-((j : ℝ) / (k : ℝ))) := by
  rw [gibbsExpectation_kthPotential_even hk j ht]
  unfold kthMomentConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  have hfac_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k) : ℝ)) := by positivity
  rw [Real.div_rpow hfac_nonneg ht_le, Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` for the 1D even moment.** Multiplied by `t^(j/k)`, the
moment tends to `C(k, j)` as `t → ∞`. -/
theorem gibbsExpectation_kthPotential_even_rescaled_tendsto
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    Tendsto (fun t : ℝ =>
        t ^ ((j : ℝ) / (k : ℝ)) *
        gibbsExpectation (kthPotential k) t (fun x : ℝ => x ^ (2 * j)))
      atTop (𝓝 (kthMomentConst k j)) := by
  have hEq : (fun t : ℝ =>
      t ^ ((j : ℝ) / (k : ℝ)) *
      gibbsExpectation (kthPotential k) t (fun x : ℝ => x ^ (2 * j)))
    =ᶠ[atTop] fun _ => kthMomentConst k j := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [gibbsExpectation_kthPotential_even_eq_const_mul_rpow hk j ht]
    rw [show t ^ ((j : ℝ) / (k : ℝ)) *
            (kthMomentConst k j * t ^ (-((j : ℝ) / (k : ℝ))))
          = kthMomentConst k j *
            (t ^ ((j : ℝ) / (k : ℝ)) * t ^ (-((j : ℝ) / (k : ℝ)))) by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact tendsto_const_nhds.congr' hEq.symm

/-- **Asymptotic equivalence for the 1D even moment.** `⟨x^(2j)⟩_t` is asymptotically
equivalent at `atTop` to the pure power law `C(k, j) · t^(-j/k)` — indeed exactly
equal to it for every `t > 0`. -/
theorem gibbsExpectation_kthPotential_even_isEquivalent_rpow
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (fun t : ℝ => gibbsExpectation (kthPotential k) t (fun x : ℝ => x ^ (2 * j)))
      ~[atTop]
      (fun t : ℝ => kthMomentConst k j * t ^ (-((j : ℝ) / (k : ℝ)))) := by
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (gibbsExpectation_kthPotential_even_eq_const_mul_rpow hk j ht).symm

end Laplace.OneD
