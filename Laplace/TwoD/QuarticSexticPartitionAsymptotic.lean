import Laplace.TwoD.QuarticSextic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# 2D partition function asymptotic for the quartic-sextic potential

For the 2D separable potential $L(x, y) = x^4/24 + y^6/720$, the
seabed lemma `partitionFunction_quarticSextic_eq` gives an exact
closed form for the 2D partition function
$Z_{2D}(t) = \int\!\int e^{-tL(x,y)}\,dx\,dy$. Pulling out the
$t$-dependence,
$$
  Z_{2D}(t) = C'' \cdot t^{-1/4 - 1/6}
$$
with
$$
  C'' := \tfrac{1}{6}\cdot 24^{1/4}\cdot 720^{1/6}
    \cdot \Gamma(1/4)\cdot \Gamma(1/6).
$$

This file packages that exact identity as a rescaled `Tendsto` (to
the constant $C''$) and as an `Asymptotics.IsEquivalent` at
$\mathrm{atTop}$. Completes the V2/Z1/Z2 triple: moment / numerator /
partition all with matching asymptotic packagings.

## Headline

* `partitionFunction_quarticSextic_eq_const_mul_rpow` — exact
  reformulation.
* `partitionFunction_quarticSextic_rescaled_tendsto` — Tendsto form.
* `partitionFunction_quarticSextic_isEquivalent_rpow` — IsEquivalent.

## Strategy

`partitionFunction_quarticSextic_eq` in
`Laplace/TwoD/QuarticSextic.lean` supplies the closed form
$(1/2)(24/t)^{1/4}\Gamma(1/4) \cdot (1/3)(720/t)^{1/6}\Gamma(1/6)$.
Pure `Real.rpow` algebra collects the $t$-pieces into a single
$t^{-1/4 - 1/6}$, identical to V2/Z1's template.
-/

open Real MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.TwoD

/-- The $t$-independent constant prefactor for the 2D quartic-sextic
partition function:
$$
  C'' := \tfrac{1}{6}\cdot 24^{1/4}\cdot 720^{1/6}
    \cdot \Gamma(1/4)\cdot \Gamma(1/6).
$$ -/
noncomputable def quarticSexticPartitionConst : ℝ :=
  (1 / 6 : ℝ) *
    (24 : ℝ) ^ ((1 : ℝ) / 4) *
    (720 : ℝ) ^ ((1 : ℝ) / 6) *
    Real.Gamma ((1 : ℝ) / 4) *
    Real.Gamma ((1 : ℝ) / 6)

/-- **Exact closed form for the 2D quartic-sextic partition function
in `const × t^(-...)` form.**

For the 2D potential $L(x, y) = x^4/24 + y^6/720$ at $t > 0$,
$$
  Z_{2D}(t) = C''\cdot t^{-1/4 - 1/6}.
$$ -/
theorem partitionFunction_quarticSextic_eq_const_mul_rpow
    {t : ℝ} (ht : 0 < t) :
    partitionFunction (addSeparable Laplace.OneD.quarticPotential
                                    Laplace.OneD.sexticPotential) t
      = quarticSexticPartitionConst *
        t ^ (-((1 : ℝ) / 4 + (1 : ℝ) / 6)) := by
  rw [partitionFunction_quarticSextic_eq ht]
  unfold quarticSexticPartitionConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  rw [Real.div_rpow (by norm_num : (24 : ℝ) ≥ 0) ht_le,
      Real.div_rpow (by norm_num : (720 : ℝ) ≥ 0) ht_le]
  rw [show (-((1 : ℝ) / 4 + (1 : ℝ) / 6))
          = (-((1 : ℝ) / 4)) + (-((1 : ℝ) / 6)) by ring,
      Real.rpow_add ht, Real.rpow_neg ht_le, Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` for the 2D quartic-sextic partition function.**

Multiplied by $t^{1/4 + 1/6}$, the partition function tends to the
constant $C''$ as $t \to \infty$. -/
theorem partitionFunction_quarticSextic_rescaled_tendsto :
    Tendsto (fun t : ℝ =>
        t ^ ((1 : ℝ) / 4 + (1 : ℝ) / 6) *
        partitionFunction (addSeparable Laplace.OneD.quarticPotential
                                        Laplace.OneD.sexticPotential) t)
      atTop (𝓝 quarticSexticPartitionConst) := by
  have hEq : (fun t : ℝ =>
      t ^ ((1 : ℝ) / 4 + (1 : ℝ) / 6) *
      partitionFunction (addSeparable Laplace.OneD.quarticPotential
                                      Laplace.OneD.sexticPotential) t)
    =ᶠ[atTop] fun _ => quarticSexticPartitionConst := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [partitionFunction_quarticSextic_eq_const_mul_rpow ht]
    rw [show t ^ ((1 : ℝ) / 4 + (1 : ℝ) / 6) *
            (quarticSexticPartitionConst *
             t ^ (-((1 : ℝ) / 4 + (1 : ℝ) / 6)))
          = quarticSexticPartitionConst *
            (t ^ ((1 : ℝ) / 4 + (1 : ℝ) / 6) *
             t ^ (-((1 : ℝ) / 4 + (1 : ℝ) / 6))) by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact (tendsto_const_nhds.congr' hEq.symm)

/-- **Asymptotic equivalence for the 2D quartic-sextic partition
function.**

The partition function is asymptotically equivalent at
$\mathrm{atTop}$ to the pure power-law $C''\cdot t^{-1/4 - 1/6}$. -/
theorem partitionFunction_quarticSextic_isEquivalent_rpow :
    (fun t : ℝ =>
        partitionFunction (addSeparable Laplace.OneD.quarticPotential
                                        Laplace.OneD.sexticPotential) t)
      ~[atTop]
      (fun t : ℝ => quarticSexticPartitionConst *
                    t ^ (-((1 : ℝ) / 4 + (1 : ℝ) / 6))) := by
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (partitionFunction_quarticSextic_eq_const_mul_rpow ht).symm

end Laplace.TwoD
