import Laplace.TwoD.QuarticSextic
import Laplace.TwoD.AddSeparable
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Unnormalised numerator asymptotic for the quartic-sextic potential

For the 2D separable potential $L(x, y) = x^4/24 + y^6/720$, the
unnormalised 2D integral with a polynomial monomial weight has an
exact closed form via separability + the 1D `_moment_even` closed
forms. Pulling out the $t$-dependence,
$$
  \int\!\int x^{2j} y^{2k}\,e^{-tL(x,y)}\,dx\,dy
  = C'(j, k) \cdot t^{-((2j+1)/4 + (2k+1)/6)}
$$
with
$$
  C'(j, k) = \tfrac{1}{6}\cdot 24^{(2j+1)/4}\cdot 720^{(2k+1)/6}
    \cdot \Gamma((2j+1)/4)\cdot \Gamma((2k+1)/6).
$$

This file packages the exact reformulation as a `Tendsto` to a
constant (after rescaling by $t^{(2j+1)/4 + (2k+1)/6}$) and as an
`Asymptotics.IsEquivalent` at $\mathrm{atTop}$, mirroring V2's
moment-side packaging (`QuarticSexticMomentAsymptotic.lean`).

## Headline

* `integral_pow_pow_exp_neg_quarticSextic_eq_const_mul_rpow` — exact
  reformulation.
* `integral_pow_pow_exp_neg_quarticSextic_rescaled_tendsto` — Tendsto
  form.
* `integral_pow_pow_exp_neg_quarticSextic_isEquivalent_rpow` —
  IsEquivalent form.

## Strategy

`integral_separable_addSeparable` from `Laplace/TwoD/AddSeparable.lean`
factors the 2D numerator integral into the product of two 1D
numerator integrals. The 1D quartic and sextic numerators have exact
$\Gamma$-function closed forms (`quartic_moment_even` and
`sextic_moment_even`). After combining and rearranging via standard
`Real.rpow` algebra, the result is $C'(j, k) \cdot t^{-(\ldots)}$.
The Tendsto and IsEquivalent forms follow by V2's standard
`tendsto_congr'` / eventual-equality idiom; no new analysis is
required because the closed form is exact.
-/

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.TwoD

/-- The $t$-independent constant prefactor for the 2D quartic-sextic
unnormalised numerator integral:
$$
  C'(j, k) := \tfrac{1}{6}\cdot 24^{(2j+1)/4}\cdot 720^{(2k+1)/6}
    \cdot \Gamma((2j+1)/4)\cdot \Gamma((2k+1)/6).
$$ -/
noncomputable def quarticSexticNumeratorConst (j k : ℕ) : ℝ :=
  (1 / 6 : ℝ) *
    (24 : ℝ) ^ ((2 * j + 1 : ℝ) / 4) *
    (720 : ℝ) ^ ((2 * k + 1 : ℝ) / 6) *
    Real.Gamma ((2 * j + 1 : ℝ) / 4) *
    Real.Gamma ((2 * k + 1 : ℝ) / 6)

/-- **Exact closed form for the unnormalised 2D quartic-sextic
numerator integral (`numerator = const × t^(-...)` form).**

For the 2D potential $L(x, y) = x^4/24 + y^6/720$ at temperature
$t > 0$ and any $j, k : \mathbb N$,
$$
  \int\!\int x^{2j} y^{2k}\,e^{-tL(x,y)}\,dx\,dy
  = C'(j, k)\cdot t^{-((2j+1)/4 + (2k+1)/6)}.
$$ -/
theorem integral_pow_pow_exp_neg_quarticSextic_eq_const_mul_rpow
    (j k : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ z : ℝ × ℝ, z.1 ^ (2 * j) * z.2 ^ (2 * k) *
        Real.exp (-(t * addSeparable Laplace.OneD.quarticPotential
                                     Laplace.OneD.sexticPotential z)))
      = quarticSexticNumeratorConst j k *
        t ^ (-((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6)) := by
  rw [integral_separable_addSeparable
        (fun x : ℝ => x ^ (2 * j)) (fun y : ℝ => y ^ (2 * k))
        (Laplace.OneD.quartic_integrable_pow_pot (2 * j) ht)
        (Laplace.OneD.sextic_integrable_pow_pot (2 * k) ht)]
  have h_q : (∫ x : ℝ, x ^ (2 * j) * Real.exp (-(t * Laplace.OneD.quarticPotential x))) =
             (∫ x : ℝ, x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24))) := by
    congr 1; ext x
    rw [Laplace.OneD.quarticPotential_apply]
    congr 2; ring
  have h_s : (∫ y : ℝ, y ^ (2 * k) * Real.exp (-(t * Laplace.OneD.sexticPotential y))) =
             (∫ y : ℝ, y ^ (2 * k) * Real.exp (-(t * y ^ 6 / 720))) := by
    congr 1; ext y
    rw [Laplace.OneD.sexticPotential_apply]
    congr 2; ring
  rw [h_q, h_s,
      Laplace.OneD.quartic_moment_even j ht,
      Laplace.OneD.sextic_moment_even k ht]
  unfold quarticSexticNumeratorConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  rw [Real.div_rpow (by norm_num : (24 : ℝ) ≥ 0) ht_le,
      Real.div_rpow (by norm_num : (720 : ℝ) ≥ 0) ht_le]
  rw [show (-((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6))
          = (-((2 * j + 1 : ℝ) / 4)) + (-((2 * k + 1 : ℝ) / 6)) by ring,
      Real.rpow_add ht, Real.rpow_neg ht_le, Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` for the 2D quartic-sextic numerator integral.**

Multiplied by $t^{(2j+1)/4 + (2k+1)/6}$, the unnormalised 2D numerator
integral tends to the constant $C'(j, k)$ as $t \to \infty$. -/
theorem integral_pow_pow_exp_neg_quarticSextic_rescaled_tendsto
    (j k : ℕ) :
    Tendsto (fun t : ℝ =>
        t ^ ((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6) *
        (∫ z : ℝ × ℝ, z.1 ^ (2 * j) * z.2 ^ (2 * k) *
            Real.exp (-(t * addSeparable Laplace.OneD.quarticPotential
                                         Laplace.OneD.sexticPotential z))))
      atTop (𝓝 (quarticSexticNumeratorConst j k)) := by
  have hEq : (fun t : ℝ =>
      t ^ ((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6) *
      (∫ z : ℝ × ℝ, z.1 ^ (2 * j) * z.2 ^ (2 * k) *
          Real.exp (-(t * addSeparable Laplace.OneD.quarticPotential
                                       Laplace.OneD.sexticPotential z))))
    =ᶠ[atTop] fun _ => quarticSexticNumeratorConst j k := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [integral_pow_pow_exp_neg_quarticSextic_eq_const_mul_rpow j k ht]
    rw [show t ^ ((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6) *
            (quarticSexticNumeratorConst j k *
             t ^ (-((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6)))
          = quarticSexticNumeratorConst j k *
            (t ^ ((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6) *
             t ^ (-((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6))) by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact (tendsto_const_nhds.congr' hEq.symm)

/-- **Asymptotic equivalence for the 2D quartic-sextic numerator
integral.**

The unnormalised numerator is asymptotically equivalent at
$\mathrm{atTop}$ to the pure power-law
$C'(j, k) \cdot t^{-((2j+1)/4 + (2k+1)/6)}$. -/
theorem integral_pow_pow_exp_neg_quarticSextic_isEquivalent_rpow
    (j k : ℕ) :
    (fun t : ℝ =>
        ∫ z : ℝ × ℝ, z.1 ^ (2 * j) * z.2 ^ (2 * k) *
            Real.exp (-(t * addSeparable Laplace.OneD.quarticPotential
                                         Laplace.OneD.sexticPotential z)))
      ~[atTop]
      (fun t : ℝ => quarticSexticNumeratorConst j k *
                    t ^ (-((2 * j + 1 : ℝ) / 4 + (2 * k + 1 : ℝ) / 6))) := by
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (integral_pow_pow_exp_neg_quarticSextic_eq_const_mul_rpow j k ht).symm

end Laplace.TwoD
