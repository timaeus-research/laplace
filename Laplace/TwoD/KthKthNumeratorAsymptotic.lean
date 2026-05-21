import Laplace.OneD.MonomialPotential
import Laplace.TwoD.AddSeparable
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Generic 2D numerator asymptotic for separable monomial potentials

For the 2D separable potential $L(x, y) = L_{k_1}(x) + L_{k_2}(y)$
with $L_k(z) = z^{2k}/(2k)!$ and $k_1, k_2 \ge 1$, this file
establishes the unnormalised numerator asymptotic:

* `integral_pow_pow_exp_neg_kthKth_eq_const_mul_rpow` — exact closed
  form $C'(k_1, k_2, j_1, j_2) \cdot t^{-(2j_1+1)/(2k_1) - (2j_2+1)/(2k_2)}$.
* `integral_pow_pow_exp_neg_kthKth_rescaled_tendsto` — Tendsto form.
* `integral_pow_pow_exp_neg_kthKth_isEquivalent_rpow` — IsEquivalent
  form.

Lifts the quartic-sextic V1 tide
(`Laplace/TwoD/QuarticSexticNumeratorAsymptotic.lean`) from
$(k_1, k_2) = (2, 3)$ to parametric $(k_1, k_2)$. Mirror-shape
sibling of `KthKthMomentAsymptotic.lean`.
-/

open Real MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.TwoD

/-- Composite constant prefactor for the generic-$(k_1, k_2)$ 2D
separable monomial unnormalised numerator:
$$
  C'(k_1, k_2, j_1, j_2) :=
    \tfrac{1}{k_1 k_2}\cdot (2k_1)!^{(2j_1+1)/(2k_1)}\cdot
    (2k_2)!^{(2j_2+1)/(2k_2)}\cdot
    \Gamma((2j_1+1)/(2k_1))\cdot \Gamma((2j_2+1)/(2k_2)).
$$ -/
noncomputable def kthKthNumeratorConst (k₁ k₂ j₁ j₂ : ℕ) : ℝ :=
  (1 / ((k₁ : ℝ) * (k₂ : ℝ))) *
    ((Nat.factorial (2 * k₁) : ℝ)) ^
      ((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) *
    ((Nat.factorial (2 * k₂) : ℝ)) ^
      ((2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
    Real.Gamma ((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) *
    Real.Gamma ((2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))

/-- **Exact closed form for the unnormalised 2D kth-kth numerator
integral.** For $k_1, k_2 \ge 1$, $j_1, j_2 : \mathbb N$, and $t > 0$,
the 2D integral is $C'(k_1, k_2, j_1, j_2) \cdot
t^{-(2j_1+1)/(2k_1) - (2j_2+1)/(2k_2)}$. -/
theorem integral_pow_pow_exp_neg_kthKth_eq_const_mul_rpow
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ j₂ : ℕ)
    {t : ℝ} (ht : 0 < t) :
    (∫ z : ℝ × ℝ, z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂) *
        Real.exp (-(t * addSeparable (Laplace.OneD.kthPotential k₁)
                                     (Laplace.OneD.kthPotential k₂) z)))
      = kthKthNumeratorConst k₁ k₂ j₁ j₂ *
        t ^ (-((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
              (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))) := by
  rw [integral_separable_addSeparable
        (fun x : ℝ => x ^ (2 * j₁)) (fun y : ℝ => y ^ (2 * j₂))
        (Laplace.OneD.kth_integrable_pow_pot (k := k₁) hk₁ (2 * j₁) ht)
        (Laplace.OneD.kth_integrable_pow_pot (k := k₂) hk₂ (2 * j₂) ht)]
  -- Each 1D integral matches kth_moment_even modulo unfolding kthPotential.
  have h_k1 : (∫ x : ℝ, x ^ (2 * j₁) *
                Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) =
              (∫ x : ℝ, x ^ (2 * j₁) *
                Real.exp (-(t * x ^ (2 * k₁) / (Nat.factorial (2 * k₁) : ℝ)))) := by
    congr 1; ext x
    rw [Laplace.OneD.kthPotential_apply]
    congr 2; ring
  have h_k2 : (∫ y : ℝ, y ^ (2 * j₂) *
                Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) =
              (∫ y : ℝ, y ^ (2 * j₂) *
                Real.exp (-(t * y ^ (2 * k₂) / (Nat.factorial (2 * k₂) : ℝ)))) := by
    congr 1; ext y
    rw [Laplace.OneD.kthPotential_apply]
    congr 2; ring
  rw [h_k1, h_k2,
      Laplace.OneD.kth_moment_even hk₁ j₁ ht,
      Laplace.OneD.kth_moment_even hk₂ j₂ ht]
  unfold kthKthNumeratorConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  have h_fact₁_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k₁) : ℝ)) := by positivity
  have h_fact₂_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k₂) : ℝ)) := by positivity
  rw [Real.div_rpow h_fact₁_nonneg ht_le,
      Real.div_rpow h_fact₂_nonneg ht_le]
  rw [show (-((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
              (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))
          = (-((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ))) +
            (-((2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))) by ring,
      Real.rpow_add ht,
      Real.rpow_neg ht_le,
      Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` for the unnormalised 2D kth-kth numerator.**
Multiplied by $t^{(2j_1+1)/(2k_1) + (2j_2+1)/(2k_2)}$, the unnormalised
2D numerator integral tends to $C'(k_1, k_2, j_1, j_2)$ at
$\mathrm{atTop}$. -/
theorem integral_pow_pow_exp_neg_kthKth_rescaled_tendsto
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ j₂ : ℕ) :
    Tendsto (fun t : ℝ =>
        t ^ ((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
             (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
        (∫ z : ℝ × ℝ, z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂) *
            Real.exp (-(t * addSeparable (Laplace.OneD.kthPotential k₁)
                                         (Laplace.OneD.kthPotential k₂) z))))
      atTop (𝓝 (kthKthNumeratorConst k₁ k₂ j₁ j₂)) := by
  have hEq : (fun t : ℝ =>
      t ^ ((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
           (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
      (∫ z : ℝ × ℝ, z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂) *
          Real.exp (-(t * addSeparable (Laplace.OneD.kthPotential k₁)
                                       (Laplace.OneD.kthPotential k₂) z))))
    =ᶠ[atTop] fun _ => kthKthNumeratorConst k₁ k₂ j₁ j₂ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [integral_pow_pow_exp_neg_kthKth_eq_const_mul_rpow hk₁ hk₂ j₁ j₂ ht]
    rw [show t ^ ((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                  (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
            (kthKthNumeratorConst k₁ k₂ j₁ j₂ *
             t ^ (-((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                    (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))))
          = kthKthNumeratorConst k₁ k₂ j₁ j₂ *
            (t ^ ((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                  (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
             t ^ (-((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                    (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))) by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact (tendsto_const_nhds.congr' hEq.symm)

/-- **Asymptotic equivalence for the unnormalised 2D kth-kth numerator.**
The unnormalised numerator is asymptotically equivalent at
$\mathrm{atTop}$ to the pure power-law
$C'(k_1, k_2, j_1, j_2) \cdot t^{-(2j_1+1)/(2k_1) - (2j_2+1)/(2k_2)}$. -/
theorem integral_pow_pow_exp_neg_kthKth_isEquivalent_rpow
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ j₂ : ℕ) :
    (fun t : ℝ =>
        ∫ z : ℝ × ℝ, z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂) *
            Real.exp (-(t * addSeparable (Laplace.OneD.kthPotential k₁)
                                         (Laplace.OneD.kthPotential k₂) z)))
      ~[atTop]
      (fun t : ℝ => kthKthNumeratorConst k₁ k₂ j₁ j₂ *
                    t ^ (-((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                          (2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))) := by
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (integral_pow_pow_exp_neg_kthKth_eq_const_mul_rpow hk₁ hk₂ j₁ j₂ ht).symm

end Laplace.TwoD
