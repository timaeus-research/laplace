import Laplace.OneD.MonomialPotential
import Laplace.TwoD.AddSeparable
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Generic 2D partition function asymptotic for separable monomial potentials

For the 2D separable potential $L(x, y) = L_{k_1}(x) + L_{k_2}(y)$
with $L_k(z) = z^{2k}/(2k)!$ and $k_1, k_2 \ge 1$, this file
establishes:

* `partitionFunction_kthKth_eq` — exact closed form
  $Z_{2D}(t) = Z_{L_{k_1}}(t) \cdot Z_{L_{k_2}}(t)$ specialised to a
  scalar polynomial-in-$t$ form;
* `partitionFunction_kthKth_eq_const_mul_rpow` — pulling out the
  $t$-dependence as $C(k_1, k_2) \cdot t^{-1/(2k_1) - 1/(2k_2)}$;
* `partitionFunction_kthKth_rescaled_tendsto` — multiplied by
  $t^{1/(2k_1) + 1/(2k_2)}$, tends to $C(k_1, k_2)$ at $\mathrm{atTop}$;
* `partitionFunction_kthKth_isEquivalent_rpow` — asymptotic
  equivalence to the pure power-law.

Lifts the quartic-sextic Z2 tide
(`Laplace/TwoD/QuarticSexticPartitionAsymptotic.lean`) from
$(k_1, k_2) = (2, 3)$ to parametric $(k_1, k_2)$.
-/

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.TwoD

/-- Composite constant prefactor for the generic-$(k_1, k_2)$ 2D
separable monomial partition function:
$$
  C(k_1, k_2) := \tfrac{1}{k_1 k_2}\cdot (2k_1)!^{1/(2k_1)}\cdot
    (2k_2)!^{1/(2k_2)}\cdot \Gamma(1/(2k_1))\cdot \Gamma(1/(2k_2)).
$$ -/
noncomputable def kthKthPartitionConst (k₁ k₂ : ℕ) : ℝ :=
  (1 / ((k₁ : ℝ) * (k₂ : ℝ))) *
    ((Nat.factorial (2 * k₁) : ℝ)) ^ ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) *
    ((Nat.factorial (2 * k₂) : ℝ)) ^ ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
    Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) *
    Real.Gamma ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))

/-- **Exact factorisation of the 2D separable kth-kth partition
function.** For $k_1, k_2 \ge 1$ and $t > 0$, the 2D partition is the
product of the two 1D partitions. -/
theorem partitionFunction_kthKth_eq
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) {t : ℝ} (ht : 0 < t) :
    partitionFunction (addSeparable (Laplace.OneD.kthPotential k₁)
                                    (Laplace.OneD.kthPotential k₂)) t =
      Laplace.partitionFunction (Laplace.OneD.kthPotential k₁) t *
      Laplace.partitionFunction (Laplace.OneD.kthPotential k₂) t := by
  -- The 1D Boltzmann weights are integrable (n = 0 specialisation).
  have hU :
      Integrable (fun x : ℝ => Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) := by
    have h := Laplace.OneD.kth_integrable_pow_pot (k := k₁) hk₁ 0 ht
    have heq : (fun x : ℝ =>
        x ^ 0 * Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) =
               (fun x : ℝ => Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) := by
      ext; simp
    rwa [heq] at h
  have hV :
      Integrable (fun y : ℝ => Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) := by
    have h := Laplace.OneD.kth_integrable_pow_pot (k := k₂) hk₂ 0 ht
    have heq : (fun y : ℝ =>
        y ^ 0 * Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) =
               (fun y : ℝ => Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) := by
      ext; simp
    rwa [heq] at h
  exact partitionFunction_addSeparable_factor hU hV

/-- **Exact closed form for the 2D kth-kth partition function in
`const × t^(-...)` form.** For $k_1, k_2 \ge 1$ and $t > 0$,
$Z_{2D}(t) = C(k_1, k_2) \cdot t^{-1/(2k_1) - 1/(2k_2)}$. -/
theorem partitionFunction_kthKth_eq_const_mul_rpow
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) {t : ℝ} (ht : 0 < t) :
    partitionFunction (addSeparable (Laplace.OneD.kthPotential k₁)
                                    (Laplace.OneD.kthPotential k₂)) t =
      kthKthPartitionConst k₁ k₂ *
        t ^ (-((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
              (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))) := by
  rw [partitionFunction_kthKth_eq hk₁ hk₂ ht,
      Laplace.OneD.partitionFunction_kthPotential hk₁ ht,
      Laplace.OneD.partitionFunction_kthPotential hk₂ ht]
  unfold kthKthPartitionConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  have h_fact₁_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k₁) : ℝ)) := by positivity
  have h_fact₂_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k₂) : ℝ)) := by positivity
  rw [Real.div_rpow h_fact₁_nonneg ht_le,
      Real.div_rpow h_fact₂_nonneg ht_le]
  rw [show (-((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) + (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))
          = (-((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ))) +
            (-((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))) by ring,
      Real.rpow_add ht,
      Real.rpow_neg ht_le,
      Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` for the 2D kth-kth partition function.**
Multiplied by $t^{1/(2k_1) + 1/(2k_2)}$, the partition function tends
to $C(k_1, k_2)$ as $t \to \infty$. -/
theorem partitionFunction_kthKth_rescaled_tendsto
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    Tendsto (fun t : ℝ =>
        t ^ ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
             (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
        partitionFunction (addSeparable (Laplace.OneD.kthPotential k₁)
                                        (Laplace.OneD.kthPotential k₂)) t)
      atTop (𝓝 (kthKthPartitionConst k₁ k₂)) := by
  have hEq : (fun t : ℝ =>
      t ^ ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
           (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
      partitionFunction (addSeparable (Laplace.OneD.kthPotential k₁)
                                      (Laplace.OneD.kthPotential k₂)) t)
    =ᶠ[atTop] fun _ => kthKthPartitionConst k₁ k₂ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [partitionFunction_kthKth_eq_const_mul_rpow hk₁ hk₂ ht]
    rw [show t ^ ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                  (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
            (kthKthPartitionConst k₁ k₂ *
             t ^ (-((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                    (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ))))
          = kthKthPartitionConst k₁ k₂ *
            (t ^ ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                  (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) *
             t ^ (-((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                    (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))) by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact (tendsto_const_nhds.congr' hEq.symm)

/-- **Asymptotic equivalence for the 2D kth-kth partition function.**
The partition function is asymptotically equivalent at $\mathrm{atTop}$
to the pure power-law $C(k_1, k_2) \cdot t^{-1/(2k_1) - 1/(2k_2)}$. -/
theorem partitionFunction_kthKth_isEquivalent_rpow
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    (fun t : ℝ =>
        partitionFunction (addSeparable (Laplace.OneD.kthPotential k₁)
                                        (Laplace.OneD.kthPotential k₂)) t)
      ~[atTop]
      (fun t : ℝ => kthKthPartitionConst k₁ k₂ *
                    t ^ (-((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ) +
                          (1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))) := by
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (partitionFunction_kthKth_eq_const_mul_rpow hk₁ hk₂ ht).symm

end Laplace.TwoD
