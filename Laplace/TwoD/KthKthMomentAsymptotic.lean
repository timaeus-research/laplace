import Laplace.OneD.MonomialPotential
import Laplace.TwoD.AddSeparable
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Generic 2D moment asymptotic for separable monomial potentials

For the 2D separable potential $L(x, y) = L_{k_1}(x) + L_{k_2}(y)$
with $L_k(z) = z^{2k}/(2k)!$ and $k_1, k_2 \ge 1$, this file
establishes the mixed-even-moment $\langle x^{2j_1} y^{2j_2}\rangle_{2D, t}$
asymptotic:

* `gibbsExpectation_kthKth_pow_pow_eq` — separable-observable
  factorisation: 2D mixed-even moment = product of 1D even moments.
* `gibbsExpectation_kthKth_pow_pow_eq_const_mul_rpow` — pulling out
  the $t$-dependence as $C(k_1, k_2, j_1, j_2) \cdot t^{-j_1/k_1 - j_2/k_2}$.
* `gibbsExpectation_kthKth_pow_pow_rescaled_tendsto` — multiplied
  by $t^{j_1/k_1 + j_2/k_2}$, tends to $C$ at $\mathrm{atTop}$.
* `gibbsExpectation_kthKth_pow_pow_isEquivalent_rpow` — asymptotic
  equivalence to the pure power-law.

Lifts the quartic-sextic V2 tide
(`Laplace/TwoD/QuarticSexticMomentAsymptotic.lean`) from
$(k_1, k_2) = (2, 3)$ to parametric $(k_1, k_2)$. Mirror-shape
follow-up to `Laplace/TwoD/KthKthPartitionAsymptotic.lean`.
-/

open Real MeasureTheory Filter Asymptotics
open scoped Topology

namespace Laplace.TwoD

/-- Composite constant prefactor for the generic-$(k_1, k_2)$ 2D
separable monomial mixed-even moment:
$$
  C(k_1, k_2, j_1, j_2) :=
    (2k_1)!^{j_1/k_1} \cdot (2k_2)!^{j_2/k_2}
    \cdot \frac{\Gamma((2j_1+1)/(2k_1))}{\Gamma(1/(2k_1))}
    \cdot \frac{\Gamma((2j_2+1)/(2k_2))}{\Gamma(1/(2k_2))}.
$$ -/
noncomputable def kthKthMomentConst (k₁ k₂ j₁ j₂ : ℕ) : ℝ :=
  ((Nat.factorial (2 * k₁) : ℝ)) ^ ((j₁ : ℝ) / (k₁ : ℝ)) *
  ((Nat.factorial (2 * k₂) : ℝ)) ^ ((j₂ : ℝ) / (k₂ : ℝ)) *
  (Real.Gamma ((2 * j₁ + 1 : ℝ) / ((2 * k₁ : ℕ) : ℝ)) /
    Real.Gamma ((1 : ℝ) / ((2 * k₁ : ℕ) : ℝ))) *
  (Real.Gamma ((2 * j₂ + 1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)) /
    Real.Gamma ((1 : ℝ) / ((2 * k₂ : ℕ) : ℝ)))

/-- **Exact factorisation of the 2D separable mixed-even moment.** For
$k_1, k_2 \ge 1$, $j_1, j_2 : \mathbb{N}$, and $t > 0$, the 2D mixed
moment factors as a product of the two 1D moments. -/
theorem gibbsExpectation_kthKth_pow_pow_eq
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ j₂ : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (addSeparable (Laplace.OneD.kthPotential k₁)
                                    (Laplace.OneD.kthPotential k₂)) t
        (fun z : ℝ × ℝ => z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂)) =
      Laplace.gibbsExpectation (Laplace.OneD.kthPotential k₁) t
        (fun x : ℝ => x ^ (2 * j₁)) *
      Laplace.gibbsExpectation (Laplace.OneD.kthPotential k₂) t
        (fun y : ℝ => y ^ (2 * j₂)) := by
  -- Apply the separable-observable factorisation.
  have hZU_ne : Laplace.partitionFunction (Laplace.OneD.kthPotential k₁) t ≠ 0 :=
    ne_of_gt (Laplace.OneD.partitionFunction_kthPotential_pos hk₁ ht)
  have hZV_ne : Laplace.partitionFunction (Laplace.OneD.kthPotential k₂) t ≠ 0 :=
    ne_of_gt (Laplace.OneD.partitionFunction_kthPotential_pos hk₂ ht)
  -- The Boltzmann weights are integrable (n = 0 case of kth_integrable_pow_pot).
  have hU : Integrable (fun x : ℝ => Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) := by
    have h := Laplace.OneD.kth_integrable_pow_pot (k := k₁) hk₁ 0 ht
    have heq : (fun x : ℝ =>
        x ^ 0 * Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) =
               (fun x : ℝ => Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) := by
      ext; simp
    rwa [heq] at h
  have hV : Integrable (fun y : ℝ => Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) := by
    have h := Laplace.OneD.kth_integrable_pow_pot (k := k₂) hk₂ 0 ht
    have heq : (fun y : ℝ =>
        y ^ 0 * Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) =
               (fun y : ℝ => Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) := by
      ext; simp
    rwa [heq] at h
  have hf : Integrable (fun x : ℝ => x ^ (2 * j₁) *
      Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) :=
    Laplace.OneD.kth_integrable_pow_pot (k := k₁) hk₁ (2 * j₁) ht
  have hg : Integrable (fun y : ℝ => y ^ (2 * j₂) *
      Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) :=
    Laplace.OneD.kth_integrable_pow_pot (k := k₂) hk₂ (2 * j₂) ht
  exact gibbsExpectation_separable_addSeparable
    (fun x : ℝ => x ^ (2 * j₁)) (fun y : ℝ => y ^ (2 * j₂))
    hZU_ne hZV_ne hU hV hf hg

/-- **Exact closed form for the 2D kth-kth mixed-even moment in
`const × t^(-...)` form.** For $k_1, k_2 \ge 1$ and $t > 0$,
the moment is $C(k_1, k_2, j_1, j_2) \cdot t^{-j_1/k_1 - j_2/k_2}$. -/
theorem gibbsExpectation_kthKth_pow_pow_eq_const_mul_rpow
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ j₂ : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (addSeparable (Laplace.OneD.kthPotential k₁)
                                    (Laplace.OneD.kthPotential k₂)) t
        (fun z : ℝ × ℝ => z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂)) =
      kthKthMomentConst k₁ k₂ j₁ j₂ *
        t ^ (-((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ))) := by
  rw [gibbsExpectation_kthKth_pow_pow_eq hk₁ hk₂ j₁ j₂ ht,
      Laplace.OneD.gibbsExpectation_kthPotential_even hk₁ j₁ ht,
      Laplace.OneD.gibbsExpectation_kthPotential_even hk₂ j₂ ht]
  unfold kthKthMomentConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  have hfac₁_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k₁) : ℝ)) := by positivity
  have hfac₂_nonneg : (0 : ℝ) ≤ ((Nat.factorial (2 * k₂) : ℝ)) := by positivity
  -- Split (fac₁/t)^(j₁/k₁) and (fac₂/t)^(j₂/k₂) into base / t^exponent pieces.
  rw [Real.div_rpow hfac₁_nonneg ht_le,
      Real.div_rpow hfac₂_nonneg ht_le]
  -- Combine 1/t^(j₁/k₁) · 1/t^(j₂/k₂) = t^(-(j₁/k₁ + j₂/k₂)).
  rw [show (-((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ)))
          = (-((j₁ : ℝ) / (k₁ : ℝ))) + (-((j₂ : ℝ) / (k₂ : ℝ))) by ring,
      Real.rpow_add ht,
      Real.rpow_neg ht_le,
      Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` for the 2D kth-kth mixed-even moment.**
Multiplied by $t^{j_1/k_1 + j_2/k_2}$, the moment tends to
$C(k_1, k_2, j_1, j_2)$ as $t \to \infty$. -/
theorem gibbsExpectation_kthKth_pow_pow_rescaled_tendsto
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ j₂ : ℕ) :
    Tendsto (fun t : ℝ =>
        t ^ ((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ)) *
        gibbsExpectation (addSeparable (Laplace.OneD.kthPotential k₁)
                                        (Laplace.OneD.kthPotential k₂)) t
          (fun z : ℝ × ℝ => z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂)))
      atTop (𝓝 (kthKthMomentConst k₁ k₂ j₁ j₂)) := by
  have hEq : (fun t : ℝ =>
      t ^ ((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ)) *
      gibbsExpectation (addSeparable (Laplace.OneD.kthPotential k₁)
                                      (Laplace.OneD.kthPotential k₂)) t
        (fun z : ℝ × ℝ => z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂)))
    =ᶠ[atTop] fun _ => kthKthMomentConst k₁ k₂ j₁ j₂ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [gibbsExpectation_kthKth_pow_pow_eq_const_mul_rpow hk₁ hk₂ j₁ j₂ ht]
    rw [show t ^ ((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ)) *
            (kthKthMomentConst k₁ k₂ j₁ j₂ *
             t ^ (-((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ))))
          = kthKthMomentConst k₁ k₂ j₁ j₂ *
            (t ^ ((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ)) *
             t ^ (-((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ)))) by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact (tendsto_const_nhds.congr' hEq.symm)

/-- **Asymptotic equivalence for the 2D kth-kth mixed-even moment.**
The moment is asymptotically equivalent at $\mathrm{atTop}$ to the
pure power-law $C(k_1, k_2, j_1, j_2) \cdot t^{-j_1/k_1 - j_2/k_2}$. -/
theorem gibbsExpectation_kthKth_pow_pow_isEquivalent_rpow
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ j₂ : ℕ) :
    (fun t : ℝ =>
        gibbsExpectation (addSeparable (Laplace.OneD.kthPotential k₁)
                                        (Laplace.OneD.kthPotential k₂)) t
          (fun z : ℝ × ℝ => z.1 ^ (2 * j₁) * z.2 ^ (2 * j₂)))
      ~[atTop]
      (fun t : ℝ => kthKthMomentConst k₁ k₂ j₁ j₂ *
                    t ^ (-((j₁ : ℝ) / (k₁ : ℝ) + (j₂ : ℝ) / (k₂ : ℝ)))) := by
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (gibbsExpectation_kthKth_pow_pow_eq_const_mul_rpow hk₁ hk₂ j₁ j₂ ht).symm

end Laplace.TwoD
