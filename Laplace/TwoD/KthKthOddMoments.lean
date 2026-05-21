import Laplace.OneD.MonomialPotential
import Laplace.TwoD.AddSeparable

/-!
# Mixed odd-power 2D moment vanishing for the generic kthkth potential

For the 2D separable potential $L(x, y) = L_{k_1}(x) + L_{k_2}(y)$
with $L_k(z) = z^{2k}/(2k)!$ and $k_1, k_2 \ge 1$, any joint moment
$\langle x^a y^b \rangle_{2D, t}$ vanishes whenever at least one
of $a, b$ is odd. We record this as two parity-completion theorems:
one fixes the $x$-exponent at $2j_1+1$ and lets the $y$-exponent be
any natural; the other fixes the $y$-exponent at $2j_2+1$ and lets
the $x$-exponent be any natural. Together they cover all
"at least one odd" cases including odd-odd.

Generic-$(k_1, k_2)$ mirror of `QuarticSexticOddMoments.lean`,
companion to the kthkth-arc trio
(`KthKthPartitionAsymptotic`, `KthKthMomentAsymptotic`,
`KthKthNumeratorAsymptotic`).

## Strategy

Apply `gibbsExpectation_separable_addSeparable` to factorise the 2D
expectation into the product of two 1D expectations; close the odd
factor via `Laplace.OneD.gibbsExpectation_kthPotential_odd`; the
product is zero by `zero_mul` / `mul_zero`. Mirror of the
quartic-sextic template at parametric $k_1, k_2$.
-/

open MeasureTheory

namespace Laplace.TwoD

/-- **Mixed odd-power 2D moment vanishes (odd-$x$ side).**

For $k_1, k_2 \ge 1$, any $j_1, n : \mathbb N$, and $t > 0$,
$\langle x^{2j_1+1} y^n \rangle_{2D, t} = 0$ on the separable
potential $L_{k_1}(x) + L_{k_2}(y)$. Holds regardless of the parity
of $n$, including the odd-odd case $n = 2j_2 + 1$. -/
theorem gibbsExpectation_kthKth_odd_pow_pow_eq_zero
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (j₁ n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (addSeparable (Laplace.OneD.kthPotential k₁)
                                    (Laplace.OneD.kthPotential k₂)) t
        (fun z : ℝ × ℝ => z.1 ^ (2 * j₁ + 1) * z.2 ^ n) = 0 := by
  have hZU_ne : Laplace.partitionFunction (Laplace.OneD.kthPotential k₁) t ≠ 0 :=
    ne_of_gt (Laplace.OneD.partitionFunction_kthPotential_pos hk₁ ht)
  have hZV_ne : Laplace.partitionFunction (Laplace.OneD.kthPotential k₂) t ≠ 0 :=
    ne_of_gt (Laplace.OneD.partitionFunction_kthPotential_pos hk₂ ht)
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
  have hf : Integrable (fun x : ℝ => x ^ (2 * j₁ + 1) *
      Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) :=
    Laplace.OneD.kth_integrable_pow_pot (k := k₁) hk₁ (2 * j₁ + 1) ht
  have hg : Integrable (fun y : ℝ => y ^ n *
      Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) :=
    Laplace.OneD.kth_integrable_pow_pot (k := k₂) hk₂ n ht
  rw [gibbsExpectation_separable_addSeparable
        (fun x : ℝ => x ^ (2 * j₁ + 1)) (fun y : ℝ => y ^ n)
        hZU_ne hZV_ne hU hV hf hg,
      Laplace.OneD.gibbsExpectation_kthPotential_odd k₁ j₁ t]
  simp

/-- **Mixed odd-power 2D moment vanishes (odd-$y$ side).**

For $k_1, k_2 \ge 1$, any $m, j_2 : \mathbb N$, and $t > 0$,
$\langle x^m y^{2j_2+1} \rangle_{2D, t} = 0$ on the separable
potential $L_{k_1}(x) + L_{k_2}(y)$. Holds regardless of the parity
of $m$, including the odd-odd case $m = 2j_1 + 1$. -/
theorem gibbsExpectation_kthKth_pow_odd_pow_eq_zero
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (m j₂ : ℕ)
    {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (addSeparable (Laplace.OneD.kthPotential k₁)
                                    (Laplace.OneD.kthPotential k₂)) t
        (fun z : ℝ × ℝ => z.1 ^ m * z.2 ^ (2 * j₂ + 1)) = 0 := by
  have hZU_ne : Laplace.partitionFunction (Laplace.OneD.kthPotential k₁) t ≠ 0 :=
    ne_of_gt (Laplace.OneD.partitionFunction_kthPotential_pos hk₁ ht)
  have hZV_ne : Laplace.partitionFunction (Laplace.OneD.kthPotential k₂) t ≠ 0 :=
    ne_of_gt (Laplace.OneD.partitionFunction_kthPotential_pos hk₂ ht)
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
  have hf : Integrable (fun x : ℝ => x ^ m *
      Real.exp (-(t * Laplace.OneD.kthPotential k₁ x))) :=
    Laplace.OneD.kth_integrable_pow_pot (k := k₁) hk₁ m ht
  have hg : Integrable (fun y : ℝ => y ^ (2 * j₂ + 1) *
      Real.exp (-(t * Laplace.OneD.kthPotential k₂ y))) :=
    Laplace.OneD.kth_integrable_pow_pot (k := k₂) hk₂ (2 * j₂ + 1) ht
  rw [gibbsExpectation_separable_addSeparable
        (fun x : ℝ => x ^ m) (fun y : ℝ => y ^ (2 * j₂ + 1))
        hZU_ne hZV_ne hU hV hf hg,
      Laplace.OneD.gibbsExpectation_kthPotential_odd k₂ j₂ t]
  simp

end Laplace.TwoD
