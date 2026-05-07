import Laplace.TwoD.QuarticSextic

/-!
# Mixed even-power 2D moments for the quartic-sextic potential

For the 2D separable potential $L(x, y) = x^4/24 + y^6/720$, the
joint moment $\langle x^{2j} \cdot y^{2k} \rangle_{2D, t}$ factors
as a product of the 1D quartic and sextic even moments.

## Headline

* `gibbsExpectation_quarticSextic_pow_pow_eq`: closed form for the
  mixed even moment.

## Strategy

Two rewrites: first apply A2's
`gibbsExpectation_quarticSextic_factor` with `f := x ↦ x^(2j)` and
`g := y ↦ y^(2k)` (using `quartic_integrable_pow_pot` and
`sextic_integrable_pow_pot` for integrability); then substitute
`quartic_expected_value_even` and `sextic_expected_value_even` to
get the closed-form Gamma expression.
-/

namespace Laplace.TwoD

/-- **Closed form for the mixed even-power 2D moment
(quartic × sextic).**

For the 2D potential $L(x, y) = x^4/24 + y^6/720$ at temperature
$t > 0$, and any $j, k : \mathbb N$,
$$
  \langle x^{2j} \cdot y^{2k} \rangle_{2D, t}
  = \left( (24/t)^{j/2} \cdot \frac{\Gamma((2j+1)/4)}{\Gamma(1/4)} \right)
    \cdot \left( (720/t)^{k/3} \cdot \frac{\Gamma((2k+1)/6)}{\Gamma(1/6)} \right).
$$
The factorisation is the structural content; the closed form is a
direct consequence of the separability of the 2D measure plus the
1D quartic and sextic even-moment closed forms. -/
theorem gibbsExpectation_quarticSextic_pow_pow_eq
    (j k : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation
        (addSeparable Laplace.OneD.quarticPotential
                      Laplace.OneD.sexticPotential) t
        (fun z : ℝ × ℝ => z.1 ^ (2 * j) * z.2 ^ (2 * k))
      = ((24 / t) ^ ((j : ℝ) / 2)
            * Real.Gamma ((2 * j + 1 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4))
        * ((720 / t) ^ ((k : ℝ) / 3)
            * Real.Gamma ((2 * k + 1 : ℝ) / 6) / Real.Gamma ((1 : ℝ) / 6)) := by
  rw [gibbsExpectation_quarticSextic_factor ht
        (fun x : ℝ => x ^ (2 * j)) (fun y : ℝ => y ^ (2 * k))
        (Laplace.OneD.quartic_integrable_pow_pot (2 * j) ht)
        (Laplace.OneD.sextic_integrable_pow_pot (2 * k) ht)]
  rw [Laplace.OneD.quartic_expected_value_even j ht,
      Laplace.OneD.sextic_expected_value_even k ht]

end Laplace.TwoD
