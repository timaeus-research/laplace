import Laplace.TwoD.QuarticSextic

/-!
# Mixed odd-power 2D moment vanishing for the quartic-sextic potential

For the 2D separable potential $L(x, y) = x^4/24 + y^6/720$, any joint
moment $\langle x^a \cdot y^b \rangle_{2D, t}$ vanishes whenever at
least one of $a, b$ is odd. We record this as two parity-completion
theorems: one fixes the $x$-exponent at $2j+1$ and lets the
$y$-exponent be any natural; the other fixes the $y$-exponent at
$2k+1$ and lets the $x$-exponent be any natural. Together they cover
all "at least one odd" cases including odd-odd.

## Headline

* `gibbsExpectation_quarticSextic_odd_pow_pow_eq_zero` — vanishing when
  the $x$-exponent is odd.
* `gibbsExpectation_quarticSextic_pow_odd_pow_eq_zero` — vanishing when
  the $y$-exponent is odd.

## Strategy

Apply A2's `gibbsExpectation_quarticSextic_factor` to factorise the
2D expectation into the product of the 1D quartic and 1D sextic
expectations of the corresponding pure monomials, then close the odd
factor by `Laplace.OneD.quartic_expected_value_odd` (resp.
`sextic_expected_value_odd`); the product is zero by `zero_mul` /
`mul_zero`, discharged by `simp`. Mirror of T1's
`gibbsExpectation_quarticSextic_pow_pow_eq` template; the only
difference is which 1D closed form does the work.
-/

namespace Laplace.TwoD

/-- **Mixed odd-power 2D moment vanishes (odd-$x$ side).**

For the 2D potential $L(x, y) = x^4/24 + y^6/720$ at temperature
$t > 0$, and any $j, n : \mathbb N$,
$$
  \langle x^{2j+1} \cdot y^n \rangle_{2D, t} = 0.
$$
Holds regardless of the parity of $n$, including the odd-odd case
$n = 2k+1$. -/
theorem gibbsExpectation_quarticSextic_odd_pow_pow_eq_zero
    (j n : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation
        (addSeparable Laplace.OneD.quarticPotential
                      Laplace.OneD.sexticPotential) t
        (fun z : ℝ × ℝ => z.1 ^ (2 * j + 1) * z.2 ^ n) = 0 := by
  rw [gibbsExpectation_quarticSextic_factor ht
        (fun x : ℝ => x ^ (2 * j + 1)) (fun y : ℝ => y ^ n)
        (Laplace.OneD.quartic_integrable_pow_pot (2 * j + 1) ht)
        (Laplace.OneD.sextic_integrable_pow_pot n ht),
      Laplace.OneD.quartic_expected_value_odd j t]
  simp

/-- **Mixed odd-power 2D moment vanishes (odd-$y$ side).**

For the 2D potential $L(x, y) = x^4/24 + y^6/720$ at temperature
$t > 0$, and any $m, k : \mathbb N$,
$$
  \langle x^m \cdot y^{2k+1} \rangle_{2D, t} = 0.
$$
Holds regardless of the parity of $m$, including the odd-odd case
$m = 2j+1$. -/
theorem gibbsExpectation_quarticSextic_pow_odd_pow_eq_zero
    (m k : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation
        (addSeparable Laplace.OneD.quarticPotential
                      Laplace.OneD.sexticPotential) t
        (fun z : ℝ × ℝ => z.1 ^ m * z.2 ^ (2 * k + 1)) = 0 := by
  rw [gibbsExpectation_quarticSextic_factor ht
        (fun x : ℝ => x ^ m) (fun y : ℝ => y ^ (2 * k + 1))
        (Laplace.OneD.quartic_integrable_pow_pot m ht)
        (Laplace.OneD.sextic_integrable_pow_pot (2 * k + 1) ht),
      Laplace.OneD.sextic_expected_value_odd k t]
  simp

end Laplace.TwoD
