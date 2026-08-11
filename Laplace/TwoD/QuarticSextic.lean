import Laplace.OneD.Quartic
import Laplace.OneD.Sextic
import Laplace.TwoD.AddSeparable

/-!
# Mixed quartic-sextic 2D potential

For the 2D pure-monomial separable potential
$$
  L(x, y) = \frac{x^4}{24} + \frac{y^6}{720},
$$
the partition function and moments factor as products of the
corresponding 1D quantities. This file specialises the generic
`Laplace.TwoD.AddSeparable` theorems
(`partitionFunction_addSeparable_factor`,
`gibbsExpectation_separable_addSeparable`,
`gibbsCov_addSeparable_fst_snd_eq_zero`) to the
$(\mathrm{quarticPotential}, \mathrm{sexticPotential})$ pair.

## Headlines

* `partitionFunction_quarticSextic_factor`:
  $Z_{\mathrm{2D}}(t) = Z_{\mathrm{quartic}}(t) \cdot Z_{\mathrm{sextic}}(t)$.
* `partitionFunction_quarticSextic_eq`:
  the closed-form value
  $Z_{\mathrm{2D}}(t) = \tfrac12 (24/t)^{1/4} \Gamma(1/4)
  \cdot \tfrac13 (720/t)^{1/6} \Gamma(1/6)$.
* `gibbsExpectation_quarticSextic_factor`:
  moment factorisation $\langle f(x) g(y) \rangle_{\mathrm{2D}}
  = \langle f \rangle_{\mathrm{quartic}} \cdot \langle g \rangle_{\mathrm{sextic}}$.
* `gibbsCov_quarticSextic_fst_snd_eq_zero`:
  the mixed-coordinate covariance vanishes,
  $\mathrm{Cov}_{\mathrm{2D}}(f(x), g(y)) = 0$.

## Tide-step provenance

Tide step A2, formalised on `tide/quartic-sextic-mixed` (laplace,
branched off `main` at commit `b844d7a`). Tide log:
`projects/primer/tide-log/2026-05-07-tide-quartic-sextic-mixed.md`.
-/

open MeasureTheory

namespace Laplace.TwoD

/-! ## Integrability discharge for the two factor potentials -/

/-- The Boltzmann weight `exp(-(t · quarticPotential x))` is integrable
on `ℝ`. -/
private lemma integrable_exp_neg_t_quartic
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => Real.exp (-(t * Laplace.OneD.quarticPotential x))) := by
  have h := Laplace.OneD.quartic_integrable_pow_pot 0 ht
  simpa [pow_zero, one_mul] using h

/-- The Boltzmann weight `exp(-(t · sexticPotential y))` is integrable
on `ℝ`. -/
private lemma integrable_exp_neg_t_sextic
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => Real.exp (-(t * Laplace.OneD.sexticPotential y))) := by
  have h := Laplace.OneD.sextic_integrable_pow_pot 0 ht
  simpa [pow_zero, one_mul] using h

/-! ## Partition-function factorisation -/

/-- **Partition-function factorisation (quartic × sextic).**
The 2D partition function for the separable potential
$(x, y) \mapsto x^4/24 + y^6/720$ factors as the product of the 1D
quartic and sextic partition functions. Direct corollary of
`partitionFunction_addSeparable_factor` (Tide 12, A3). -/
theorem partitionFunction_quarticSextic_factor
    {t : ℝ} (ht : 0 < t) :
    partitionFunction (addSeparable Laplace.OneD.quarticPotential
                                    Laplace.OneD.sexticPotential) t
      = Laplace.partitionFunction Laplace.OneD.quarticPotential t *
        Laplace.partitionFunction Laplace.OneD.sexticPotential t :=
  partitionFunction_addSeparable_factor
    (integrable_exp_neg_t_quartic ht)
    (integrable_exp_neg_t_sextic ht)

/-- **Closed-form value of the 2D quartic-sextic partition function.**
Substituting the explicit `quartic_partition` and `sextic_partition`
formulas:
\[
  Z_{\mathrm{2D}}(t) = \tfrac12 (24/t)^{1/4} \Gamma(1/4) \cdot
                       \tfrac13 (720/t)^{1/6} \Gamma(1/6).
\] -/
theorem partitionFunction_quarticSextic_eq
    {t : ℝ} (ht : 0 < t) :
    partitionFunction (addSeparable Laplace.OneD.quarticPotential
                                    Laplace.OneD.sexticPotential) t
      = ((1 : ℝ)/2) * (24/t) ^ ((1 : ℝ)/4) * Real.Gamma ((1 : ℝ)/4) *
        (((1 : ℝ)/3) * (720/t) ^ ((1 : ℝ)/6) * Real.Gamma ((1 : ℝ)/6)) := by
  rw [partitionFunction_quarticSextic_factor ht,
      Laplace.OneD.quartic_partition ht,
      Laplace.OneD.sextic_partition ht]

/-- **Strict positivity of the 2D quartic-sextic partition.** -/
theorem partitionFunction_quarticSextic_pos
    {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction (addSeparable Laplace.OneD.quarticPotential
                                        Laplace.OneD.sexticPotential) t := by
  rw [partitionFunction_quarticSextic_factor ht]
  exact mul_pos (Laplace.OneD.quartic_partition_pos ht)
                (Laplace.OneD.sextic_partition_pos ht)

/-! ## Moment factorisation -/

/-- **Separable-observable moment factorisation (quartic × sextic).**
For a separable observable `f(x) · g(y)` against the 2D quartic-sextic
Gibbs measure, the expectation factors as a product of 1D
expectations. -/
theorem gibbsExpectation_quarticSextic_factor
    {t : ℝ} (ht : 0 < t) (f g : ℝ → ℝ)
    (hf : Integrable (fun x : ℝ => f x *
            Real.exp (-(t * Laplace.OneD.quarticPotential x))))
    (hg : Integrable (fun y : ℝ => g y *
            Real.exp (-(t * Laplace.OneD.sexticPotential y)))) :
    gibbsExpectation (addSeparable Laplace.OneD.quarticPotential
                                   Laplace.OneD.sexticPotential) t
        (fun z => f z.1 * g z.2)
      = Laplace.gibbsExpectation Laplace.OneD.quarticPotential t f *
        Laplace.gibbsExpectation Laplace.OneD.sexticPotential t g :=
  gibbsExpectation_separable_addSeparable f g
    (ne_of_gt (Laplace.OneD.quartic_partition_pos ht))
    (ne_of_gt (Laplace.OneD.sextic_partition_pos ht))
    (integrable_exp_neg_t_quartic ht)
    (integrable_exp_neg_t_sextic ht)
    hf hg

/-! ## Mixed-coordinate covariance vanishing -/

/-- **Mixed-coordinate covariance vanishes (quartic × sextic).**
For an `f`-of-first-coordinate observable and a `g`-of-second-coordinate
observable against the 2D quartic-sextic Gibbs measure, the covariance
is zero. The structural payoff of separability. -/
theorem gibbsCov_quarticSextic_fst_snd_eq_zero
    {t : ℝ} (ht : 0 < t) (f g : ℝ → ℝ)
    (hf : Integrable (fun x : ℝ => f x *
            Real.exp (-(t * Laplace.OneD.quarticPotential x))))
    (hg : Integrable (fun y : ℝ => g y *
            Real.exp (-(t * Laplace.OneD.sexticPotential y)))) :
    gibbsCov (addSeparable Laplace.OneD.quarticPotential
                           Laplace.OneD.sexticPotential) t
        (fun z => f z.1) (fun z => g z.2) = 0 :=
  gibbsCov_addSeparable_fst_snd_eq_zero f g
    (ne_of_gt (Laplace.OneD.quartic_partition_pos ht))
    (ne_of_gt (Laplace.OneD.sextic_partition_pos ht))
    (integrable_exp_neg_t_quartic ht)
    (integrable_exp_neg_t_sextic ht)
    hf hg

end Laplace.TwoD
