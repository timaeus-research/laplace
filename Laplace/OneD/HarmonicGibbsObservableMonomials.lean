import Laplace.OneD.HarmonicGibbsRegularity
import Laplace.OneD.IntegralRemainder
import Threepoint.CrossSusceptibility

/-!
# `Threepoint.GibbsObservable` instances for harmonic monomials (in progress)

Working towards concrete `Threepoint.GibbsObservable` instances for the
harmonic potential `L(x) = (λ/2) x²` with linear perturbation
`A(x) = x` and monomial observables `(fun x => x^k)` for `k : ℕ`. This
makes Tide 13's `cov_h_id_id_deriv_harmonic_eq_zero` unconditional on
the `GibbsObservable` hypotheses for the canonical `x, x², x³`
observables.

## Strategy

After the GPT-5.5 Pro deliberation, the chosen route is **dominated
differentiation under the integral sign** (not the closed-form
binomial-expansion route): apply
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
a Gaussian-domination bound
\[
  |x^k \cdot e^{-(t\,((\lambda/2)x^2 + h\,x))}|
    \;\le\; C \cdot |x|^k \cdot e^{-(t\lambda/4)\,x^2}
\]
valid for `|h| ≤ 1` (Young's inequality:
`|hx| ≤ (λ/4)x² + h²/λ` absorbs the linear perturbation into the
quadratic decay). Integrability of the dominator falls out from
`integrable_abs_pow_mul_exp_neg_mul_sq` already in the seabed
(`Laplace/OneD/IntegralRemainder.lean`).

The dominated-differentiation route is cleaner than the closed-form
route here because (i) it is generic in `k : ℕ` at no extra cost,
(ii) it avoids needing a central-Gaussian-moment library (M₂, M₄, …)
that Mathlib v4.29.0 doesn't ship in the form we need, and (iii) the
integrability infrastructure is already in the seabed.

## Status

This file currently provides one foundational primitive needed by the
upcoming `GibbsObservable` instances:

- `harmonic_perturbed_numerator_zero_eq`: the `h = 0` reduction of
  the perturbed monomial numerator. Discharges the first conjunct of
  `Threepoint.GibbsObservable` for any monomial observable.

The headline `harmonic_id_gibbsObservable_pow` and the analytic core
(domination bound, dominated-differentiation invocation, `HasDerivAt`
conjunct of `GibbsObservable`) are sketched in the local handoff note
`notes/gibbsobservable_monomials_handoff.md` and will land in a
follow-up session. The h=0 identity primitive committed here is
independently useful — it covers the first conjunct of every
`GibbsObservable` instance for *any* observable that doesn't see the
perturbation parameter, not just monomials.

## Tide-step provenance

Tide step (G4 from the 7 May candidates survey),
`tide/harmonic-gibbsobservable-monomials` branch, off laplace `main`
at `f21a9cc`. Tide log:
`sri/projects/patterning/tide-log/2026-05-07-tide-harmonic-gibbsobservable-monomials.md`.
-/

open MeasureTheory Set

namespace Laplace.OneD

/-! ## The `h = 0` identity for monomial-numerator integrals

`Threepoint.GibbsObservable μ L A t φ` is a conjunction; the first
conjunct asks that the numerator
`∫ φ(w) · exp(-(t · (L(w) + 0 · A(w)))) ∂μ` reduces to
`∫ φ(w) · exp(-(t · L(w))) ∂μ`. For the harmonic + linear setup
`(L, A) = ((λ/2)·², id)` with monomial `φ(x) = x^k`, this is a
`simp [zero_mul, add_zero]`-style reduction. The lemma below does the
reduction once for any observable; it is independent of the choice of
`φ` and even of `k`. -/

/-- For the harmonic potential `(λ/2)·x²` with linear perturbation
`A(x) = x`, the perturbed numerator at `h = 0` reduces to the
unperturbed integral. Independent of the observable `φ`. -/
theorem harmonic_perturbed_numerator_zero_eq
    (lam t : ℝ) (φ : ℝ → ℝ) :
    (∫ w : ℝ, φ w * Real.exp (-(t * ((lam / 2) * w ^ 2 + 0 * w))))
      = (∫ w : ℝ, φ w * Real.exp (-(t * ((lam / 2) * w ^ 2)))) := by
  congr 1
  funext w
  ring_nf

/-- Specialisation to monomial observables. Matches the first conjunct
of `Threepoint.GibbsObservable` for `(volume, harmonic, id)` at
`φ(x) = x^k`. -/
theorem harmonic_perturbed_numerator_zero_eq_pow
    (lam t : ℝ) (k : ℕ) :
    (∫ w : ℝ, w ^ k * Real.exp (-(t * ((lam / 2) * w ^ 2 + 0 * w))))
      = (∫ w : ℝ, w ^ k * Real.exp (-(t * ((lam / 2) * w ^ 2)))) :=
  harmonic_perturbed_numerator_zero_eq lam t (fun w => w ^ k)

end Laplace.OneD
