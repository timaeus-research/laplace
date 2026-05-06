import Laplace.Gibbs
import Laplace.TwoD.SemiDegenerate

/-!
# Additively-separable 2D potentials

For potentials of the form `L(x, y) = U(x) + V(y)`, this file establishes the
generic factorisation lemmas that the existing `Laplace/TwoD/SemiDegenerate.lean`
(harmonic + quartic) and `Laplace/TwoD/PureQuartic.lean` (quartic + quartic)
files prove case-by-case. The two existing files are not (yet) refactored to
use the abstraction; this is the "additive infrastructure only" entry that a
follow-up tide can build the refactor on top of.

## Headline results

* `partitionFunction_addSeparable_factor`: under integrability of each
  marginal Boltzmann weight, `Z_2D(t) = Z_U(t) · Z_V(t)`.
* `integral_separable_addSeparable`: for separable observables `f(x) · g(y)`,
  `∫ f(x) g(y) e^{-tL(x,y)} dx dy = (∫ f(x) e^{-tU(x)} dx) · (∫ g(y) e^{-tV(y)} dy)`.
* `gibbsExpectation_separable_addSeparable`: when both 1D partition functions
  are nonzero, `⟨f ⊗ g⟩_{2D, t} = ⟨f⟩_{U, t} · ⟨g⟩_{V, t}`.
* `gibbsCov_addSeparable_fst_snd_eq_zero`: the structural payoff of
  separability — under product Gibbs, the covariance of an `f`-of-first and
  `g`-of-second observable vanishes.

## Why this is a tide step

Both `SemiDegenerate.lean` and `PureQuartic.lean` re-derive the same template;
the two files share an exactly-parallel proof skeleton. This module exposes
that template once. Future 2D files (e.g. quartic-sextic mixed) become
specialisations rather than copy-paste rewrites, and the mixed-covariance
vanishing is now a generic theorem rather than an algebra-by-cancellation in
each headline `cov_affine_*`.

See `projects/primer/tide-log/2026-05-06-tide-separable-potential.md` in the
SRI repo for the deliberation log.
-/

open Real MeasureTheory

namespace Laplace.TwoD

/-- The additively-separable 2D potential `L(x, y) = U(x) + V(y)`. -/
noncomputable def addSeparable (U V : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun z => U z.1 + V z.2

@[simp] lemma addSeparable_apply (U V : ℝ → ℝ) (z : ℝ × ℝ) :
    addSeparable U V z = U z.1 + V z.2 := rfl

/-- Boltzmann factor decomposition for the additively-separable potential. -/
lemma exp_neg_t_addSeparable_eq_mul (U V : ℝ → ℝ) (t : ℝ) (z : ℝ × ℝ) :
    Real.exp (-(t * addSeparable U V z)) =
      Real.exp (-(t * U z.1)) * Real.exp (-(t * V z.2)) := by
  rw [addSeparable_apply,
      show (-(t * (U z.1 + V z.2)) : ℝ) = -(t * U z.1) + -(t * V z.2) from by ring,
      Real.exp_add]

/-- **Partition-function factorisation**: `Z_2D(t) = Z_U(t) · Z_V(t)`.
Unconditional: `MeasureTheory.integral_prod_mul` is unconditional, so the
factorisation holds even when the 1D weights are not Lebesgue-integrable
(both sides are `0` by Bochner convention in that case). -/
theorem partitionFunction_addSeparable_factor
    (U V : ℝ → ℝ) (t : ℝ) :
    partitionFunction (addSeparable U V) t =
      Laplace.partitionFunction U t * Laplace.partitionFunction V t := by
  unfold partitionFunction Laplace.partitionFunction
  rw [show (fun z : ℝ × ℝ => Real.exp (-(t * addSeparable U V z))) =
        (fun z : ℝ × ℝ =>
          Real.exp (-(t * U z.1)) * Real.exp (-(t * V z.2))) from by
        funext z; exact exp_neg_t_addSeparable_eq_mul U V t z]
  exact MeasureTheory.integral_prod_mul
    (f := fun x : ℝ => Real.exp (-(t * U x)))
    (g := fun y : ℝ => Real.exp (-(t * V y)))

/-- **Separable-observable factorisation**: for an integrand `f(x) · g(y) · e^{-tL}`,
the 2D integral factors as a product of 1D weighted integrals.
Unconditional, for the same reason as `partitionFunction_addSeparable_factor`. -/
theorem integral_separable_addSeparable
    (U V : ℝ → ℝ) (t : ℝ) (f g : ℝ → ℝ) :
    (∫ z : ℝ × ℝ, f z.1 * g z.2 * Real.exp (-(t * addSeparable U V z))) =
      (∫ x : ℝ, f x * Real.exp (-(t * U x))) *
        (∫ y : ℝ, g y * Real.exp (-(t * V y))) := by
  rw [show (fun z : ℝ × ℝ => f z.1 * g z.2 * Real.exp (-(t * addSeparable U V z))) =
        (fun z : ℝ × ℝ =>
          (f z.1 * Real.exp (-(t * U z.1))) *
          (g z.2 * Real.exp (-(t * V z.2)))) from by
        funext z
        rw [exp_neg_t_addSeparable_eq_mul U V t z]
        ring]
  exact MeasureTheory.integral_prod_mul
    (f := fun x : ℝ => f x * Real.exp (-(t * U x)))
    (g := fun y : ℝ => g y * Real.exp (-(t * V y)))

/-- **Gibbs-expectation factorisation**: when both 1D partition functions are
nonzero, the 2D Gibbs expectation of a separable observable factors. -/
theorem gibbsExpectation_separable_addSeparable
    {U V : ℝ → ℝ} {t : ℝ} (f g : ℝ → ℝ)
    (hZU_ne : Laplace.partitionFunction U t ≠ 0)
    (hZV_ne : Laplace.partitionFunction V t ≠ 0) :
    gibbsExpectation (addSeparable U V) t (fun z => f z.1 * g z.2) =
      Laplace.gibbsExpectation U t f *
        Laplace.gibbsExpectation V t g := by
  unfold gibbsExpectation Laplace.gibbsExpectation
  rw [partitionFunction_addSeparable_factor]
  rw [integral_separable_addSeparable]
  field_simp

/-- **Mixed-covariance vanishing**: under a product/separable Gibbs measure,
the covariance between an `f`-of-first observable and a `g`-of-second
observable is zero. The structural payoff of separability. -/
theorem gibbsCov_addSeparable_fst_snd_eq_zero
    {U V : ℝ → ℝ} {t : ℝ} (f g : ℝ → ℝ)
    (hZU_ne : Laplace.partitionFunction U t ≠ 0)
    (hZV_ne : Laplace.partitionFunction V t ≠ 0) :
    gibbsCov (addSeparable U V) t
        (fun z => f z.1) (fun z => g z.2) = 0 := by
  unfold gibbsCov
  -- Step 1: ⟨f(z.1) · g(z.2)⟩ = ⟨f⟩_U · ⟨g⟩_V (separable-observable factorisation).
  rw [gibbsExpectation_separable_addSeparable f g hZU_ne hZV_ne]
  -- Step 2: ⟨f(z.1)⟩_2D = ⟨f⟩_U (collapse with g = 1).
  have hExp_f : gibbsExpectation (addSeparable U V) t (fun z => f z.1) =
      Laplace.gibbsExpectation U t f := by
    have h := gibbsExpectation_separable_addSeparable f (fun _ => (1 : ℝ))
      hZU_ne hZV_ne
    have hg1 : Laplace.gibbsExpectation V t (fun _ => (1 : ℝ)) = 1 :=
      Laplace.gibbsExpectation_const V t 1 hZV_ne
    rw [show (fun z : ℝ × ℝ => f z.1 * (1 : ℝ)) = (fun z : ℝ × ℝ => f z.1) from by
          funext z; ring] at h
    rw [h, hg1, mul_one]
  -- Step 3: ⟨g(z.2)⟩_2D = ⟨g⟩_V (collapse with f = 1).
  have hExp_g : gibbsExpectation (addSeparable U V) t (fun z => g z.2) =
      Laplace.gibbsExpectation V t g := by
    have h := gibbsExpectation_separable_addSeparable (fun _ => (1 : ℝ)) g
      hZU_ne hZV_ne
    have hf1 : Laplace.gibbsExpectation U t (fun _ => (1 : ℝ)) = 1 :=
      Laplace.gibbsExpectation_const U t 1 hZU_ne
    rw [show (fun z : ℝ × ℝ => (1 : ℝ) * g z.2) = (fun z : ℝ × ℝ => g z.2) from by
          funext z; ring] at h
    rw [h, hf1, one_mul]
  rw [hExp_f, hExp_g]
  ring

end Laplace.TwoD
