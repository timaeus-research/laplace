import Laplace.Gibbs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-!
# 2D Gibbs framework

Thin wrappers for the 2D analogues of `Laplace.partitionFunction`,
`Laplace.gibbsExpectation`, `Laplace.gibbsCov` over potentials
`L : ℝ × ℝ → ℝ`.

Pulled out of `Laplace.TwoD.SemiDegenerate` (where they originally lived,
mixed in with the `(λ/2)y² + x⁴/24` potential's specific lemmas) into
this small foundational file so that
`Laplace.TwoD.AddSeparable` can use them without inducing a circular
import — `SemiDegenerate.lean` and `PureQuartic.lean` now both depend
on `AddSeparable` for their bridge lemmas.
-/

open Real MeasureTheory

namespace Laplace.TwoD

/-- Partition function of the 2D Gibbs measure `exp(-t · L(z)) dz` on `ℝ × ℝ`. -/
noncomputable def partitionFunction (L : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, Real.exp (-(t * L z))

/-- Gibbs expectation `⟨φ⟩_t = (1/Z(t)) · ∫ φ(z) exp(-t L(z)) dz`. -/
noncomputable def gibbsExpectation (L : ℝ × ℝ → ℝ) (t : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  (∫ z : ℝ × ℝ, φ z * Real.exp (-(t * L z))) / partitionFunction L t

/-- Gibbs covariance `Cov_t[φ, ψ] = ⟨φψ⟩_t − ⟨φ⟩_t ⟨ψ⟩_t`. -/
noncomputable def gibbsCov
    (L : ℝ × ℝ → ℝ) (t : ℝ) (φ ψ : ℝ × ℝ → ℝ) : ℝ :=
  gibbsExpectation L t (fun z => φ z * ψ z)
    - gibbsExpectation L t φ * gibbsExpectation L t ψ

end Laplace.TwoD
