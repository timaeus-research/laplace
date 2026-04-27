import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Multivariate Gibbs measures

For a smooth potential `L : (ι → ℝ) → ℝ` on a finite-dimensional space and
inverse-temperature parameter `t > 0`, this file defines the multivariate
analogues of the 1D `partitionFunction`, `gibbsExpectation`, and `gibbsCov`
from `Laplace.Gibbs`.

We use `ι → ℝ` (with `[Fintype ι]`) rather than `EuclideanSpace ℝ ι` because
the former has a canonical `MeasureSpace` instance (via `Pi.MeasureSpace`)
giving the product Lebesgue measure. Inner product structure for gradients
is recovered as needed via the natural identification with `EuclideanSpace`.

Used by `Laplace.Multi.Covariance` to formalise the primer's
`lem:laplace_cov`: `Cov_t[φ, ψ] = (1/t) · ⟨∇φ(w*), Σ ∇ψ(w*)⟩ + O(t⁻²)`
with `Σ = H⁻¹`.
-/

open MeasureTheory

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- Partition function `Z(t) = ∫ exp(-t · L(w)) dw` over `ι → ℝ`. -/
noncomputable def partitionFunction (L : (ι → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ w : ι → ℝ, Real.exp (-(t * L w))

/-- Gibbs expectation `⟨φ⟩_t = (1/Z(t)) · ∫ φ(w) exp(-t · L(w)) dw`. -/
noncomputable def gibbsExpectation
    (L : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → ℝ) : ℝ :=
  (∫ w : ι → ℝ, φ w * Real.exp (-(t * L w))) / partitionFunction L t

/-- Gibbs covariance `Cov_t[φ, ψ] = ⟨φψ⟩_t - ⟨φ⟩_t ⟨ψ⟩_t`. -/
noncomputable def gibbsCov
    (L : (ι → ℝ) → ℝ) (t : ℝ) (φ ψ : (ι → ℝ) → ℝ) : ℝ :=
  gibbsExpectation L t (fun w => φ w * ψ w)
    - gibbsExpectation L t φ * gibbsExpectation L t ψ

/-- Definitional unfolding for `partitionFunction`. -/
lemma partitionFunction_def (L : (ι → ℝ) → ℝ) (t : ℝ) :
    partitionFunction L t = ∫ w : ι → ℝ, Real.exp (-(t * L w)) := rfl

/-- Definitional unfolding for `gibbsExpectation`. -/
lemma gibbsExpectation_def (L : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → ℝ) :
    gibbsExpectation L t φ =
      (∫ w : ι → ℝ, φ w * Real.exp (-(t * L w))) / partitionFunction L t := rfl

end Laplace.Multi
