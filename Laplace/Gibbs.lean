import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gibbs measures, partition functions, and expectations

For a smooth potential `L : ℝ → ℝ` and an inverse-temperature parameter `t > 0`,
this file defines

* `partitionFunction L t : ℝ := ∫ x, exp(-t · L x)`,
* `gibbsExpectation L t φ : ℝ := (∫ x, φ x · exp(-t · L x)) / partitionFunction L t`,
* `gibbsCov L t φ ψ : ℝ :=
     gibbsExpectation L t (φ * ψ) - gibbsExpectation L t φ * gibbsExpectation L t ψ`.

These are the 1D versions corresponding to the primer's
`Z(t)`, `⟨·⟩_t`, and `Cov_t[φ, ψ]` (with prior `π ≡ 1`).
The asymptotic-expansion theorems live in subsequent files; this file
defines the objects and proves only basic algebraic identities.

## Notation

* `⟨φ⟩[L, t]` for `gibbsExpectation L t φ` (scoped).
* The covariance has no special notation since it is rarely used in isolation.
-/

open Real MeasureTheory

namespace Laplace

/-- Partition function of the Gibbs measure `exp(-t · L(x)) dx` on `ℝ`. -/
noncomputable def partitionFunction (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-(t * L x))

/-- Gibbs expectation `⟨φ⟩_t = (1/Z(t)) · ∫ φ(x) exp(-t L(x)) dx`. -/
noncomputable def gibbsExpectation (L : ℝ → ℝ) (t : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, φ x * Real.exp (-(t * L x))) / partitionFunction L t

/-- Gibbs covariance `Cov_t[φ, ψ] = ⟨φψ⟩_t - ⟨φ⟩_t ⟨ψ⟩_t`. -/
noncomputable def gibbsCov
    (L : ℝ → ℝ) (t : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  gibbsExpectation L t (fun x => φ x * ψ x)
    - gibbsExpectation L t φ * gibbsExpectation L t ψ

scoped notation "⟨" φ "⟩[" L ", " t "]" => gibbsExpectation L t φ

/-- The partition function, expanded. -/
lemma partitionFunction_def (L : ℝ → ℝ) (t : ℝ) :
    partitionFunction L t = ∫ x : ℝ, Real.exp (-(t * L x)) := rfl

/-- The Gibbs expectation, expanded. -/
lemma gibbsExpectation_def (L : ℝ → ℝ) (t : ℝ) (φ : ℝ → ℝ) :
    gibbsExpectation L t φ =
      (∫ x : ℝ, φ x * Real.exp (-(t * L x))) / partitionFunction L t := rfl

/-- Constant observables: `⟨c⟩_t = c` whenever `Z(t) ≠ 0`. -/
lemma gibbsExpectation_const (L : ℝ → ℝ) (t : ℝ) (c : ℝ)
    (hZ : partitionFunction L t ≠ 0) :
    gibbsExpectation L t (fun _ => c) = c := by
  have hZ' : (∫ x : ℝ, Real.exp (-(t * L x))) ≠ 0 := hZ
  simp only [gibbsExpectation, partitionFunction]
  rw [integral_const_mul c (fun x => Real.exp (-(t * L x)))]
  field_simp

end Laplace
