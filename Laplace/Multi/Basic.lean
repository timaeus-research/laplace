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

/-! ## Algebraic infrastructure for `gibbsExpectation` and `gibbsCov`

Multivariate analogues of the lemmas in `Laplace.Gibbs`. The proofs are
mechanically identical to the 1D versions (the underlying integration lemmas
`MeasureTheory.integral_const_mul` and `MeasureTheory.integral_add` are
parametric in the underlying measurable space). -/

/-- Constant observables: `⟨c⟩_t = c` whenever `Z(t) ≠ 0`. -/
lemma gibbsExpectation_const (L : (ι → ℝ) → ℝ) (t : ℝ) (c : ℝ)
    (hZ : partitionFunction L t ≠ 0) :
    gibbsExpectation L t (fun _ => c) = c := by
  have hZ' : (∫ w : ι → ℝ, Real.exp (-(t * L w))) ≠ 0 := hZ
  simp only [gibbsExpectation, partitionFunction]
  rw [integral_const_mul c (fun w => Real.exp (-(t * L w)))]
  field_simp

/-- Scalar-multiplication pulls out of the Gibbs expectation. No hypotheses:
when `Z(t) = 0` both sides are zero. -/
lemma gibbsExpectation_smul (L : (ι → ℝ) → ℝ) (t : ℝ) (c : ℝ) (φ : (ι → ℝ) → ℝ) :
    gibbsExpectation L t (fun w => c * φ w) = c * gibbsExpectation L t φ := by
  simp only [gibbsExpectation]
  rw [show (fun w => c * φ w * Real.exp (-(t * L w)))
        = (fun w => c * (φ w * Real.exp (-(t * L w)))) from by funext w; ring,
      integral_const_mul c (fun w => φ w * Real.exp (-(t * L w))),
      mul_div_assoc]

/-- The Gibbs expectation of the zero observable is zero, unconditionally. -/
lemma gibbsExpectation_zero (L : (ι → ℝ) → ℝ) (t : ℝ) :
    gibbsExpectation L t (fun _ => 0) = 0 := by
  simp [gibbsExpectation]

/-- Additivity of the Gibbs expectation: requires integrability of each
weighted observable. -/
lemma gibbsExpectation_add (L : (ι → ℝ) → ℝ) (t : ℝ) (φ₁ φ₂ : (ι → ℝ) → ℝ)
    (h₁ : Integrable (fun w => φ₁ w * Real.exp (-(t * L w))))
    (h₂ : Integrable (fun w => φ₂ w * Real.exp (-(t * L w)))) :
    gibbsExpectation L t (fun w => φ₁ w + φ₂ w)
      = gibbsExpectation L t φ₁ + gibbsExpectation L t φ₂ := by
  simp only [gibbsExpectation]
  rw [show (fun w => (φ₁ w + φ₂ w) * Real.exp (-(t * L w)))
        = (fun w => φ₁ w * Real.exp (-(t * L w))
                  + φ₂ w * Real.exp (-(t * L w))) from by funext w; ring,
      integral_add h₁ h₂, add_div]

/-- Symmetry: `Cov_t[φ, ψ] = Cov_t[ψ, φ]`. -/
lemma gibbsCov_symm (L : (ι → ℝ) → ℝ) (t : ℝ) (φ ψ : (ι → ℝ) → ℝ) :
    gibbsCov L t φ ψ = gibbsCov L t ψ φ := by
  simp only [gibbsCov]
  rw [show (fun w => φ w * ψ w) = (fun w => ψ w * φ w) from by funext w; ring,
      mul_comm (gibbsExpectation L t φ)]

/-- Scalar pulls out of the left slot. No hypotheses. -/
lemma gibbsCov_smul_left (L : (ι → ℝ) → ℝ) (t : ℝ) (c : ℝ) (φ ψ : (ι → ℝ) → ℝ) :
    gibbsCov L t (fun w => c * φ w) ψ = c * gibbsCov L t φ ψ := by
  simp only [gibbsCov]
  rw [show (fun w => c * φ w * ψ w) = (fun w => c * (φ w * ψ w)) from
        by funext w; ring,
      gibbsExpectation_smul, gibbsExpectation_smul]
  ring

/-- Scalar pulls out of the right slot. -/
lemma gibbsCov_smul_right (L : (ι → ℝ) → ℝ) (t : ℝ) (c : ℝ) (φ ψ : (ι → ℝ) → ℝ) :
    gibbsCov L t φ (fun w => c * ψ w) = c * gibbsCov L t φ ψ := by
  rw [gibbsCov_symm, gibbsCov_smul_left, gibbsCov_symm]

/-- Constants in the left slot give zero covariance. Unconditional: when
`Z(t) = 0` every Gibbs expectation collapses to `0`, so both sides agree. -/
lemma gibbsCov_const_left (L : (ι → ℝ) → ℝ) (t : ℝ) (c : ℝ) (ψ : (ι → ℝ) → ℝ) :
    gibbsCov L t (fun _ => c) ψ = 0 := by
  by_cases hZ : partitionFunction L t = 0
  · simp [gibbsCov, gibbsExpectation, partitionFunction] at hZ ⊢
    simp [hZ]
  · simp only [gibbsCov]
    rw [show (fun w => (fun _ => c) w * ψ w) = (fun w => c * ψ w) from rfl,
        gibbsExpectation_smul, gibbsExpectation_const L t c hZ]
    ring

/-- Constants in the right slot give zero covariance. -/
lemma gibbsCov_const_right (L : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → ℝ) (c : ℝ) :
    gibbsCov L t φ (fun _ => c) = 0 := by
  rw [gibbsCov_symm, gibbsCov_const_left]

/-- Additivity in the left slot. Requires integrability of each weighted
observable, both alone and against `ψ`. -/
lemma gibbsCov_add_left (L : (ι → ℝ) → ℝ) (t : ℝ) (φ₁ φ₂ ψ : (ι → ℝ) → ℝ)
    (h₁ : Integrable (fun w => φ₁ w * Real.exp (-(t * L w))))
    (h₂ : Integrable (fun w => φ₂ w * Real.exp (-(t * L w))))
    (h₁ψ : Integrable (fun w => φ₁ w * ψ w * Real.exp (-(t * L w))))
    (h₂ψ : Integrable (fun w => φ₂ w * ψ w * Real.exp (-(t * L w)))) :
    gibbsCov L t (fun w => φ₁ w + φ₂ w) ψ
      = gibbsCov L t φ₁ ψ + gibbsCov L t φ₂ ψ := by
  simp only [gibbsCov]
  rw [show (fun w => (φ₁ w + φ₂ w) * ψ w)
        = (fun w => φ₁ w * ψ w + φ₂ w * ψ w) from by funext w; ring,
      gibbsExpectation_add L t (fun w => φ₁ w * ψ w) (fun w => φ₂ w * ψ w) h₁ψ h₂ψ,
      gibbsExpectation_add L t φ₁ φ₂ h₁ h₂]
  ring

/-- Additivity in the right slot. -/
lemma gibbsCov_add_right (L : (ι → ℝ) → ℝ) (t : ℝ) (φ ψ₁ ψ₂ : (ι → ℝ) → ℝ)
    (h₁ : Integrable (fun w => ψ₁ w * Real.exp (-(t * L w))))
    (h₂ : Integrable (fun w => ψ₂ w * Real.exp (-(t * L w))))
    (h₁φ : Integrable (fun w => φ w * ψ₁ w * Real.exp (-(t * L w))))
    (h₂φ : Integrable (fun w => φ w * ψ₂ w * Real.exp (-(t * L w)))) :
    gibbsCov L t φ (fun w => ψ₁ w + ψ₂ w)
      = gibbsCov L t φ ψ₁ + gibbsCov L t φ ψ₂ := by
  have h₁φ' : Integrable (fun w => ψ₁ w * φ w * Real.exp (-(t * L w))) := by
    simpa [mul_comm] using h₁φ
  have h₂φ' : Integrable (fun w => ψ₂ w * φ w * Real.exp (-(t * L w))) := by
    simpa [mul_comm] using h₂φ
  rw [gibbsCov_symm L t φ (fun w => ψ₁ w + ψ₂ w),
      gibbsCov_add_left L t ψ₁ ψ₂ φ h₁ h₂ h₁φ' h₂φ',
      gibbsCov_symm L t ψ₁ φ, gibbsCov_symm L t ψ₂ φ]

/-- Zero observable on the left gives zero covariance. -/
lemma gibbsCov_zero_left (L : (ι → ℝ) → ℝ) (t : ℝ) (ψ : (ι → ℝ) → ℝ) :
    gibbsCov L t (fun _ => 0) ψ = 0 :=
  gibbsCov_const_left L t 0 ψ

/-- Zero observable on the right gives zero covariance. -/
lemma gibbsCov_zero_right (L : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → ℝ) :
    gibbsCov L t φ (fun _ => 0) = 0 :=
  gibbsCov_const_right L t φ 0

end Laplace.Multi
