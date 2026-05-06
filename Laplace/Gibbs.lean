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

/-! ## Algebraic infrastructure for `gibbsExpectation` and `gibbsCov`

The lemmas below give the bilinearity / scalar-pulling / constant-collapse
facts needed to manipulate Gibbs expectations and covariances of affine and
multilinear observables without unfolding the definitions. They are used
downstream by the affine-observable covariance lemmas (e.g.
`Laplace.OneD.Quartic.gibbsCov_first_order_rate_sharp` and the 2D analogues).

`Integrable` hypotheses are stated directly rather than bundled into a
typeclass: at the algebraic level, only `MeasureTheory.integral_add` requires
them, and the typeclass abstraction belongs at the layer where differentiation
under the integral is the load-bearing operation. -/

/-- Scalar-multiplication pulls out of the Gibbs expectation. No hypotheses:
when `Z(t) = 0` both sides are zero. -/
lemma gibbsExpectation_smul (L : ℝ → ℝ) (t : ℝ) (c : ℝ) (φ : ℝ → ℝ) :
    gibbsExpectation L t (fun x => c * φ x) = c * gibbsExpectation L t φ := by
  simp only [gibbsExpectation]
  rw [show (fun x => c * φ x * Real.exp (-(t * L x)))
        = (fun x => c * (φ x * Real.exp (-(t * L x)))) from by funext x; ring,
      integral_const_mul c (fun x => φ x * Real.exp (-(t * L x))),
      mul_div_assoc]

/-- The Gibbs expectation of the zero observable is zero, unconditionally. -/
lemma gibbsExpectation_zero (L : ℝ → ℝ) (t : ℝ) :
    gibbsExpectation L t (fun _ => 0) = 0 := by
  simp [gibbsExpectation]

/-- Additivity of the Gibbs expectation: requires integrability of each
weighted observable. -/
lemma gibbsExpectation_add (L : ℝ → ℝ) (t : ℝ) (φ₁ φ₂ : ℝ → ℝ)
    (h₁ : Integrable (fun x => φ₁ x * Real.exp (-(t * L x))))
    (h₂ : Integrable (fun x => φ₂ x * Real.exp (-(t * L x)))) :
    gibbsExpectation L t (fun x => φ₁ x + φ₂ x)
      = gibbsExpectation L t φ₁ + gibbsExpectation L t φ₂ := by
  simp only [gibbsExpectation]
  rw [show (fun x => (φ₁ x + φ₂ x) * Real.exp (-(t * L x)))
        = (fun x => φ₁ x * Real.exp (-(t * L x))
                  + φ₂ x * Real.exp (-(t * L x))) from by funext x; ring,
      integral_add h₁ h₂, add_div]

/-- Symmetry: `Cov_t[φ, ψ] = Cov_t[ψ, φ]`. -/
lemma gibbsCov_symm (L : ℝ → ℝ) (t : ℝ) (φ ψ : ℝ → ℝ) :
    gibbsCov L t φ ψ = gibbsCov L t ψ φ := by
  simp only [gibbsCov]
  rw [show (fun x => φ x * ψ x) = (fun x => ψ x * φ x) from by funext x; ring,
      mul_comm (gibbsExpectation L t φ)]

/-- Scalar pulls out of the left slot. No hypotheses. -/
lemma gibbsCov_smul_left (L : ℝ → ℝ) (t : ℝ) (c : ℝ) (φ ψ : ℝ → ℝ) :
    gibbsCov L t (fun x => c * φ x) ψ = c * gibbsCov L t φ ψ := by
  simp only [gibbsCov]
  rw [show (fun x => c * φ x * ψ x) = (fun x => c * (φ x * ψ x)) from
        by funext x; ring,
      gibbsExpectation_smul, gibbsExpectation_smul]
  ring

/-- Scalar pulls out of the right slot. -/
lemma gibbsCov_smul_right (L : ℝ → ℝ) (t : ℝ) (c : ℝ) (φ ψ : ℝ → ℝ) :
    gibbsCov L t φ (fun x => c * ψ x) = c * gibbsCov L t φ ψ := by
  rw [gibbsCov_symm, gibbsCov_smul_left, gibbsCov_symm]

/-- Constants in the left slot give zero covariance. Unconditional: when
`Z(t) = 0` every Gibbs expectation collapses to `0`, so both sides agree. -/
lemma gibbsCov_const_left (L : ℝ → ℝ) (t : ℝ) (c : ℝ) (ψ : ℝ → ℝ) :
    gibbsCov L t (fun _ => c) ψ = 0 := by
  by_cases hZ : partitionFunction L t = 0
  · simp [gibbsCov, gibbsExpectation, partitionFunction] at hZ ⊢
    simp [hZ]
  · simp only [gibbsCov]
    rw [show (fun x => (fun _ => c) x * ψ x) = (fun x => c * ψ x) from rfl,
        gibbsExpectation_smul, gibbsExpectation_const L t c hZ]
    ring

/-- Constants in the right slot give zero covariance. -/
lemma gibbsCov_const_right (L : ℝ → ℝ) (t : ℝ) (φ : ℝ → ℝ) (c : ℝ) :
    gibbsCov L t φ (fun _ => c) = 0 := by
  rw [gibbsCov_symm, gibbsCov_const_left]

/-- Additivity in the left slot. Requires integrability of each weighted
observable, both alone and against `ψ`. -/
lemma gibbsCov_add_left (L : ℝ → ℝ) (t : ℝ) (φ₁ φ₂ ψ : ℝ → ℝ)
    (h₁ : Integrable (fun x => φ₁ x * Real.exp (-(t * L x))))
    (h₂ : Integrable (fun x => φ₂ x * Real.exp (-(t * L x))))
    (h₁ψ : Integrable (fun x => φ₁ x * ψ x * Real.exp (-(t * L x))))
    (h₂ψ : Integrable (fun x => φ₂ x * ψ x * Real.exp (-(t * L x)))) :
    gibbsCov L t (fun x => φ₁ x + φ₂ x) ψ
      = gibbsCov L t φ₁ ψ + gibbsCov L t φ₂ ψ := by
  simp only [gibbsCov]
  rw [show (fun x => (φ₁ x + φ₂ x) * ψ x)
        = (fun x => φ₁ x * ψ x + φ₂ x * ψ x) from by funext x; ring,
      gibbsExpectation_add L t (fun x => φ₁ x * ψ x) (fun x => φ₂ x * ψ x) h₁ψ h₂ψ,
      gibbsExpectation_add L t φ₁ φ₂ h₁ h₂]
  ring

/-- Additivity in the right slot. -/
lemma gibbsCov_add_right (L : ℝ → ℝ) (t : ℝ) (φ ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : Integrable (fun x => ψ₁ x * Real.exp (-(t * L x))))
    (h₂ : Integrable (fun x => ψ₂ x * Real.exp (-(t * L x))))
    (h₁φ : Integrable (fun x => φ x * ψ₁ x * Real.exp (-(t * L x))))
    (h₂φ : Integrable (fun x => φ x * ψ₂ x * Real.exp (-(t * L x)))) :
    gibbsCov L t φ (fun x => ψ₁ x + ψ₂ x)
      = gibbsCov L t φ ψ₁ + gibbsCov L t φ ψ₂ := by
  have h₁φ' : Integrable (fun x => ψ₁ x * φ x * Real.exp (-(t * L x))) := by
    simpa [mul_comm] using h₁φ
  have h₂φ' : Integrable (fun x => ψ₂ x * φ x * Real.exp (-(t * L x))) := by
    simpa [mul_comm] using h₂φ
  rw [gibbsCov_symm L t φ (fun x => ψ₁ x + ψ₂ x),
      gibbsCov_add_left L t ψ₁ ψ₂ φ h₁ h₂ h₁φ' h₂φ',
      gibbsCov_symm L t ψ₁ φ, gibbsCov_symm L t ψ₂ φ]

/-- Zero observable on the left gives zero covariance. -/
lemma gibbsCov_zero_left (L : ℝ → ℝ) (t : ℝ) (ψ : ℝ → ℝ) :
    gibbsCov L t (fun _ => 0) ψ = 0 :=
  gibbsCov_const_left L t 0 ψ

/-- Zero observable on the right gives zero covariance. -/
lemma gibbsCov_zero_right (L : ℝ → ℝ) (t : ℝ) (φ : ℝ → ℝ) :
    gibbsCov L t φ (fun _ => 0) = 0 :=
  gibbsCov_const_right L t φ 0

end Laplace
