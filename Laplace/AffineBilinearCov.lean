import Laplace.Gibbs

/-!
# Affine-bilinear specialisation of the Gibbs covariance

For a 1D Gibbs measure `exp(-t·L(x)) dx`, the unperturbed covariance
`gibbsCov L t φ ψ = ⟨φψ⟩ - ⟨φ⟩⟨ψ⟩` is bilinear in `(φ, ψ)`. Composing the
algebra introduced in `Laplace.Gibbs` (`gibbsCov_add_left/right`,
`gibbsCov_smul_left/right`, `gibbsCov_const_left/right`), this file
records the *affine-bilinear* specialisation: shifting either observable
by an additive constant leaves the covariance unchanged, and rescaling
by a scalar pulls a factor out, so

  `Cov_t[a₁·φ + b₁, a₂·ψ + b₂] = a₁·a₂ · Cov_t[φ, ψ]`

is the closed form. This was Tide 12 Candidate B (deferred from the 2D
pure-quartic refactor) and is the first non-trivial consumer of the
gibbsCov algebra landed in Tide I2.
-/

open Real MeasureTheory

namespace Laplace

/-- Affine-input reduction on the left slot: an affine combination
`a · φ + b` reduces the covariance to a scalar multiple of the base.
The constant offset `b` contributes zero (covariance with a constant
is zero); the scalar `a` pulls out via bilinearity. -/
theorem gibbsCov_affine_left
    (L : ℝ → ℝ) (t : ℝ) (a b : ℝ) (φ ψ : ℝ → ℝ)
    (h_exp : Integrable (fun x => Real.exp (-(t * L x))))
    (h_φ : Integrable (fun x => φ x * Real.exp (-(t * L x))))
    (h_ψ : Integrable (fun x => ψ x * Real.exp (-(t * L x))))
    (h_φψ : Integrable (fun x => φ x * ψ x * Real.exp (-(t * L x)))) :
    gibbsCov L t (fun x => a * φ x + b) ψ = a * gibbsCov L t φ ψ := by
  have h₁ : Integrable (fun x => (a * φ x) * Real.exp (-(t * L x))) := by
    have := h_φ.const_mul a
    simpa [mul_assoc] using this
  have h₂ : Integrable (fun x => b * Real.exp (-(t * L x))) :=
    h_exp.const_mul b
  have h₁ψ : Integrable (fun x => (a * φ x) * ψ x * Real.exp (-(t * L x))) := by
    have := h_φψ.const_mul a
    simpa [mul_assoc] using this
  have h₂ψ : Integrable (fun x => b * ψ x * Real.exp (-(t * L x))) := by
    have := h_ψ.const_mul b
    simpa [mul_assoc] using this
  have eq : (fun x => a * φ x + b) = (fun x => (a * φ x) + (fun _ : ℝ => b) x) :=
    rfl
  rw [eq,
      gibbsCov_add_left L t (fun x => a * φ x) (fun _ => b) ψ h₁ h₂ h₁ψ h₂ψ,
      gibbsCov_smul_left L t a φ ψ,
      gibbsCov_const_left L t b ψ,
      add_zero]

/-- Affine-input reduction on the right slot. -/
theorem gibbsCov_affine_right
    (L : ℝ → ℝ) (t : ℝ) (a b : ℝ) (φ ψ : ℝ → ℝ)
    (h_exp : Integrable (fun x => Real.exp (-(t * L x))))
    (h_φ : Integrable (fun x => φ x * Real.exp (-(t * L x))))
    (h_ψ : Integrable (fun x => ψ x * Real.exp (-(t * L x))))
    (h_φψ : Integrable (fun x => φ x * ψ x * Real.exp (-(t * L x)))) :
    gibbsCov L t φ (fun x => a * ψ x + b) = a * gibbsCov L t φ ψ := by
  have h_ψφ : Integrable (fun x => ψ x * φ x * Real.exp (-(t * L x))) := by
    simpa [mul_comm] using h_φψ
  rw [gibbsCov_symm L t φ (fun x => a * ψ x + b),
      gibbsCov_affine_left L t a b ψ φ h_exp h_ψ h_φ h_ψφ,
      gibbsCov_symm L t ψ φ]

/-- The headline affine-bilinear identity: an affine input on each slot
collapses to the product of the linear scalars times the base
covariance. -/
theorem gibbsCov_affine_affine
    (L : ℝ → ℝ) (t : ℝ) (a₁ b₁ a₂ b₂ : ℝ) (φ ψ : ℝ → ℝ)
    (h_exp : Integrable (fun x => Real.exp (-(t * L x))))
    (h_φ : Integrable (fun x => φ x * Real.exp (-(t * L x))))
    (h_ψ : Integrable (fun x => ψ x * Real.exp (-(t * L x))))
    (h_φψ : Integrable (fun x => φ x * ψ x * Real.exp (-(t * L x)))) :
    gibbsCov L t (fun x => a₁ * φ x + b₁) (fun x => a₂ * ψ x + b₂)
      = a₁ * a₂ * gibbsCov L t φ ψ := by
  have h_ψ' : Integrable
      (fun x => (a₂ * ψ x + b₂) * Real.exp (-(t * L x))) := by
    have eq : (fun x => (a₂ * ψ x + b₂) * Real.exp (-(t * L x))) =
              (fun x => a₂ * (ψ x * Real.exp (-(t * L x))) +
                        b₂ * Real.exp (-(t * L x))) := by
      funext x; ring
    rw [eq]
    exact (h_ψ.const_mul a₂).add (h_exp.const_mul b₂)
  have h_φψ' : Integrable
      (fun x => φ x * (a₂ * ψ x + b₂) * Real.exp (-(t * L x))) := by
    have eq : (fun x => φ x * (a₂ * ψ x + b₂) * Real.exp (-(t * L x))) =
              (fun x => a₂ * (φ x * ψ x * Real.exp (-(t * L x))) +
                        b₂ * (φ x * Real.exp (-(t * L x)))) := by
      funext x; ring
    rw [eq]
    exact (h_φψ.const_mul a₂).add (h_φ.const_mul b₂)
  rw [gibbsCov_affine_left L t a₁ b₁ φ (fun x => a₂ * ψ x + b₂)
        h_exp h_φ h_ψ' h_φψ',
      gibbsCov_affine_right L t a₂ b₂ φ ψ h_exp h_φ h_ψ h_φψ,
      ← mul_assoc]

end Laplace
