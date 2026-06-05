import Laplace.Multi.Basic

/-!
# Affine-bilinear specialisation of the multi-index Gibbs covariance

The multi-index analogue of `Laplace/AffineBilinearCov.lean` (the
1D version, Tide I3). For the multi-index Gibbs measure
`exp(-t · L(w)) dw` on `(ι → ℝ)`, the unperturbed covariance is
bilinear in `(φ, ψ)`; chaining the algebra in `Laplace/Multi/Basic.lean`
(`Laplace.Multi.gibbsCov_add_left/right`,
`gibbsCov_smul_left/right`, `gibbsCov_const_left/right`),

  `Cov_t[a₁·φ + b₁, a₂·ψ + b₂] = a₁·a₂ · Cov_t[φ, ψ]`

is the closed form. This is the natural first consumer of the
multi-index `gibbsCov` algebra and the multi-index mirror of I3.
-/

open MeasureTheory

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- Affine-input reduction on the left slot (multi-index version):
an affine combination `a · φ + b` reduces the covariance to a scalar
multiple of the base. Constants drop by `gibbsCov_const_left`; scalars
factor by `gibbsCov_smul_left`. -/
theorem gibbsCov_affine_left
    (L : (ι → ℝ) → ℝ) (t : ℝ) (a b : ℝ) (φ ψ : (ι → ℝ) → ℝ)
    (h_exp : Integrable (fun w : ι → ℝ => Real.exp (-(t * L w))))
    (h_φ : Integrable (fun w : ι → ℝ => φ w * Real.exp (-(t * L w))))
    (h_ψ : Integrable (fun w : ι → ℝ => ψ w * Real.exp (-(t * L w))))
    (h_φψ : Integrable (fun w : ι → ℝ => φ w * ψ w * Real.exp (-(t * L w)))) :
    gibbsCov L t (fun w => a * φ w + b) ψ = a * gibbsCov L t φ ψ := by
  have h₁ : Integrable (fun w : ι → ℝ => (a * φ w) * Real.exp (-(t * L w))) := by
    have := h_φ.const_mul a
    simpa [mul_assoc] using this
  have h₂ : Integrable (fun w : ι → ℝ => b * Real.exp (-(t * L w))) :=
    h_exp.const_mul b
  have h₁ψ : Integrable (fun w : ι → ℝ => (a * φ w) * ψ w * Real.exp (-(t * L w))) := by
    have := h_φψ.const_mul a
    simpa [mul_assoc] using this
  have h₂ψ : Integrable (fun w : ι → ℝ => b * ψ w * Real.exp (-(t * L w))) := by
    have := h_ψ.const_mul b
    simpa [mul_assoc] using this
  have eq : (fun w : ι → ℝ => a * φ w + b)
              = (fun w => (a * φ w) + (fun _ : ι → ℝ => b) w) := rfl
  rw [eq,
      gibbsCov_add_left L t (fun w => a * φ w) (fun _ => b) ψ h₁ h₂ h₁ψ h₂ψ,
      gibbsCov_smul_left L t a φ ψ,
      gibbsCov_const_left L t b ψ,
      add_zero]

/-- Affine-input reduction on the right slot. -/
theorem gibbsCov_affine_right
    (L : (ι → ℝ) → ℝ) (t : ℝ) (a b : ℝ) (φ ψ : (ι → ℝ) → ℝ)
    (h_exp : Integrable (fun w : ι → ℝ => Real.exp (-(t * L w))))
    (h_φ : Integrable (fun w : ι → ℝ => φ w * Real.exp (-(t * L w))))
    (h_ψ : Integrable (fun w : ι → ℝ => ψ w * Real.exp (-(t * L w))))
    (h_φψ : Integrable (fun w : ι → ℝ => φ w * ψ w * Real.exp (-(t * L w)))) :
    gibbsCov L t φ (fun w => a * ψ w + b) = a * gibbsCov L t φ ψ := by
  have h_ψφ : Integrable (fun w : ι → ℝ => ψ w * φ w * Real.exp (-(t * L w))) := by
    simpa [mul_comm] using h_φψ
  rw [gibbsCov_symm L t φ (fun w => a * ψ w + b),
      gibbsCov_affine_left L t a b ψ φ h_exp h_ψ h_φ h_ψφ,
      gibbsCov_symm L t ψ φ]

/-- The headline affine-bilinear identity (multi-index version): an
affine input on each slot collapses to the product of the linear
scalars times the base covariance. -/
theorem gibbsCov_affine_affine
    (L : (ι → ℝ) → ℝ) (t : ℝ) (a₁ b₁ a₂ b₂ : ℝ) (φ ψ : (ι → ℝ) → ℝ)
    (h_exp : Integrable (fun w : ι → ℝ => Real.exp (-(t * L w))))
    (h_φ : Integrable (fun w : ι → ℝ => φ w * Real.exp (-(t * L w))))
    (h_ψ : Integrable (fun w : ι → ℝ => ψ w * Real.exp (-(t * L w))))
    (h_φψ : Integrable (fun w : ι → ℝ => φ w * ψ w * Real.exp (-(t * L w)))) :
    gibbsCov L t (fun w => a₁ * φ w + b₁) (fun w => a₂ * ψ w + b₂)
      = a₁ * a₂ * gibbsCov L t φ ψ := by
  have h_ψ' : Integrable
      (fun w : ι → ℝ => (a₂ * ψ w + b₂) * Real.exp (-(t * L w))) := by
    have eq : (fun w : ι → ℝ => (a₂ * ψ w + b₂) * Real.exp (-(t * L w))) =
              (fun w => a₂ * (ψ w * Real.exp (-(t * L w))) +
                        b₂ * Real.exp (-(t * L w))) := by
      funext w; ring
    rw [eq]
    exact (h_ψ.const_mul a₂).add (h_exp.const_mul b₂)
  have h_φψ' : Integrable
      (fun w : ι → ℝ => φ w * (a₂ * ψ w + b₂) * Real.exp (-(t * L w))) := by
    have eq : (fun w : ι → ℝ => φ w * (a₂ * ψ w + b₂) * Real.exp (-(t * L w))) =
              (fun w => a₂ * (φ w * ψ w * Real.exp (-(t * L w))) +
                        b₂ * (φ w * Real.exp (-(t * L w)))) := by
      funext w; ring
    rw [eq]
    exact (h_φψ.const_mul a₂).add (h_φ.const_mul b₂)
  rw [gibbsCov_affine_left L t a₁ b₁ φ (fun w => a₂ * ψ w + b₂)
        h_exp h_φ h_ψ' h_φψ',
      gibbsCov_affine_right L t a₂ b₂ φ ψ h_exp h_φ h_ψ h_φψ,
      ← mul_assoc]

end Laplace.Multi
