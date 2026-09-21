/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib

/-!
# The direct force (regime 1)

The linear algebra of Proposition 4.1 and Corollary 4.2 of the working note *Patterning
flow*. With per-sample gradients `G = [g_1, …, g_n]`, observable gradients `A = [a_1, …, a_k]`,
the resolvent `R = (H + ρ)⁻¹` (any symmetric matrix here), and the Laplace susceptibility
`χ = -(1/n) Aᵀ R G`:

* `suscept_mul_transpose`: `χ χᵀ = (1/n) S` with `S = Aᵀ R C R A`, `C = (1/n) G Gᵀ`;
* `suscept_mulVec_omegaP`: `ε ω_P = -Gᵀ R A S⁻¹ dμ` solves the fundamental equation
  `χ (ε ω) = dμ`;
* `omegaP_minimal`: it is the minimal sum-of-squares solution (Euclidean norm);
* `omegaP_mean_zero`: it is mean-zero when `G 𝟙 = 0`;
* `force_omegaP`: the force `(1/n) G (ε ω_P) = -C R A S⁻¹ dμ`;
* `natgrad_*`: the `C = H` algebra of Corollary 4.2, `S = Aᵀ R A - ρ Aᵀ R² A` and
  `Aᵀ δw_∞ = dμ + ρ Aᵀ R² A S⁻¹ dμ` for `δw_∞ = R A S⁻¹ dμ`.

The dynamical statements (the shifts `δw_T`, `δw_∞`) are those of `Horizon.lean`.
-/

namespace Laplace.Patterning

open Matrix

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

noncomputable section

/-- Gradient second moment `C = (1/n) G Gᵀ`. -/
def gradCov (n : ℝ) (G : Matrix ι ν ℝ) : Matrix ι ι ℝ := (1 / n) • (G * Gᵀ)

/-- The Laplace susceptibility matrix `χ = -(1/n) Aᵀ R G`. -/
def suscept (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ) :
    Matrix κ ν ℝ := -((1 / n) • (Aᵀ * R * G))

/-- The Gram matrix `S = Aᵀ R C R A`. -/
def gram (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ) : Matrix κ κ ℝ :=
  Aᵀ * R * gradCov n G * R * A

/-- The minimal-norm weights `ε ω_P = -Gᵀ R A S⁻¹ dμ`. -/
def omegaP (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ) (dμ : κ → ℝ) :
    ν → ℝ := -((Gᵀ * R * A * (gram n A R G)⁻¹) *ᵥ dμ)

/-- The gradient-response force `(1/n) G ω`. -/
def force (n : ℝ) (G : Matrix ι ν ℝ) (ω : ν → ℝ) : ι → ℝ := (1 / n) • (G *ᵥ ω)

/-- `χ χᵀ = (1/n) S`. -/
theorem suscept_mul_transpose (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ)
    (hR : Rᵀ = R) :
    suscept n A R G * (suscept n A R G)ᵀ = (1 / n) • gram n A R G := by
  simp only [suscept, gram, gradCov, Matrix.transpose_neg, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hR, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [smul_neg, neg_neg, smul_smul]

/-- The weights `ω_P` are `χᵀ z` with `z = n S⁻¹ dμ`. -/
theorem omegaP_eq_transpose_mulVec (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ)
    (G : Matrix ι ν ℝ) (dμ : κ → ℝ) (hR : Rᵀ = R) (hn : n ≠ 0) :
    omegaP n A R G dμ = (suscept n A R G)ᵀ *ᵥ (n • ((gram n A R G)⁻¹ *ᵥ dμ)) := by
  simp only [omegaP, suscept, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hR, Matrix.neg_mul, Matrix.smul_mul, Matrix.neg_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_neg, smul_smul, one_div,
    mul_inv_cancel₀ hn, one_smul, Matrix.mul_assoc]

/-- **The fundamental equation is solved.** `χ ω_P = dμ` when `S` is invertible. -/
theorem suscept_mulVec_omegaP (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ)
    (dμ : κ → ℝ) (hR : Rᵀ = R) (hS : IsUnit (gram n A R G).det) :
    suscept n A R G *ᵥ omegaP n A R G dμ = dμ := by
  have hkey : suscept n A R G * (Gᵀ * R * A * (gram n A R G)⁻¹) = -1 := by
    have h1 : suscept n A R G * (Gᵀ * R * A * (gram n A R G)⁻¹)
        = -(gram n A R G * (gram n A R G)⁻¹) := by
      simp only [suscept, gram, gradCov, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc, hR]
    rw [h1, Matrix.mul_nonsing_inv _ hS]
  rw [omegaP, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hkey, Matrix.neg_mulVec, Matrix.one_mulVec,
    neg_neg]

/-- **Pythagoras for the least-squares solution.** If `ω = Mᵀ z` and `M ω' = M ω`, then
`|ω'|² = |ω|² + |ω' - ω|²`. -/
theorem sq_sum_eq_of_range_transpose (M : Matrix κ ν ℝ) (z : κ → ℝ) (ω' : ν → ℝ)
    (h : M *ᵥ ω' = M *ᵥ (Mᵀ *ᵥ z)) :
    ω' ⬝ᵥ ω' = (Mᵀ *ᵥ z) ⬝ᵥ (Mᵀ *ᵥ z) + (ω' - Mᵀ *ᵥ z) ⬝ᵥ (ω' - Mᵀ *ᵥ z) := by
  have horth : (Mᵀ *ᵥ z) ⬝ᵥ (ω' - Mᵀ *ᵥ z) = 0 := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_sub,
      ← Matrix.mulVec_transpose, h, sub_self, dotProduct_zero]
  have hexp : (ω' - Mᵀ *ᵥ z) ⬝ᵥ (ω' - Mᵀ *ᵥ z)
      = ω' ⬝ᵥ ω' - 2 * ((Mᵀ *ᵥ z) ⬝ᵥ ω') + (Mᵀ *ᵥ z) ⬝ᵥ (Mᵀ *ᵥ z) := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm ω' (Mᵀ *ᵥ z)]
    ring
  have h2 : (Mᵀ *ᵥ z) ⬝ᵥ ω' = (Mᵀ *ᵥ z) ⬝ᵥ (Mᵀ *ᵥ z) := by
    rw [dotProduct_sub] at horth
    linarith
  rw [hexp, h2]
  ring

/-- **Minimal norm.** Every solution `ω'` of `χ ω' = dμ` has `|ω'|² ≥ |ω_P|²`. -/
theorem omegaP_minimal (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ)
    (dμ : κ → ℝ) (hR : Rᵀ = R) (hn : n ≠ 0) (hS : IsUnit (gram n A R G).det)
    (ω' : ν → ℝ) (hω' : suscept n A R G *ᵥ ω' = dμ) :
    omegaP n A R G dμ ⬝ᵥ omegaP n A R G dμ ≤ ω' ⬝ᵥ ω' := by
  have hP := omegaP_eq_transpose_mulVec n A R G dμ hR hn
  have hsol := suscept_mulVec_omegaP n A R G dμ hR hS
  rw [hP] at hsol ⊢
  rw [sq_sum_eq_of_range_transpose (suscept n A R G) _ ω' (by rw [hω', hsol])]
  exact le_add_of_nonneg_right (dotProduct_self_star_nonneg _)

/-- **Mean zero.** If `G 𝟙 = 0` (the sum of the per-sample gradients vanishes) then
`𝟙 ⬝ ω_P = 0`. -/
theorem omegaP_mean_zero (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ)
    (dμ : κ → ℝ) (hG : G *ᵥ (fun _ => (1 : ℝ)) = 0) :
    (fun _ => (1 : ℝ)) ⬝ᵥ omegaP n A R G dμ = 0 := by
  simp only [omegaP, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, dotProduct_neg,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose, hG,
    Matrix.mulVec_zero, zero_dotProduct, neg_zero]

/-- **The force.** `(1/n) G ω_P = -C R A S⁻¹ dμ`. -/
theorem force_omegaP (n : ℝ) (A : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ)
    (dμ : κ → ℝ) :
    force n G (omegaP n A R G dμ) = -((gradCov n G * R * A * (gram n A R G)⁻¹) *ᵥ dμ) := by
  simp only [force, omegaP, gradCov, Matrix.mulVec_neg, Matrix.mulVec_mulVec, smul_neg,
    Matrix.smul_mulVec, Matrix.smul_mul, Matrix.mul_assoc]

/-! ### The case `C = H` (Corollary 4.2) -/

/-- `R (H + ρ) = 1` implies `R H R = R - ρ R²`. -/
theorem resolvent_mul_mul (H R : Matrix ι ι ℝ) (ρ : ℝ) (hR : R * (H + ρ • (1 : Matrix ι ι ℝ)) = 1) :
    R * H * R = R - ρ • (R * R) := by
  have h : R * H = 1 - ρ • R := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at hR
    exact eq_sub_of_add_eq hR
  rw [h, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]

/-- With `C = H` the Gram matrix is `Aᵀ R A - ρ Aᵀ R² A`. -/
theorem natgrad_gram (n : ℝ) (A : Matrix ι κ ℝ) (H R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ) (ρ : ℝ)
    (hC : gradCov n G = H) (hR : R * (H + ρ • (1 : Matrix ι ι ℝ)) = 1) :
    gram n A R G = Aᵀ * R * A - ρ • (Aᵀ * (R * R) * A) := by
  rw [gram, hC, show Aᵀ * R * H * R * A = Aᵀ * (R * H * R) * A by
    simp only [Matrix.mul_assoc], resolvent_mul_mul H R ρ hR, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-- With `C = H` the force is `-H R A S⁻¹ dμ`. -/
theorem natgrad_force (n : ℝ) (A : Matrix ι κ ℝ) (H R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ)
    (dμ : κ → ℝ) (hC : gradCov n G = H) :
    force n G (omegaP n A R G dμ) = -((H * R * A * (gram n A R G)⁻¹) *ᵥ dμ) := by
  rw [force_omegaP, hC]

/-- **The target is achieved up to the damping term.** For `δw_∞ = R A S⁻¹ dμ` with `C = H`,
`Aᵀ δw_∞ = dμ + ρ Aᵀ R² A S⁻¹ dμ`. -/
theorem natgrad_target (n : ℝ) (A : Matrix ι κ ℝ) (H R : Matrix ι ι ℝ) (G : Matrix ι ν ℝ)
    (dμ : κ → ℝ) (ρ : ℝ) (hC : gradCov n G = H) (hR : R * (H + ρ • (1 : Matrix ι ι ℝ)) = 1)
    (hS : IsUnit (gram n A R G).det) :
    Aᵀ *ᵥ ((R * A * (gram n A R G)⁻¹) *ᵥ dμ)
      = dμ + ρ • ((Aᵀ * (R * R) * A * (gram n A R G)⁻¹) *ᵥ dμ) := by
  have hgram := natgrad_gram n A H R G ρ hC hR
  have h1 : Aᵀ * R * A = gram n A R G + ρ • (Aᵀ * (R * R) * A) := by
    rw [hgram, sub_add_cancel]
  rw [Matrix.mulVec_mulVec,
    show Aᵀ * (R * A * (gram n A R G)⁻¹) = (Aᵀ * R * A) * (gram n A R G)⁻¹ by
      simp only [Matrix.mul_assoc],
    h1, Matrix.add_mul, Matrix.mul_nonsing_inv _ hS, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mul, Matrix.smul_mulVec]

end

end Laplace.Patterning
