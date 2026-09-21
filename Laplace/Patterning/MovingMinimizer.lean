/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.Jacobi

/-!
# The moving minimiser of Proposition 5.2

Proposition 5.2 of the working note *Patterning flow* deforms the loss to `L_s = L_n + s(ℓ_i - L_n)`,
follows the minimiser `w*(s)` and the Hessian `H(s) = ∇²L_s(w*(s))`, and differentiates
`log det H(s)` at `s = 0`. `Jacobi.lean` supplies the log-determinant derivative and the algebraic
identification; this file supplies the two calculus steps that connect them to the deformation:

* `movingMinimizer_deriv`: a differentiable curve of critical points of a parametrised gradient
  field `G s w` (with `∂_s G = g`, `∂_w G = H` at `(0, w₀)`) has derivative `w*'(0) = -H⁻¹ g`;
* `movingMinimizer_exists`: such a curve exists near `s = 0` when `G` is strictly differentiable
  and `H` is invertible, by the inverse function theorem applied to `(s, w) ↦ (s, G s w)`;
* `movingHessian_entry_deriv` and `logdet_response_deriv`: the chain rule for the moving Hessian
  and the derivative `d/ds log det H(s)|₀ = tr(B_i Σ) - d + (T:Σ)·w*'(0)`, which with
  `w*'(0) = -Σ g_i` is `tr(B_i Σ) - d - (Σ g_i)ᵀ(T:Σ)`, the right-hand side of eq. (primer_nlo)
  up to the factor `1/(2t²)` (`logdet_response_deriv_at_minimizer`).

The primer's next-to-leading covariance formula itself is not formalised here.
-/

namespace Laplace.Patterning

open Matrix Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The curve `s ↦ (s, w s)` has derivative `(1, v)` when `w` has derivative `v`. -/
lemma hasDerivAt_prod_curve {w : ℝ → ι → ℝ} {v : ι → ℝ} {s₀ : ℝ} (hw : HasDerivAt w v s₀) :
    HasDerivAt (fun s => ((s, w s) : ℝ × (ι → ℝ))) (1, v) s₀ :=
  (hasDerivAt_id s₀).prodMk hw

/-- **The derivative of the moving minimiser.** If `w` is a differentiable curve of critical
points of `G`, `w 0 = w₀`, and `DG(0, w₀)[σ, u] = σ g + H u` with `H` invertible, then
`w'(0) = -H⁻¹ g`. -/
theorem movingMinimizer_deriv (G : ℝ → (ι → ℝ) → (ι → ℝ)) (w : ℝ → ι → ℝ) (v w₀ g : ι → ℝ)
    (H : Matrix ι ι ℝ) (G' : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hw0 : w 0 = w₀) (hw : HasDerivAt w v 0)
    (hG : HasFDerivAt (fun p : ℝ × (ι → ℝ) => G p.1 p.2) G' (0, w₀))
    (hG' : ∀ σ u, G' (σ, u) = σ • g + H *ᵥ u)
    (hzero : ∀ s, G s (w s) = 0) (hH : IsUnit H.det) :
    v = -(H⁻¹ *ᵥ g) := by
  subst hw0
  have hcomp0 := hG.comp_hasDerivAt 0 (hasDerivAt_prod_curve hw)
  have hcomp : HasDerivAt (fun s => G s (w s)) (G' (1, v)) 0 := hcomp0
  have hconst : HasDerivAt (fun s => G s (w s)) 0 0 := by
    have : (fun s => G s (w s)) = fun _ => (0 : ι → ℝ) := funext hzero
    rw [this]
    exact hasDerivAt_const _ _
  have h0 : G' (1, v) = 0 := hcomp.unique hconst
  rw [hG', one_smul] at h0
  have hHv : H *ᵥ v = -g := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h0
  calc v = H⁻¹ *ᵥ (H *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hH, Matrix.one_mulVec]
    _ = -(H⁻¹ *ᵥ g) := by rw [hHv, Matrix.mulVec_neg]


/-! ### Existence of the moving minimiser (inverse function theorem) -/

/-- The derivative of `(s, w) ↦ (s, G s w)`: `(σ, u) ↦ (σ, G'(σ, u))`. -/
noncomputable def fwdDeriv (G' : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    ℝ × (ι → ℝ) →L[ℝ] ℝ × (ι → ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).prod G'

/-- Its inverse when `G'(σ, u) = σ g + H u` with `H` invertible: `(σ, y) ↦ (σ, H⁻¹(y - σ g))`. -/
noncomputable def invDeriv (H : Matrix ι ι ℝ) (g : ι → ℝ) :
    ℝ × (ι → ℝ) →L[ℝ] ℝ × (ι → ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).prod
    ((LinearMap.toContinuousLinearMap (Matrix.toLin' H⁻¹)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ) - (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).smulRight g))

lemma fwdDeriv_apply (G' : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)) (p : ℝ × (ι → ℝ)) :
    fwdDeriv G' p = (p.1, G' p) := by
  simp [fwdDeriv]

lemma invDeriv_apply (H : Matrix ι ι ℝ) (g : ι → ℝ) (p : ℝ × (ι → ℝ)) :
    invDeriv H g p = (p.1, H⁻¹ *ᵥ (p.2 - p.1 • g)) := by
  simp [invDeriv, Matrix.toLin'_apply, Matrix.mulVec_sub, Matrix.mulVec_smul]

lemma invDeriv_leftInverse (H : Matrix ι ι ℝ) (g : ι → ℝ) (G' : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hG' : ∀ σ u, G' (σ, u) = σ • g + H *ᵥ u) (hH : IsUnit H.det) :
    Function.LeftInverse (invDeriv H g) (fwdDeriv G') := by
  rintro ⟨σ, u⟩
  rw [fwdDeriv_apply, invDeriv_apply, hG']
  simp only [add_sub_cancel_left, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hH,
    Matrix.one_mulVec]

lemma invDeriv_rightInverse (H : Matrix ι ι ℝ) (g : ι → ℝ) (G' : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hG' : ∀ σ u, G' (σ, u) = σ • g + H *ᵥ u) (hH : IsUnit H.det) :
    Function.RightInverse (invDeriv H g) (fwdDeriv G') := by
  rintro ⟨σ, y⟩
  rw [invDeriv_apply, fwdDeriv_apply, hG']
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec,
    add_sub_cancel]

/-- The derivative of `(s, w) ↦ (s, G s w)` as a continuous linear equivalence. -/
noncomputable def fwdEquiv (H : Matrix ι ι ℝ) (g : ι → ℝ) (G' : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hG' : ∀ σ u, G' (σ, u) = σ • g + H *ᵥ u) (hH : IsUnit H.det) :
    (ℝ × (ι → ℝ)) ≃L[ℝ] (ℝ × (ι → ℝ)) :=
  ContinuousLinearEquiv.equivOfInverse (fwdDeriv G') (invDeriv H g)
    (invDeriv_leftInverse H g G' hG' hH) (invDeriv_rightInverse H g G' hG' hH)

/-- **Existence of the moving minimiser** (inverse function theorem). If `G 0 w₀ = 0`,
`(s, w) ↦ G s w` is strictly differentiable at `(0, w₀)` with derivative `(σ, u) ↦ σ g + H u`,
and `H` is invertible, there is a curve `w` of critical points through `w₀` with
`w'(0) = -H⁻¹ g`. (Criticality, not minimality, is what the theorem provides.) -/
theorem movingMinimizer_exists (G : ℝ → (ι → ℝ) → (ι → ℝ)) (w₀ g : ι → ℝ) (H : Matrix ι ι ℝ)
    (G' : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)) (hG0 : G 0 w₀ = 0)
    (hGs : HasStrictFDerivAt (fun p : ℝ × (ι → ℝ) => G p.1 p.2) G' (0, w₀))
    (hG' : ∀ σ u, G' (σ, u) = σ • g + H *ᵥ u) (hH : IsUnit H.det) :
    ∃ w : ℝ → ι → ℝ, w 0 = w₀ ∧ (∀ᶠ s in 𝓝 (0 : ℝ), G s (w s) = 0) ∧
      HasDerivAt w (-(H⁻¹ *ᵥ g)) 0 := by
  set Φ : ℝ × (ι → ℝ) → ℝ × (ι → ℝ) := fun p => (p.1, G p.1 p.2) with hΦdef
  let Φ' := fwdEquiv H g G' hG' hH
  have hΦ : HasStrictFDerivAt Φ (Φ' : ℝ × (ι → ℝ) →L[ℝ] ℝ × (ι → ℝ)) (0, w₀) :=
    (hasStrictFDerivAt_fst.prodMk hGs).congr_fderiv rfl
  have hΦa : Φ (0, w₀) = (0, 0) := by
    simp [hΦdef, hG0]
  refine ⟨fun s => (hΦ.localInverse Φ Φ' (0, w₀) (s, 0)).2, ?_, ?_, ?_⟩
  · have h := hΦ.localInverse_apply_image
    rw [hΦa] at h
    simp only [h]
  · have hev := hΦ.eventually_right_inverse
    rw [hΦa] at hev
    have ht : Tendsto (fun s : ℝ => ((s, 0) : ℝ × (ι → ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
      (continuous_id.prodMk continuous_const).tendsto' 0 _ rfl
    filter_upwards [ht.eventually hev] with s hs
    have h1 := congrArg Prod.fst hs
    have h2 := congrArg Prod.snd hs
    simp only [hΦdef] at h1 h2
    rw [h1] at h2
    exact h2
  · have hd := hΦ.to_localInverse
    rw [hΦa] at hd
    have hcurve : HasDerivAt (fun s : ℝ => ((s, 0) : ℝ × (ι → ℝ))) ((1, 0) : ℝ × (ι → ℝ)) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const _ _)
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt 0 hcurve
    have hsnd := (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)).hasFDerivAt.comp_hasDerivAt 0 hcomp
    refine hsnd.congr_deriv ?_
    simp [Φ', fwdEquiv, ContinuousLinearEquiv.symm_equivOfInverse,
      ContinuousLinearEquiv.equivOfInverse_apply, invDeriv_apply, Matrix.mulVec_neg]

/-! ### The moving Hessian -/

/-- **Chain rule for the moving Hessian.** If the entries of `Hess s w` are differentiable at
`(0, w₀)` with `D_ij[σ, u] = σ (B - H)_ij + ∑ k, T_kij u_k`, then along a curve `w` with
`w'(0) = v`, `d/ds Hess(s, w s)_ij|₀ = (B - H)_ij + (T·v)_ij`. -/
theorem movingHessian_entry_deriv (Hess : ℝ → (ι → ℝ) → Matrix ι ι ℝ)
    (D : ι → ι → ℝ × (ι → ℝ) →L[ℝ] ℝ) (w : ℝ → ι → ℝ) (v w₀ : ι → ℝ) (B H : Matrix ι ι ℝ)
    (T : ι → ι → ι → ℝ) (hw0 : w 0 = w₀) (hw : HasDerivAt w v 0)
    (hHess : ∀ i j, HasFDerivAt (fun p : ℝ × (ι → ℝ) => Hess p.1 p.2 i j) (D i j) (0, w₀))
    (hD : ∀ i j σ u, D i j (σ, u) = σ * (B i j - H i j) + ∑ k, T k i j * u k) (i j : ι) :
    HasDerivAt (fun s => Hess s (w s) i j) (((B - H) + tensorApply T v) i j) 0 := by
  subst hw0
  have h := (hHess i j).comp_hasDerivAt 0 (hasDerivAt_prod_curve hw)
  refine h.congr_deriv ?_
  rw [hD, Matrix.add_apply, Matrix.sub_apply, tensorApply, Matrix.of_apply, one_mul]

/-- **The log-volume derivative along the deformation** (eq. (logdet_response) of the note,
without the factor `1/(2t²)`): with `Hess 0 w₀ = H`, `Σ = H⁻¹` symmetric,
`d/ds log det Hess(s, w s)|₀ = tr(B Σ) - d + (T:Σ)·v`. -/
theorem logdet_response_deriv (Hess : ℝ → (ι → ℝ) → Matrix ι ι ℝ)
    (D : ι → ι → ℝ × (ι → ℝ) →L[ℝ] ℝ) (w : ℝ → ι → ℝ) (v w₀ : ι → ℝ) (B H : Matrix ι ι ℝ)
    (T : ι → ι → ι → ℝ) (hw0 : w 0 = w₀) (hw : HasDerivAt w v 0)
    (hHess : ∀ i j, HasFDerivAt (fun p : ℝ × (ι → ℝ) => Hess p.1 p.2 i j) (D i j) (0, w₀))
    (hD : ∀ i j σ u, D i j (σ, u) = σ * (B i j - H i j) + ∑ k, T k i j * u k)
    (hH0 : Hess 0 w₀ = H) (hdet : H.det ≠ 0) (hsymm : (H⁻¹)ᵀ = H⁻¹) :
    HasDerivAt (fun s => Real.log (Hess s (w s)).det)
      ((B * H⁻¹).trace - Fintype.card ι + ∑ j, tensorContract T H⁻¹ j * v j) 0 := by
  have hentries : ∀ i j,
      HasDerivAt (fun s => Hess s (w s) i j) (((B - H) + tensorApply T v) i j) 0 :=
    movingHessian_entry_deriv Hess D w v w₀ B H T hw0 hw hHess hD
  have hdet' : (Hess 0 (w 0)).det ≠ 0 := by rw [hw0, hH0]; exact hdet
  have h := hasDerivAt_log_det (fun s => Hess s (w s)) ((B - H) + tensorApply T v) 0 hentries hdet'
  rw [hw0, hH0] at h
  refine h.congr_deriv ?_
  exact logdet_response_algebra H⁻¹ H B T v (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet))
    hsymm

/-- **At the moving minimiser**, `v = -Σ g`, the log-volume derivative is
`tr(B Σ) - d - (Σ g)ᵀ (T:Σ)`. -/
theorem logdet_response_deriv_at_minimizer (Hess : ℝ → (ι → ℝ) → Matrix ι ι ℝ)
    (D : ι → ι → ℝ × (ι → ℝ) →L[ℝ] ℝ) (w : ℝ → ι → ℝ) (w₀ g : ι → ℝ) (B H : Matrix ι ι ℝ)
    (T : ι → ι → ι → ℝ) (hw0 : w 0 = w₀) (hw : HasDerivAt w (-(H⁻¹ *ᵥ g)) 0)
    (hHess : ∀ i j, HasFDerivAt (fun p : ℝ × (ι → ℝ) => Hess p.1 p.2 i j) (D i j) (0, w₀))
    (hD : ∀ i j σ u, D i j (σ, u) = σ * (B i j - H i j) + ∑ k, T k i j * u k)
    (hH0 : Hess 0 w₀ = H) (hdet : H.det ≠ 0) (hsymm : (H⁻¹)ᵀ = H⁻¹) :
    HasDerivAt (fun s => Real.log (Hess s (w s)).det)
      ((B * H⁻¹).trace - Fintype.card ι - ∑ j, tensorContract T H⁻¹ j * (H⁻¹ *ᵥ g) j) 0 := by
  have h := logdet_response_deriv Hess D w (-(H⁻¹ *ᵥ g)) w₀ B H T hw0 hw hHess hD hH0 hdet hsymm
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

end Laplace.Patterning
