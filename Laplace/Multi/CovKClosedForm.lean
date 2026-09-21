/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.HessianRoute
import Laplace.Multi.TiltedGaussian

/-!
# `eq:covK` in closed form and the variance of the loss

For `Hinv = Σ = P⁻¹` and an observable `φ` with Hessian `P`, the seabed's second-order covariance
coefficient collapses:

* `φ = ½wᵀPw` (`Φ = 0`): `cov2Coefficient = ½ trASig B Σ − ⟨Σb, T:Σ⟩`;
* `φ = V` (`Φ = T`): `cov2Coefficient = ½ trASig B Σ − ½ ⟨Σb, T:Σ⟩`,

where `B`, `b` are the Hessian and gradient of `ψ` and `T = ∇³V`. With the quintic package of `V`
as an observable (`potentialObservableQuintic`) the rate theorem gives the note's `eq:covK` for the
loss in closed form (`covV_first_order_rate_posDef`), and with `ψ = V` the variance of the loss:
`|t² Var_t(V) − d/2| ≤ C/t` (`varV_first_order_rate_posDef`) — the regular-model value `d/2` of the
singular fluctuation.
-/

open Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Algebra of `matCLM P` and its inverse -/

theorem matCLM_inv_comp {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    (matCLM P⁻¹).comp (matCLM P) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  rw [matCLM_mul, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP.det_pos.ne'), matCLM_one]

theorem matCLM_inv_apply_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) :
    matCLM P⁻¹ (matCLM P v) = v := by
  have := congrArg (fun f : (ι → ℝ) →L[ℝ] (ι → ℝ) => f v) (matCLM_inv_comp hP)
  simpa using this

theorem dot_matCLM_inv_symm {P : Matrix ι ι ℝ} (hP : P.PosDef) (x y : ι → ℝ) :
    dot x (matCLM P⁻¹ y) = dot (matCLM P⁻¹ x) y := by
  have hinv : (P⁻¹).PosDef := Matrix.posDef_inv_iff.mpr hP
  have h := dotProduct_mulVec_symm hinv x y
  simp only [dot, matCLM_apply]
  change x ⬝ᵥ P⁻¹ *ᵥ y = (P⁻¹ *ᵥ x) ⬝ᵥ y
  rw [h, dotProduct_comm]

theorem trASig_comp_one (B Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    trASig (B.comp Hinv) (1 : (ι → ℝ) →L[ℝ] (ι → ℝ)) = trASig B Hinv := by
  simp [trASig]

theorem tensorContractMatrix_zero (Sig : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    tensorContractMatrix (0 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ) Sig = 0 := by
  funext i
  simp [tensorContractMatrix]

theorem comp_inv_comp_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) (B : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    (matCLM P).comp ((matCLM P⁻¹).comp (B.comp (matCLM P⁻¹))) = B.comp (matCLM P⁻¹) := by
  rw [← ContinuousLinearMap.comp_assoc (matCLM P) (matCLM P⁻¹) (B.comp (matCLM P⁻¹)),
    matCLM_comp_inv hP, ContinuousLinearMap.id_comp]

theorem inv_comp_comp_inv_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    (matCLM P⁻¹).comp ((matCLM P).comp (matCLM P⁻¹)) = matCLM P⁻¹ := by
  rw [matCLM_comp_inv hP, ContinuousLinearMap.comp_id]

/-! ### The closed forms -/

/-- `cov2Coefficient` for the quadratic observable `½wᵀPw`: `½ trASig B Σ − ⟨Σb, T:Σ⟩`. -/
theorem cov2Coefficient_quadObservable {V ψ : (ι → ℝ) → ℝ} {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {b : ι → ℝ} (hV : PotentialTensorApprox V (matCLM P)) (hψ : ObservableTensorApprox ψ b) :
    cov2Coefficient V (fun w : ι → ℝ => (1 / 2 : ℝ) * quadForm (matCLM P) w) ψ (matCLM P)
        (matCLM P⁻¹) 0 b hV (quadObservable P hP) hψ =
      (1 / 2 : ℝ) * trASig hψ.A (matCLM P⁻¹) -
        dot (matCLM P⁻¹ b) (tensorContractMatrix hV.T (matCLM P⁻¹)) := by
  unfold cov2Coefficient
  rw [show (quadObservable P hP).A = matCLM P from rfl, show (quadObservable P hP).Φ = 0 from rfl,
    tensorContractMatrix_zero, comp_inv_comp_eq hP, inv_comp_comp_inv_eq hP, trASig_comp_one,
    matCLM_inv_apply_matCLM hP, dot_matCLM_inv_symm hP]
  simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  ring

/-- `cov2Coefficient` for the loss itself: `½ trASig B Σ − ½ ⟨Σb, T:Σ⟩`. -/
theorem cov2Coefficient_potentialObservable {V ψ : (ι → ℝ) → ℝ} {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {b : ι → ℝ} (hV : PotentialTensorApprox V (matCLM P)) (hψ : ObservableTensorApprox ψ b) :
    cov2Coefficient V V ψ (matCLM P) (matCLM P⁻¹) 0 b hV (potentialObservable hP hV) hψ =
      (1 / 2 : ℝ) * trASig hψ.A (matCLM P⁻¹) -
        (1 / 2 : ℝ) * dot (matCLM P⁻¹ b) (tensorContractMatrix hV.T (matCLM P⁻¹)) := by
  unfold cov2Coefficient
  rw [show (potentialObservable hP hV).A = matCLM P from rfl,
    show (potentialObservable hP hV).Φ = hV.T from rfl, comp_inv_comp_eq hP,
    inv_comp_comp_inv_eq hP, trASig_comp_one, matCLM_inv_apply_matCLM hP, dot_matCLM_inv_symm hP]
  ring

/-! ### The loss as a quintic observable -/

/-- The potential's own odd-part quintic bound makes `V` a quintic observable. -/
noncomputable def potentialObservableQuintic {V : (ι → ℝ) → ℝ} {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (hV : PotentialQuinticApprox V (matCLM P)) : ObservableQuinticApprox V 0 where
  toObservableTensorApprox := potentialObservable hP hV.toPotentialTensorApprox
  Q_const := hV.Q_const
  Q_const_nn := hV.Q_const_nn
  φ_odd_quintic_bound := fun w hw => by
    have hr : (potentialObservable hP hV.toPotentialTensorApprox).jet_radius =
        min hV.local_radius hV.jet_radius := rfl
    rw [hr] at hw
    have hΦ : (potentialObservable hP hV.toPotentialTensorApprox).Φ = hV.T := rfl
    rw [hΦ]
    have := hV.V_odd_quintic_bound w (hw.trans (min_le_right _ _))
    simpa [dot] using this

/-! ### `eq:covK` and the variance of the loss -/

/-- **`eq:covK` for the loss, in closed form**: `t² Cov_t(V, ψ) → ½ tr(BΣ) − ½ ⟨Σb, T:Σ⟩`. -/
theorem covV_first_order_rate_posDef [Nonempty ι] (V ψ : (ι → ℝ) → ℝ) {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (b : ι → ℝ) (hV : PotentialQuinticApprox V (matCLM P))
    (hψ : ObservableTensorApprox ψ b) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * gibbsCov V t V ψ -
          ((1 / 2 : ℝ) * trASig hψ.A (matCLM P⁻¹) -
            (1 / 2 : ℝ) * dot (matCLM P⁻¹ b) (tensorContractMatrix hV.T (matCLM P⁻¹)))| ≤
        K / t := by
  have h := gibbsCov_first_order_rate_explicit_posDef V V ψ hP 0 b hV
    (potentialObservableQuintic hP hV) hψ rfl
  rwa [show (potentialObservableQuintic hP hV).toObservableTensorApprox =
    potentialObservable hP hV.toPotentialTensorApprox from rfl,
    cov2Coefficient_potentialObservable hP hV.toPotentialTensorApprox hψ] at h

/-- **`eq:covK` for the quadratic observable, in closed form**:
`t² Cov_t(½wᵀPw, ψ) → ½ tr(BΣ) − ⟨Σb, T:Σ⟩`. -/
theorem covK_closed_form_rate_posDef [Nonempty ι] (V ψ : (ι → ℝ) → ℝ) {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (b : ι → ℝ) (hV : PotentialQuinticApprox V (matCLM P))
    (hψ : ObservableTensorApprox ψ b) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * gibbsCov V t (fun w => (1 / 2 : ℝ) * quadForm (matCLM P) w) ψ -
          ((1 / 2 : ℝ) * trASig hψ.A (matCLM P⁻¹) -
            dot (matCLM P⁻¹ b) (tensorContractMatrix hV.T (matCLM P⁻¹)))| ≤ K / t := by
  have h := covK_first_order_rate_posDef V ψ hP b hV hψ
  rwa [cov2Coefficient_quadObservable hP hV.toPotentialTensorApprox hψ] at h

/-- **The variance of the loss**: `|t² Var_t(V) − d/2| ≤ C/t` for every regular potential. -/
theorem varV_first_order_rate_posDef [Nonempty ι] (V : (ι → ℝ) → ℝ) {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (hV : PotentialQuinticApprox V (matCLM P)) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * gibbsCov V t V V - (1 / 2 : ℝ) * Fintype.card ι| ≤ K / t := by
  obtain ⟨K, T₀, hT, h⟩ := covV_first_order_rate_posDef V V hP 0 hV
    (potentialObservable hP hV.toPotentialTensorApprox)
  refine ⟨K, T₀, hT, fun t ht => ?_⟩
  have := h t ht
  rw [show (potentialObservable hP hV.toPotentialTensorApprox).A = matCLM P from rfl,
    trASig_matCLM_inv hP, map_zero] at this
  simpa [dot] using this

/-- **The variance of the quadratic observable**: `|t² Var_t(½wᵀPw) − d/2| ≤ C/t`. -/
theorem varK_first_order_rate_posDef [Nonempty ι] (V : (ι → ℝ) → ℝ) {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (hV : PotentialQuinticApprox V (matCLM P)) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t ^ 2 * gibbsCov V t (fun w => (1 / 2 : ℝ) * quadForm (matCLM P) w)
          (fun w => (1 / 2 : ℝ) * quadForm (matCLM P) w) - (1 / 2 : ℝ) * Fintype.card ι| ≤
        K / t := by
  obtain ⟨K, T₀, hT, h⟩ := covK_closed_form_rate_posDef V _ hP 0 hV (quadObservable P hP)
  refine ⟨K, T₀, hT, fun t ht => ?_⟩
  have := h t ht
  rw [quadObservable_A, trASig_matCLM_inv hP, map_zero] at this
  simpa [dot] using this

end Laplace.Multi
