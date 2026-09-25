/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthLPChart

/-!
# Solved-pair independence of the face constant

Astra round 11, item (c). The face theorem parametrises the face
`F = {α ≥ 0 | κ·α = δ, Q·α = γ}` by `k` free coordinates and two solved ones, and its constant
`vol(F')/|det M|` (`F'` the projection of `F` to the free coordinates, `M` the `2 × 2` matrix of
the solved pair) looks as if it depended on the choice. It does not: for a permutation `σ` of
the active coordinates, with both solved pairs nondegenerate,
`vol(F'_σ)/|det M_σ| = vol(F')/|det M|` (`volume_facePolytope_div_det_perm`), hence for two
splittings `e₁, e₂ : Fin k ⊕ Fin 2 ≃ ι` of a chart (`faceConst_eq`).

The route (Astra): the augmented matrix `augMat κ Q = [[1, 0], [A, M']]`, `α ↦ (α_free, κ·α, Q·α)`,
has `|det| = |det M|`; the face polytope is the set of `w` whose lift
`augMat⁻¹ (w, δ, γ)` is nonnegative (`mem_facePolytope_iff_augInv_nonneg`); the transition
`w ↦ (augMat_σ *ᵥ (lift w ∘ σ))_free` between the two parametrisations is affine with linear
part the top-left block `L` of `B = augMat_σ · P_σ · augMat⁻¹`, whose lower blocks are `0` and
`1`, so `det B = det L` and `|det L| = |det M_σ|/|det M|`; the affine change of variables
(`addHaar_image_linearMap`, translation invariance) gives `vol(F'_σ) = |det L| vol(F')`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-- The augmented matrix of a splitting: `α ↦ (α_free, κ·α, Q·α)`. -/
def augMat (κ Q : Fin k ⊕ Fin 2 → ℝ) : Matrix (Fin k ⊕ Fin 2) (Fin k ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks 1 0 (Matrix.of ![fun i ↦ κ (Sum.inl i), fun i ↦ Q (Sum.inl i)])
    (Matrix.of ![fun j ↦ κ (Sum.inr j), fun j ↦ Q (Sum.inr j)])

theorem augMat_mulVec (κ Q : Fin k ⊕ Fin 2 → ℝ) (α : Fin k ⊕ Fin 2 → ℝ) :
    augMat κ Q *ᵥ α =
      Sum.elim (fun i ↦ α (Sum.inl i)) ![∑ s, κ s * α s, ∑ s, Q s * α s] := by
  rw [augMat, Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  funext s
  rcases s with i | j
  · rfl
  · simp only [Sum.elim_inr, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Function.comp]
    fin_cases j <;> simp [Fintype.sum_sum_type]

theorem augMat_det (κ Q : Fin k ⊕ Fin 2 → ℝ) : (augMat κ Q).det = -(transMat κ Q).det := by
  rw [augMat, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_fin_two,
    Matrix.det_fin_two]
  simp [transMat]
  ring

theorem augMat_det_ne_zero {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0) :
    (augMat κ Q).det ≠ 0 := by
  rw [augMat_det]
  exact neg_ne_zero.mpr hΔ

/-- The lift of a free point `w` to the affine constraint set: `augMat⁻¹ (w, δ, γ)`. -/
noncomputable def faceLift (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ : ℝ) (w : Fin k → ℝ) :
    Fin k ⊕ Fin 2 → ℝ :=
  (augMat κ Q)⁻¹ *ᵥ Sum.elim w ![δ, γ]

theorem augMat_mulVec_faceLift {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (δ γ : ℝ) (w : Fin k → ℝ) :
    augMat κ Q *ᵥ faceLift κ Q δ γ w = Sum.elim w ![δ, γ] := by
  unfold faceLift
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    (augMat_det_ne_zero hΔ)), Matrix.one_mulVec]

/-- The lift is the unique point of the affine constraint set over `w`. -/
theorem faceLift_eq_of {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0) {δ γ : ℝ}
    {w : Fin k → ℝ} {α : Fin k ⊕ Fin 2 → ℝ} (hw : ∀ i, α (Sum.inl i) = w i)
    (hκ : ∑ s, κ s * α s = δ) (hQ : ∑ s, Q s * α s = γ) : faceLift κ Q δ γ w = α := by
  unfold faceLift
  have h : augMat κ Q *ᵥ α = Sum.elim w ![δ, γ] := by
    rw [augMat_mulVec, hκ, hQ]
    congr 1
    funext i
    exact hw i
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
    (augMat_det_ne_zero hΔ)), Matrix.one_mulVec]

theorem faceLift_inl {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0) (δ γ : ℝ)
    (w : Fin k → ℝ) (i : Fin k) : faceLift κ Q δ γ w (Sum.inl i) = w i := by
  have h := congrFun (augMat_mulVec_faceLift hΔ δ γ w) (Sum.inl i)
  rw [augMat_mulVec] at h
  simpa using h

theorem faceLift_sum_κ {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0) (δ γ : ℝ)
    (w : Fin k → ℝ) : ∑ s, κ s * faceLift κ Q δ γ w s = δ := by
  have h := congrFun (augMat_mulVec_faceLift hΔ δ γ w) (Sum.inr 0)
  rw [augMat_mulVec] at h
  simpa using h

theorem faceLift_sum_Q {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0) (δ γ : ℝ)
    (w : Fin k → ℝ) : ∑ s, Q s * faceLift κ Q δ γ w s = γ := by
  have h := congrFun (augMat_mulVec_faceLift hΔ δ γ w) (Sum.inr 1)
  rw [augMat_mulVec] at h
  simpa using h

/-- The solved pair of the lift is `fibreA − fibreCoef ⬝ w`. -/
theorem faceLift_inr {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0) (δ γ : ℝ)
    (w : Fin k → ℝ) (j : Fin 2) :
    faceLift κ Q δ γ w (Sum.inr j) = fibreA κ Q δ γ j - fibreCoef κ Q j ⬝ᵥ w := by
  set y : Fin 2 → ℝ := (transMat κ Q)⁻¹ *ᵥ (0 - transShift κ Q δ γ 1 w) with hy
  have hyj : ∀ j, y j = fibreA κ Q δ γ j - fibreCoef κ Q j ⬝ᵥ w := by
    intro j
    rw [hy, inv_mulVec_sub_shift, mul_one]
    simp [fibreB]
  have hM : transMat κ Q *ᵥ y + transShift κ Q δ γ 1 w = 0 := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΔ),
      Matrix.one_mulVec]
    simp
  rw [transMat_mulVec_add_shift] at hM
  have h0 := congrFun hM 0
  have h1 := congrFun hM 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, mul_one] at h0 h1
  have := faceLift_eq_of hΔ (δ := δ) (γ := γ) (α := Sum.elim w y) (w := w) (fun i ↦ rfl)
    (by linarith) (by linarith)
  rw [this, Sum.elim_inr, hyj]

/-- **The face polytope is the set of free points with a nonnegative lift.** -/
theorem mem_facePolytope_iff_faceLift_nonneg {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (δ γ : ℝ) (w : Fin k → ℝ) :
    w ∈ facePolytope κ Q δ γ ↔ ∀ s, 0 ≤ faceLift κ Q δ γ w s := by
  unfold facePolytope poly2
  rw [Set.mem_ofPred_eq, Sum.forall]
  simp only [faceLift_inl hΔ, faceLift_inr hΔ, Fin.forall_fin_two, sub_nonneg]

/-- The permutation matrix acting on a vector by precomposition. -/
theorem permMatrix_mulVec' (σ : Equiv.Perm (Fin k ⊕ Fin 2)) (v : Fin k ⊕ Fin 2 → ℝ) :
    σ.permMatrix ℝ *ᵥ v = v ∘ σ :=
  Matrix.permMatrix_mulVec σ

/-- The transition matrix between two parametrisations. -/
noncomputable def transitionMat (κ Q : Fin k ⊕ Fin 2 → ℝ) (σ : Equiv.Perm (Fin k ⊕ Fin 2)) :
    Matrix (Fin k ⊕ Fin 2) (Fin k ⊕ Fin 2) ℝ :=
  augMat (κ ∘ σ) (Q ∘ σ) * σ.permMatrix ℝ * (augMat κ Q)⁻¹

theorem transitionMat_mulVec {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (σ : Equiv.Perm (Fin k ⊕ Fin 2)) (w : Fin k → ℝ) (v : Fin 2 → ℝ) :
    transitionMat κ Q σ *ᵥ Sum.elim w v =
      Sum.elim (fun i ↦ faceLift κ Q (v 0) (v 1) w (σ (Sum.inl i))) v := by
  have hv : ![v 0, v 1] = v := by
    funext j
    fin_cases j <;> rfl
  unfold transitionMat
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hlift : (augMat κ Q)⁻¹ *ᵥ Sum.elim w v = faceLift κ Q (v 0) (v 1) w := by
    unfold faceLift
    rw [hv]
  rw [hlift, permMatrix_mulVec', augMat_mulVec]
  congr 1
  funext j
  fin_cases j
  · exact (Equiv.sum_comp σ (fun s ↦ κ s * faceLift κ Q (v 0) (v 1) w s)).trans
      (faceLift_sum_κ hΔ (v 0) (v 1) w)
  · exact (Equiv.sum_comp σ (fun s ↦ Q s * faceLift κ Q (v 0) (v 1) w s)).trans
      (faceLift_sum_Q hΔ (v 0) (v 1) w)

/-- The transition map is affine with linear part the top-left block of the transition matrix. -/
theorem faceLift_transition_eq {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (σ : Equiv.Perm (Fin k ⊕ Fin 2)) (w : Fin k → ℝ) (v : Fin 2 → ℝ) :
    (fun i ↦ faceLift κ Q (v 0) (v 1) w (σ (Sum.inl i))) =
      (transitionMat κ Q σ).toBlocks₁₁ *ᵥ w + (transitionMat κ Q σ).toBlocks₁₂ *ᵥ v := by
  have h := transitionMat_mulVec hΔ σ w v
  rw [← Matrix.fromBlocks_toBlocks (transitionMat κ Q σ), Matrix.fromBlocks_mulVec] at h
  have h1 := congrArg (fun f ↦ f ∘ Sum.inl) h
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h1
  exact h1.symm

/-- The lower blocks of the transition matrix are `0` and `1`. -/
theorem transitionMat_eq_fromBlocks {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (σ : Equiv.Perm (Fin k ⊕ Fin 2)) :
    transitionMat κ Q σ = Matrix.fromBlocks (transitionMat κ Q σ).toBlocks₁₁
      (transitionMat κ Q σ).toBlocks₁₂ 0 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← Sum.elim_comp_inl_inr x, transitionMat_mulVec hΔ, Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, Matrix.one_mulVec, zero_add]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [faceLift_transition_eq hΔ σ]

theorem transitionMat_det_eq {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (σ : Equiv.Perm (Fin k ⊕ Fin 2)) :
    (transitionMat κ Q σ).det = (transitionMat κ Q σ).toBlocks₁₁.det := by
  conv_lhs => rw [transitionMat_eq_fromBlocks hΔ σ]
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem abs_det_transitionMat (κ Q : Fin k ⊕ Fin 2 → ℝ) (σ : Equiv.Perm (Fin k ⊕ Fin 2)) :
    |(transitionMat κ Q σ).det| = |(transMat (κ ∘ σ) (Q ∘ σ)).det| / |(transMat κ Q).det| := by
  unfold transitionMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    Matrix.det_permutation, abs_mul, abs_mul, abs_inv, augMat_det, augMat_det, abs_neg,
    abs_neg]
  have : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [this, mul_one, div_eq_mul_inv]

/-- The transition map sends the face polytope of `(κ, Q)` onto that of `(κ ∘ σ, Q ∘ σ)`. -/
theorem image_facePolytope_transition {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (σ : Equiv.Perm (Fin k ⊕ Fin 2)) (hΔσ : (transMat (κ ∘ σ) (Q ∘ σ)).det ≠ 0) (δ γ : ℝ) :
    (fun w ↦ fun i ↦ faceLift κ Q δ γ w (σ (Sum.inl i))) '' facePolytope κ Q δ γ =
      facePolytope (κ ∘ σ) (Q ∘ σ) δ γ := by
  ext w'
  constructor
  · rintro ⟨w, hw, rfl⟩
    beta_reduce
    rw [mem_facePolytope_iff_faceLift_nonneg hΔσ]
    have hlift : faceLift (κ ∘ σ) (Q ∘ σ) δ γ (fun i ↦ faceLift κ Q δ γ w (σ (Sum.inl i))) =
        faceLift κ Q δ γ w ∘ σ := by
      refine faceLift_eq_of hΔσ (fun i ↦ rfl) ?_ ?_
      · exact (Equiv.sum_comp σ (fun s ↦ κ s * faceLift κ Q δ γ w s)).trans
          (faceLift_sum_κ hΔ δ γ w)
      · exact (Equiv.sum_comp σ (fun s ↦ Q s * faceLift κ Q δ γ w s)).trans
          (faceLift_sum_Q hΔ δ γ w)
    rw [hlift]
    intro s
    exact (mem_facePolytope_iff_faceLift_nonneg hΔ δ γ w).mp hw (σ s)
  · intro hw'
    refine ⟨fun i ↦ faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' (σ.symm (Sum.inl i)), ?_, ?_⟩
    · rw [mem_facePolytope_iff_faceLift_nonneg hΔ]
      have hlift : faceLift κ Q δ γ (fun i ↦ faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' (σ.symm (Sum.inl i)))
          = faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' ∘ σ.symm := by
        refine faceLift_eq_of hΔ (fun i ↦ rfl) ?_ ?_
        · have := Equiv.sum_comp σ.symm
            (fun s ↦ (κ ∘ σ) s * faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' s)
          simp only [Function.comp, Equiv.apply_symm_apply] at this
          exact this.trans (faceLift_sum_κ hΔσ δ γ w')
        · have := Equiv.sum_comp σ.symm
            (fun s ↦ (Q ∘ σ) s * faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' s)
          simp only [Function.comp, Equiv.apply_symm_apply] at this
          exact this.trans (faceLift_sum_Q hΔσ δ γ w')
      rw [hlift]
      intro s
      exact (mem_facePolytope_iff_faceLift_nonneg hΔσ δ γ w').mp hw' (σ.symm s)
    · funext i
      beta_reduce
      have hlift : faceLift κ Q δ γ (fun i ↦ faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' (σ.symm (Sum.inl i)))
          = faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' ∘ σ.symm := by
        refine faceLift_eq_of hΔ (fun i ↦ rfl) ?_ ?_
        · have := Equiv.sum_comp σ.symm
            (fun s ↦ (κ ∘ σ) s * faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' s)
          simp only [Function.comp, Equiv.apply_symm_apply] at this
          exact this.trans (faceLift_sum_κ hΔσ δ γ w')
        · have := Equiv.sum_comp σ.symm
            (fun s ↦ (Q ∘ σ) s * faceLift (κ ∘ σ) (Q ∘ σ) δ γ w' s)
          simp only [Function.comp, Equiv.apply_symm_apply] at this
          exact this.trans (faceLift_sum_Q hΔσ δ γ w')
      rw [hlift]
      simp only [Function.comp, Equiv.symm_apply_apply]
      exact faceLift_inl hΔσ δ γ w' i

/-- **Solved-pair independence** (permutation form):
`vol(F'_σ)/|det M_σ| = vol(F')/|det M|`. -/
theorem volume_facePolytope_div_det_perm {κ Q : Fin k ⊕ Fin 2 → ℝ} (hκ : ∀ s, 0 < κ s)
    (hΔ : (transMat κ Q).det ≠ 0) (σ : Equiv.Perm (Fin k ⊕ Fin 2))
    (hΔσ : (transMat (κ ∘ σ) (Q ∘ σ)).det ≠ 0) (δ γ : ℝ) :
    (volume (facePolytope (κ ∘ σ) (Q ∘ σ) δ γ)).toReal / |(transMat (κ ∘ σ) (Q ∘ σ)).det| =
      (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| := by
  set L := (transitionMat κ Q σ).toBlocks₁₁ with hL
  set c := (transitionMat κ Q σ).toBlocks₁₂ *ᵥ ![δ, γ] with hc
  have himg : facePolytope (κ ∘ σ) (Q ∘ σ) δ γ =
      (fun w ↦ w + c) '' ((Matrix.toLin' L) '' facePolytope κ Q δ γ) := by
    rw [← image_facePolytope_transition hΔ σ hΔσ δ γ, Set.image_image]
    refine Set.image_congr fun w _ ↦ ?_
    have := faceLift_transition_eq hΔ σ w ![δ, γ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [this, Matrix.toLin'_apply]
  have hvol : volume (facePolytope (κ ∘ σ) (Q ∘ σ) δ γ) =
      ENNReal.ofReal |L.det| * volume (facePolytope κ Q δ γ) := by
    rw [himg, Set.image_add_right, measure_preimage_add_right,
      Measure.addHaar_image_linearMap, LinearMap.det_toLin']
  have hdet : |L.det| = |(transMat (κ ∘ σ) (Q ∘ σ)).det| / |(transMat κ Q).det| := by
    rw [hL, ← transitionMat_det_eq hΔ σ, abs_det_transitionMat κ Q σ]
  have hne : volume (facePolytope κ Q δ γ) ≠ ⊤ := volume_facePolytope_ne_top hΔ hκ δ γ
  rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), hdet]
  have h1 : |(transMat (κ ∘ σ) (Q ∘ σ)).det| ≠ 0 := abs_ne_zero.mpr hΔσ
  have h2 : |(transMat κ Q).det| ≠ 0 := abs_ne_zero.mpr hΔ
  field_simp

/-- **Solved-pair independence** for two splittings of a chart's active coordinates. -/
theorem volume_facePolytope_div_det_eq {ι : Type*} {κ Q : ι → ℝ} (hκ : ∀ s, 0 < κ s)
    (e₁ e₂ : Fin k ⊕ Fin 2 ≃ ι) (hΔ₁ : (transMat (κ ∘ e₁) (Q ∘ e₁)).det ≠ 0)
    (hΔ₂ : (transMat (κ ∘ e₂) (Q ∘ e₂)).det ≠ 0) (δ γ : ℝ) :
    (volume (facePolytope (κ ∘ e₂) (Q ∘ e₂) δ γ)).toReal / |(transMat (κ ∘ e₂) (Q ∘ e₂)).det| =
      (volume (facePolytope (κ ∘ e₁) (Q ∘ e₁) δ γ)).toReal /
        |(transMat (κ ∘ e₁) (Q ∘ e₁)).det| := by
  have hσ : κ ∘ e₂ = (κ ∘ e₁) ∘ ⇑(e₂.trans e₁.symm) ∧
      Q ∘ e₂ = (Q ∘ e₁) ∘ ⇑(e₂.trans e₁.symm) := by
    constructor <;> (funext s; simp [Function.comp])
  rw [hσ.1, hσ.2]
  rw [hσ.1, hσ.2] at hΔ₂
  exact volume_facePolytope_div_det_perm (fun s ↦ hκ _) hΔ₁ (e₂.trans e₁.symm) hΔ₂ δ γ

namespace WallChartsData.Phase

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)} {D : WallChartsData m ℓ L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {i : D.ι}

/-- **The face constant does not depend on the solved pair.** -/
theorem faceConst_eq (γ : ℝ) (hκ : ∀ j, 0 < P.kappa i j) (e₁ e₂ : Fin k ⊕ Fin 2 ≃ Fin m)
    (hΔ₁ : (transMat (P.kappa i ∘ e₁) (D.Qexp i ∘ e₁)).det ≠ 0)
    (hΔ₂ : (transMat (P.kappa i ∘ e₂) (D.Qexp i ∘ e₂)).det ≠ 0) :
    P.faceConst i γ e₂ = P.faceConst i γ e₁ :=
  volume_facePolytope_div_det_eq hκ e₁ e₂ hΔ₁ hΔ₂ (P.phaseExp i γ) γ

end WallChartsData.Phase

end Laplace.Multi
