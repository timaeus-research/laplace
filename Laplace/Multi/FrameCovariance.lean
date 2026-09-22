/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TwoLoopEnergy

/-!
# The Hessian route is frame-covariant

The note's formulas are tensor expressions in `H`, `T`, `Q₄` and `S = (tH)⁻¹`. Under an orthogonal
change of coordinates `w = Q u` the tensors transform as `H ↦ Q H Qᵀ`, `T ↦ rotateT Q T`
(`T'ᵢⱼₖ = ∑ Qᵢₐ Qⱼ_b Qₖ_c T_{abc}`), `Q₄ ↦ rotateQ Q Q₄`, and this file shows every formula
transforms accordingly, for *arbitrary* tensors (no symmetry is used):

* `contractT_rotate`, `contractQ_rotate`, `bubble_rotate`, `tadpoleLine_rotate`, `oneLoopPi_rotate`:
  the contractions are covariant (`Q *ᵥ ·` for the vector, `Q · Qᵀ` for the matrices);
* `smul_conj_inv`: `(t • (Q H Qᵀ))⁻¹ = Q (t • H)⁻¹ Qᵀ` for every `H`;
* `oneLoopCov_rotate`: `oneLoopCov t (QHQᵀ) T' Q₄' = Q (oneLoopCov t H T Q₄) Qᵀ` (eq:oneloop);
* `meanShift_rotate`: `meanShift t (QHQᵀ) T' = Q *ᵥ meanShift t H T` (eq:mean);
* `covKFormula_rotate`: `covKFormula t (QHQᵀ) T' (QBQᵀ) (Q *ᵥ b) = covKFormula t H T B b` (eq:covK);
* `twoLoopEnergy_rotate`: `twoLoopEnergy t (QHQᵀ) T' Q₄' = twoLoopEnergy t H T Q₄`;
* `rotT_eq_rotateT`, `rotQ_eq_rotateQ`: E2's `rotT`, `rotQ` are `rotateT`, `rotateQ` of the diagonal
  tensors, so `OneLoopRotated`'s closed forms are the separable instance.

The proofs work at the matrix level: the contractions are Frobenius pairings `frob X Y = tr(Xᵀ Y)`
of slices of the tensors, the slices of a rotated tensor are sums of conjugates
(`slice_rotateT`), and `frob (Q X Qᵀ) (Q Y Qᵀ) = frob X Y`.
-/

open Matrix

namespace Laplace.Multi

variable {d : ℕ}

/-! ### Rotated tensors -/

/-- The cubic tensor in the frame `w = Q u`: `T'ᵢⱼₖ = ∑ Qᵢₐ Qⱼ_b Qₖ_c T_{abc}`. -/
noncomputable def rotateT (Q : Matrix (Fin d) (Fin d) ℝ) (T : Fin d → Fin d → Fin d → ℝ) :
    Fin d → Fin d → Fin d → ℝ :=
  fun i j k => ∑ a, ∑ b, ∑ c, Q i a * Q j b * Q k c * T a b c

/-- The quartic tensor in the frame `w = Q u`. -/
noncomputable def rotateQ (Q : Matrix (Fin d) (Fin d) ℝ)
    (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ) : Fin d → Fin d → Fin d → Fin d → ℝ :=
  fun i j k l => ∑ a, ∑ b, ∑ c, ∑ e, Q i a * Q j b * Q k c * Q l e * Q4 a b c e

/-- The matrix slice `(slice T i) k l = T i k l`. -/
noncomputable def slice (T : Fin d → Fin d → Fin d → ℝ) (i : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun k l => T i k l

/-- The matrix slice `(slice2 Q4 i j) k l = Q4 i j k l`. -/
noncomputable def slice2 (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ) (i j : Fin d) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun k l => Q4 i j k l

/-- The Frobenius pairing `frob X Y = tr(Xᵀ Y) = ∑ᵢⱼ Xᵢⱼ Yᵢⱼ`. -/
noncomputable def frob (X Y : Matrix (Fin d) (Fin d) ℝ) : ℝ := (Xᵀ * Y).trace

theorem frob_apply (X Y : Matrix (Fin d) (Fin d) ℝ) : frob X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp only [frob, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem frob_sum_left {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin d) ℝ) : frob (∑ a ∈ s, X a) Y = ∑ a ∈ s, frob (X a) Y := by
  simp only [frob, Matrix.transpose_sum, Matrix.sum_mul, Matrix.trace_sum]

theorem frob_sum_right {ι : Type*} (s : Finset ι) (X : Matrix (Fin d) (Fin d) ℝ)
    (Y : ι → Matrix (Fin d) (Fin d) ℝ) : frob X (∑ a ∈ s, Y a) = ∑ a ∈ s, frob X (Y a) := by
  simp only [frob, Matrix.mul_sum, Matrix.trace_sum]

theorem frob_smul_left (c : ℝ) (X Y : Matrix (Fin d) (Fin d) ℝ) :
    frob (c • X) Y = c * frob X Y := by
  simp only [frob, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem frob_smul_right (c : ℝ) (X Y : Matrix (Fin d) (Fin d) ℝ) :
    frob X (c • Y) = c * frob X Y := by
  simp only [frob, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

section Conj

variable {Q : Matrix (Fin d) (Fin d) ℝ}

theorem conj_apply (Q : Matrix (Fin d) (Fin d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    (Q * M * Qᵀ) i j = ∑ a, ∑ b, Q i a * M a b * Q j b := by
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem transpose_conj (Q : Matrix (Fin d) (Fin d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (Q * M * Qᵀ)ᵀ = Q * Mᵀ * Qᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]

/-- **Frobenius invariance**: `frob (Q X Qᵀ) (Q Y Qᵀ) = frob X Y`. -/
theorem frob_conj (hQ : Qᵀ * Q = 1) (X Y : Matrix (Fin d) (Fin d) ℝ) :
    frob (Q * X * Qᵀ) (Q * Y * Qᵀ) = frob X Y := by
  rw [frob, transpose_conj, conj_mul_conj hQ, Matrix.trace_mul_cycle, hQ, Matrix.one_mul, frob]

/-- `(t • (Q H Qᵀ))⁻¹ = Q (t • H)⁻¹ Qᵀ`, for every `H` (both sides vanish when `H` is singular). -/
theorem smul_conj_inv (hQ : Qᵀ * Q = 1) (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) :
    (t • (Q * H * Qᵀ))⁻¹ = Q * (t • H)⁻¹ * Qᵀ := by
  have h1 : t • (Q * H * Qᵀ) = Q * (t • H) * Qᵀ := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  have hQinv : Q⁻¹ = Qᵀ := Matrix.inv_eq_left_inv hQ
  have hQTinv : (Qᵀ)⁻¹ = Q := Matrix.inv_eq_right_inv hQ
  rw [h1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hQinv, hQTinv, Matrix.mul_assoc]

end Conj

/-! ### Slices of rotated tensors -/

theorem slice_rotateT (Q : Matrix (Fin d) (Fin d) ℝ) (T : Fin d → Fin d → Fin d → ℝ) (i : Fin d) :
    slice (rotateT Q T) i = ∑ a, Q i a • (Q * slice T a * Qᵀ) := by
  ext k l
  simp only [slice, Matrix.of_apply, rotateT, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    conj_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem slice2_rotateQ (Q : Matrix (Fin d) (Fin d) ℝ) (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (i j : Fin d) :
    slice2 (rotateQ Q Q4) i j = ∑ a, ∑ b, (Q i a * Q j b) • (Q * slice2 Q4 a b * Qᵀ) := by
  ext k l
  simp only [slice2, Matrix.of_apply, rotateQ, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    conj_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-! ### The contractions as Frobenius pairings -/

theorem contractT_eq_frob (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (l : Fin d) : contractT T S l = frob (slice T l) S := by
  simp only [contractT, frob_apply, slice, Matrix.of_apply]

theorem contractQ_eq_frob (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) : contractQ Q4 S i j = frob (slice2 Q4 i j) S := by
  simp only [contractQ, frob_apply, slice2, Matrix.of_apply]

theorem bubble_eq_frob (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) : bubble T S i j = frob (slice T i) (S * slice T j * Sᵀ) := by
  simp only [bubble, frob_apply, slice, Matrix.of_apply, Matrix.mul_apply, transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  ring

theorem tadpoleLine_eq_mulVec (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) : tadpoleLine T S i j = (slice T i *ᵥ (S *ᵥ contractT T S)) j := by
  simp only [tadpoleLine, Matrix.of_apply, slice, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem thetaDiagram_eq_frob (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    thetaDiagram T S = frob S (bubble T S) := by
  simp only [thetaDiagram, frob_apply]

theorem figureEight_eq_frob (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) : figureEight Q4 S = frob (contractQ Q4 S) S := by
  simp only [figureEight, frob_apply]

/-! ### Covariance of the contractions -/

section Rotate

variable {Q : Matrix (Fin d) (Fin d) ℝ}

theorem contractT_rotate (hQ : Qᵀ * Q = 1) (T : Fin d → Fin d → Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) :
    contractT (rotateT Q T) (Q * S * Qᵀ) = Q *ᵥ contractT T S := by
  funext l
  rw [contractT_eq_frob, slice_rotateT, frob_sum_left]
  simp only [frob_smul_left, frob_conj hQ, Matrix.mulVec, dotProduct, contractT_eq_frob]

theorem contractQ_rotate (hQ : Qᵀ * Q = 1) (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) :
    contractQ (rotateQ Q Q4) (Q * S * Qᵀ) = Q * contractQ Q4 S * Qᵀ := by
  ext i j
  rw [contractQ_eq_frob, slice2_rotateQ, frob_sum_left, conj_apply]
  simp only [frob_sum_left, frob_smul_left, frob_conj hQ, contractQ_eq_frob]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem bubble_rotate (hQ : Qᵀ * Q = 1) (T : Fin d → Fin d → Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) :
    bubble (rotateT Q T) (Q * S * Qᵀ) = Q * bubble T S * Qᵀ := by
  ext i j
  rw [bubble_eq_frob, slice_rotateT, slice_rotateT, conj_apply]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, frob_sum_left,
    frob_sum_right, frob_smul_left, frob_smul_right]
  have hconj : ∀ a, Q * S * Qᵀ * (Q * slice T a * Qᵀ) * (Q * S * Qᵀ)ᵀ =
      Q * (S * slice T a * Sᵀ) * Qᵀ := fun a => by
    rw [transpose_conj, conj_mul_conj hQ, conj_mul_conj hQ]
  simp only [hconj, frob_conj hQ, bubble_eq_frob, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem tadpoleLine_rotate (hQ : Qᵀ * Q = 1) (T : Fin d → Fin d → Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) :
    tadpoleLine (rotateT Q T) (Q * S * Qᵀ) = Q * tadpoleLine T S * Qᵀ := by
  ext i j
  rw [tadpoleLine_eq_mulVec, contractT_rotate hQ, slice_rotateT, conj_apply]
  have hv : (Q * S * Qᵀ) *ᵥ (Q *ᵥ contractT T S) = Q *ᵥ (S *ᵥ contractT T S) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Q * S), hQ, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hQv : ∀ a, (Q * slice T a * Qᵀ) *ᵥ (Q *ᵥ (S *ᵥ contractT T S)) =
      Q *ᵥ (slice T a *ᵥ (S *ᵥ contractT T S)) := fun a => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Q * slice T a), hQ, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
  have e : ∀ w : Fin d → ℝ, (Q *ᵥ w) j = ∑ b, Q j b * w b := fun w => rfl
  rw [hv, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, hQv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e,
    tadpoleLine_eq_mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem oneLoopPi_rotate (hQ : Qᵀ * Q = 1) (t : ℝ) (T : Fin d → Fin d → Fin d → ℝ)
    (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    oneLoopPi t (rotateT Q T) (rotateQ Q Q4) (Q * S * Qᵀ) = Q * oneLoopPi t T Q4 S * Qᵀ := by
  rw [oneLoopPi, oneLoopPi, contractQ_rotate hQ, bubble_rotate hQ, tadpoleLine_rotate hQ,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]

/-- **eq:oneloop is frame-covariant.** -/
theorem oneLoopCov_rotate (hQ : Qᵀ * Q = 1) (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ) :
    oneLoopCov t (Q * H * Qᵀ) (rotateT Q T) (rotateQ Q Q4) = Q * oneLoopCov t H T Q4 * Qᵀ := by
  rw [oneLoopCov, oneLoopCov, smul_conj_inv hQ, oneLoopPi_rotate hQ, conj_mul_conj hQ,
    conj_mul_conj hQ, Matrix.mul_add, Matrix.add_mul]

/-- **eq:mean is frame-covariant.** -/
theorem meanShift_rotate (hQ : Qᵀ * Q = 1) (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) :
    meanShift t (Q * H * Qᵀ) (rotateT Q T) = Q *ᵥ meanShift t H T := by
  rw [meanShift, meanShift, smul_conj_inv hQ, contractT_rotate hQ]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one]

/-- `Q *ᵥ v ⬝ᵥ Q *ᵥ w = v ⬝ᵥ w`. -/
theorem conj_SHS (hQ : Qᵀ * Q = 1) (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) :
    (t • (Q * H * Qᵀ))⁻¹ * (Q * H * Qᵀ) * (t • (Q * H * Qᵀ))⁻¹ =
      Q * ((t • H)⁻¹ * H * (t • H)⁻¹) * Qᵀ := by
  rw [smul_conj_inv hQ, conj_mul_conj hQ, conj_mul_conj hQ]

/-- **eq:covK is frame-invariant.** -/
theorem covKFormula_rotate (hQ : Qᵀ * Q = 1) (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) :
    covKFormula t (Q * H * Qᵀ) (rotateT Q T) (Q * B * Qᵀ) (Q *ᵥ b) = covKFormula t H T B b := by
  have hS := smul_conj_inv hQ t H
  have hSb : (t • (Q * H * Qᵀ))⁻¹ *ᵥ (Q *ᵥ b) = Q *ᵥ ((t • H)⁻¹ *ᵥ b) := by
    rw [hS, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have htr : (Q * H * Qᵀ * (t • (Q * H * Qᵀ))⁻¹ * (Q * B * Qᵀ) * (t • (Q * H * Qᵀ))⁻¹).trace =
      (H * (t • H)⁻¹ * B * (t • H)⁻¹).trace := by
    rw [hS, conj_mul_conj hQ, conj_mul_conj hQ, conj_mul_conj hQ, Matrix.trace_mul_cycle, hQ,
      Matrix.one_mul]
  have hSHS : Q * (t • H)⁻¹ * Qᵀ * (Q * H * Qᵀ) * (Q * (t • H)⁻¹ * Qᵀ) =
      Q * ((t • H)⁻¹ * H * (t • H)⁻¹) * Qᵀ := by
    rw [conj_mul_conj hQ, conj_mul_conj hQ]
  have e2 : (Q *ᵥ b) ⬝ᵥ ((Q * ((t • H)⁻¹ * H * (t • H)⁻¹) * Qᵀ) *ᵥ (Q *ᵥ contractT T (t • H)⁻¹)) =
      b ⬝ᵥ (((t • H)⁻¹ * H * (t • H)⁻¹) *ᵥ contractT T (t • H)⁻¹) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Q * ((t • H)⁻¹ * H * (t • H)⁻¹)), hQ,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, mulVec_dotProduct_mulVec hQ]
  rw [covKFormula, covKFormula, htr, hSb, hS, contractT_rotate hQ, hSHS, contractT_rotate hQ, e2,
    mulVec_dotProduct_mulVec hQ, mulVec_dotProduct_mulVec hQ]

/-- **The two-loop energy is frame-invariant.** -/
theorem twoLoopEnergy_rotate (hQ : Qᵀ * Q = 1) (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ) :
    twoLoopEnergy t (Q * H * Qᵀ) (rotateT Q T) (rotateQ Q Q4) = twoLoopEnergy t H T Q4 := by
  have hS := smul_conj_inv hQ t H
  have htr : (Q * H * Qᵀ * (Q * (t • H)⁻¹ * Qᵀ)).trace = (H * (t • H)⁻¹).trace := by
    rw [conj_mul_conj hQ, Matrix.trace_mul_cycle, hQ, Matrix.one_mul]
  have hdumb : dumbbell (rotateT Q T) (Q * (t • H)⁻¹ * Qᵀ) = dumbbell T (t • H)⁻¹ := by
    rw [dumbbell, dumbbell, contractT_rotate hQ, Matrix.mulVec_mulVec,
      Matrix.mul_assoc (Q * (t • H)⁻¹), hQ, Matrix.mul_one, ← Matrix.mulVec_mulVec,
      mulVec_dotProduct_mulVec hQ]
  have htheta : thetaDiagram (rotateT Q T) (Q * (t • H)⁻¹ * Qᵀ) = thetaDiagram T (t • H)⁻¹ := by
    rw [thetaDiagram_eq_frob, thetaDiagram_eq_frob, bubble_rotate hQ, frob_conj hQ]
  have hq : figureEight (rotateQ Q Q4) (Q * (t • H)⁻¹ * Qᵀ) = figureEight Q4 (t • H)⁻¹ := by
    rw [figureEight_eq_frob, figureEight_eq_frob, contractQ_rotate hQ, frob_conj hQ]
  rw [twoLoopEnergy, twoLoopEnergy, hS, htr, hdumb, htheta, hq]

end Rotate

/-! ### The identity acts trivially -/

theorem rotateT_one (T : Fin d → Fin d → Fin d → ℝ) :
    rotateT (1 : Matrix (Fin d) (Fin d) ℝ) T = T := by
  funext i j k
  simp [rotateT, Matrix.one_apply]

theorem rotateQ_one (Q4 : Fin d → Fin d → Fin d → Fin d → ℝ) :
    rotateQ (1 : Matrix (Fin d) (Fin d) ℝ) Q4 = Q4 := by
  funext i j k l
  simp [rotateQ, Matrix.one_apply]

theorem slice_ext {T T' : Fin d → Fin d → Fin d → ℝ} (h : ∀ i, slice T i = slice T' i) :
    T = T' := by
  funext i k l
  have := congrFun (congrFun (h i) k) l
  simpa [slice] using this

/-- **Composition**: `rotateT Q₁ (rotateT Q₂ T) = rotateT (Q₁ Q₂) T` (no orthogonality needed). -/
theorem rotateT_rotateT (Q₁ Q₂ : Matrix (Fin d) (Fin d) ℝ) (T : Fin d → Fin d → Fin d → ℝ) :
    rotateT Q₁ (rotateT Q₂ T) = rotateT (Q₁ * Q₂) T := by
  refine slice_ext fun i => ?_
  rw [slice_rotateT, slice_rotateT]
  simp only [slice_rotateT, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    transpose_mul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul]
  simp only [Matrix.mul_assoc]

/-! ### The separable tensors are the diagonal instance -/

/-- The diagonal cubic tensor `diagT α a b c = α a` when `a = b = c`, else `0`. -/
noncomputable def diagT (alpha : Fin d → ℝ) : Fin d → Fin d → Fin d → ℝ :=
  fun a b c => if c = a then (if b = a then alpha a else 0) else 0

/-- The diagonal quartic tensor. -/
noncomputable def diagQ (gamma : Fin d → ℝ) : Fin d → Fin d → Fin d → Fin d → ℝ :=
  fun a b c e => if e = a then (if c = a then (if b = a then gamma a else 0) else 0) else 0

theorem rotT_eq_rotateT (Q : Matrix (Fin d) (Fin d) ℝ) (alpha : Fin d → ℝ) :
    rotT Q alpha = rotateT Q (diagT alpha) := by
  funext i j k
  simp only [rotT, rotateT, diagT, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem rotQ_eq_rotateQ (Q : Matrix (Fin d) (Fin d) ℝ) (gamma : Fin d → ℝ) :
    rotQ Q gamma = rotateQ Q (diagQ gamma) := by
  funext i j k l
  simp only [rotQ, rotateQ, diagQ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end Laplace.Multi
