/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthTheorem

/-!
# The degenerate three-coordinate face as an instance of the face theorem

`DegenerateFace.lean` proved `t⁴ I(t)/log t → 1` for
`I(t) = ∫_{(0,1)³, xyz > t^{-2}} z² e^{-t³ x y z²}` by hand. Here the same rate and constant are
read off the transverse active-truth face theorem: on `Fin 1 ⊕ Fin 2` (free coordinate `x`, solved
pair `(y, z)`) with `κ = (1, 1, 2)`, `Q = (1, 1, 1)`, `r = (0, 0, 2)`, `ρ = A = B = D = q = w₀ =
a₀ = 1`, `γ = 2`, `p = 0`, `δ = 3`, the dual certificate is `(β, η) = (2, 1)` (`r + 1 = 2κ − Q`),
the transverse matrix is `[[1, 2], [−1, −1]]` with determinant `1`, the fibre constraints are
`x ≤ 1` and the vacuous `0 ≤ 1` (this is why the theorem's nondegeneracy is `(c_j, a_j) ≠ (0, 0)`
rather than `c_j ≠ 0`), the face polytope is `[0, 1]` of volume `1`, and the constant is
`Γ(2) = 1` (`tendsto_modelKernel_degExample`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

/-- The loss exponents `(1, 1, 2)` of the degenerate example. -/
def degκ : Fin 1 ⊕ Fin 2 → ℝ := Sum.elim ![1] ![1, 2]

/-- The truth exponents `(1, 1, 1)`. -/
def degQ : Fin 1 ⊕ Fin 2 → ℝ := Sum.elim ![1] ![1, 1]

/-- The density exponents `(0, 0, 2)`. -/
def degr : Fin 1 ⊕ Fin 2 → ℝ := Sum.elim ![0] ![0, 2]

theorem degκ_pos : ∀ i, 0 < degκ i := by
  rw [Sum.forall]
  constructor <;> intro i <;> fin_cases i <;> simp [degκ]

theorem deg_certificate : ∀ i, degr i + 1 = 2 * degκ i - 1 * degQ i := by
  rw [Sum.forall]
  constructor <;> intro i <;> fin_cases i <;> simp [degr, degκ, degQ] <;> norm_num

theorem degTransMat : transMat degκ degQ = !![1, 2; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transMat, degκ, degQ]

theorem degTransMat_det : (transMat degκ degQ).det = 1 := by
  rw [degTransMat, Matrix.det_fin_two_of]
  norm_num

theorem degTransMat_inv : (transMat degκ degQ)⁻¹ = !![-1, -2; 1, 1] := by
  rw [Matrix.inv_def, degTransMat_det, degTransMat, Matrix.adjugate_fin_two_of]
  simp

theorem degFibreCoef_zero : fibreCoef degκ degQ 0 = fun _ ↦ 1 := by
  funext i
  fin_cases i
  simp only [fibreCoef, degTransMat_inv]
  simp [degκ, degQ]
  norm_num

theorem degFibreCoef_one : fibreCoef degκ degQ 1 = fun _ ↦ 0 := by
  funext i
  fin_cases i
  simp only [fibreCoef, degTransMat_inv]
  simp [degκ, degQ]

theorem degFibreA_zero : fibreA degκ degQ 3 2 0 = 1 := by
  simp [fibreA, degTransMat_inv]
  norm_num

theorem degFibreA_one : fibreA degκ degQ 3 2 1 = 1 := by
  simp [fibreA, degTransMat_inv]
  norm_num

/-- The face polytope of the example is the unit interval in the free coordinate. -/
theorem degFacePolytope : facePolytope degκ degQ 3 2 = Icc (0 : Fin 1 → ℝ) 1 := by
  ext w
  simp only [facePolytope, poly2, degFibreCoef_zero, degFibreCoef_one, degFibreA_zero,
    degFibreA_one, Set.mem_ofPred_eq, dotProduct, Fin.sum_univ_one, one_mul, zero_mul,
    zero_le_one, and_true, Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply,
    Fin.forall_fin_one]

theorem volume_degFacePolytope : volume (facePolytope degκ degQ 3 2) = 1 := by
  rw [degFacePolytope, Real.volume_Icc_pi]
  simp

/-- **The degenerate example as an instance**: the face theorem gives `t⁴/log t · K(t) → 1`. -/
theorem tendsto_modelKernel_degExample :
    Tendsto (fun t ↦ t ^ 4 / log t *
      modelKernel 1 1 1 1 2 0 1 3 degQ degκ degr (fun _ _ ↦ 1) (fun _ _ ↦ 1) t) atTop (𝓝 1) := by
  have h := tendsto_modelKernel_activeTruth' (k := 1) (ρ := 1) (A := 1) (B := 1) (D := 1)
    (γ := 2) (p := 0) (q := 1) (δ := 3) (β := 2) (η := 1) (w₀ := 1) (a₀ := 1) (Q := degQ)
    (κ := degκ) (r := degr) one_pos one_pos one_pos one_pos one_pos two_pos one_pos
    (by norm_num) degκ_pos (by rw [degTransMat_det]; exact one_ne_zero)
    (Or.inl (by rw [degFibreCoef_zero]; exact fun h ↦ one_ne_zero (congrFun h 0)))
    (Or.inr (by rw [degFibreA_one]; exact one_ne_zero)) deg_certificate
  rw [volume_degFacePolytope, degTransMat_det] at h
  norm_num [Real.Gamma_two] at h
  exact h

end Laplace.Multi
