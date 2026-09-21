/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Laplace.Multi.GaussianIBP
import Laplace.Multi.GaussianLLC
import Laplace.Multi.RescaledIntegrals
import Laplace.OneD.GaussianMoments
import Laplace.OneD.IntegralRemainder
import Laplace.Sampler.GaussianInvariance

/-!
# Gaussian moments on `ℝ^d` for a positive definite precision matrix

The multivariate track of this seabed states its Gaussian identities relative to a hypothesis
package (integrability of the Gaussian weight and its polynomial moments, and the Fubini-IBP
identity `FubiniIBPHypothesis`). Here the package is discharged for the weight
`exp(-½ uᵀ P u)` of a positive definite matrix `P`, by the linear change of variables
`u = M v`, `M = U diag(p^{-1/2})`, under which the weight becomes the standard Gaussian
`exp(-|v|²/2)` and Lebesgue measure scales by `|det M| = (det P)^{-1/2}`:
`Z = (2π)^{d/2} (det P)^{-1/2}` and `∫ uᵢ uⱼ e^{-½uᵀPu} = Z (P⁻¹)ᵢⱼ`; the IBP identity follows
because it is equivalent to `P · (second moments) = Z · I`.
-/

open MeasureTheory Matrix Laplace.Multi Laplace.Sampler

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuous linear map of a matrix on `ι → ℝ`. -/
noncomputable def matCLM (P : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' P)

@[simp] theorem matCLM_apply (P : Matrix ι ι ℝ) (u : ι → ℝ) : matCLM P u = P *ᵥ u := by
  simp [matCLM]

theorem quadForm_matCLM (P : Matrix ι ι ℝ) (u : ι → ℝ) : quadForm (matCLM P) u = u ⬝ᵥ P *ᵥ u := by
  simp [quadForm, dotProduct]

/-! ### The whitening change of variables -/

/-- The whitening matrix `M = U diag(p^{-1/2})` with `P = U diag(p) Uᵀ`. -/
noncomputable def whitening {P : Matrix ι ι ℝ} (hP : P.PosDef) : Matrix ι ι ℝ :=
  orthoOf hP.1 * diagonal fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹

theorem mul_orthoOf_eq_diagonal {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    P * orthoOf hP.1 = orthoOf hP.1 * diagonal hP.1.eigenvalues := by
  have h : P * orthoOf hP.1 =
      (orthoOf hP.1 * diagonal hP.1.eigenvalues * (orthoOf hP.1)ᵀ) * orthoOf hP.1 := by
    rw [← spectral_real hP.1]
  rw [h, Matrix.mul_assoc, orthoOf_transpose_mul hP.1, Matrix.mul_one]

theorem sqrt_eigenvalue_pos {P : Matrix ι ι ℝ} (hP : P.PosDef) (i : ι) :
    0 < Real.sqrt (hP.1.eigenvalues i) := Real.sqrt_pos.mpr (hP.eigenvalues_pos i)

theorem whitening_transpose_mul_mul {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    (whitening hP)ᵀ * P * whitening hP = 1 := by
  have hUPU := orthoOf_transpose_mul_mul hP.1
  unfold whitening
  rw [transpose_mul, diagonal_transpose]
  calc (diagonal (fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹) * (orthoOf hP.1)ᵀ) * P *
        (orthoOf hP.1 * diagonal (fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹))
      = diagonal (fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹) *
          ((orthoOf hP.1)ᵀ * P * orthoOf hP.1) *
          diagonal (fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hUPU, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        have hs := sqrt_eigenvalue_pos hP i
        have hsq := Real.mul_self_sqrt (hP.eigenvalues_pos i).le
        field_simp
        linarith


theorem whitening_mul_transpose {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    whitening hP * (whitening hP)ᵀ = P⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  unfold whitening
  rw [transpose_mul, diagonal_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P (orthoOf hP.1), mul_orthoOf_eq_diagonal hP]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal hP.1.eigenvalues) (diagonal _), diagonal_mul_diagonal,
    ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
  have h : (fun i => hP.1.eigenvalues i * (Real.sqrt (hP.1.eigenvalues i))⁻¹ *
      (Real.sqrt (hP.1.eigenvalues i))⁻¹) = fun _ => (1 : ℝ) := by
    funext i
    have hs := sqrt_eigenvalue_pos hP i
    have hsq := Real.mul_self_sqrt (hP.eigenvalues_pos i).le
    field_simp
    linarith
  rw [h, diagonal_one, Matrix.one_mul, orthoOf_mul_transpose hP.1]


theorem abs_det_whitening {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    |(whitening hP).det| = (Real.sqrt P.det)⁻¹ := by
  have h := congrArg Matrix.det (whitening_transpose_mul_mul hP)
  rw [det_mul, det_mul, det_transpose, det_one] at h
  have hdet := hP.det_pos
  have hsq : (whitening hP).det ^ 2 = (P.det)⁻¹ := by
    field_simp
    linarith [h]
  rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_inv]



theorem det_whitening_ne_zero {P : Matrix ι ι ℝ} (hP : P.PosDef) : (whitening hP).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (whitening_transpose_mul_mul hP)
  rw [det_mul, det_mul, det_transpose, h, mul_zero, det_one] at this
  exact zero_ne_one this


/-- **Linear change of variables** for Lebesgue measure on `ι → ℝ`:
`∫ g u du = |det M| ∫ g (M v) dv` for invertible `M`. -/
theorem map_mulVec_volume (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    Measure.map (fun v : ι → ℝ => M *ᵥ v) volume = ENNReal.ofReal |M.det|⁻¹ • volume := by
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := Matrix.toLin' M)
    (by rw [LinearMap.det_toLin']; exact hM)
  rw [LinearMap.det_toLin', abs_inv] at h
  convert h using 2
  funext v
  simp [Matrix.toLin'_apply]

theorem integral_comp_mulVec (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) (g : (ι → ℝ) → ℝ)
    (hg : AEStronglyMeasurable g volume) :
    ∫ u, g u = |M.det| * ∫ v, g (M *ᵥ v) := by
  have hmeas : Measurable (fun v : ι → ℝ => M *ᵥ v) :=
    (Matrix.toLin' M).toContinuousLinearMap.continuous.measurable
  have hmap := map_mulVec_volume M hM
  have h1 : ∫ v, g (M *ᵥ v) = ∫ u, g u ∂(Measure.map (fun v : ι → ℝ => M *ᵥ v) volume) := by
    rw [integral_map hmeas.aemeasurable]
    rw [hmap]
    exact hg.smul_measure _
  have hpos : 0 < |M.det| := abs_pos.mpr hM
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hpos.le), smul_eq_mul]
  field_simp

theorem integrable_comp_mulVec_iff (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) (g : (ι → ℝ) → ℝ)
    (hg : AEStronglyMeasurable g volume) :
    Integrable (fun v => g (M *ᵥ v)) ↔ Integrable g := by
  have hmeas : Measurable (fun v : ι → ℝ => M *ᵥ v) :=
    (Matrix.toLin' M).toContinuousLinearMap.continuous.measurable
  have hmap := map_mulVec_volume M hM
  have hpos : 0 < |M.det| := abs_pos.mpr hM
  have hc0 : ENNReal.ofReal |M.det|⁻¹ ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact inv_pos.mpr hpos
  have hcT : ENNReal.ofReal |M.det|⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hg' : AEStronglyMeasurable g (Measure.map (fun v : ι → ℝ => M *ᵥ v) volume) := by
    rw [hmap]; exact hg.smul_measure _
  have h1 := integrable_map_measure hg' hmeas.aemeasurable
  have h2 : Integrable g (Measure.map (fun v : ι → ℝ => M *ᵥ v) volume) ↔ Integrable g volume := by
    rw [hmap]; exact integrable_smul_measure hc0 hcT
  exact h1.symm.trans h2

/-! ### Standard Gaussian moments on `ι → ℝ` -/

omit [DecidableEq ι] in
/-- The standard Gaussian weight on `ι → ℝ` is a product. -/
theorem exp_neg_half_sum_sq (v : ι → ℝ) :
    Real.exp (-(1 / 2) * ∑ i, v i * v i) = ∏ i, Real.exp (-(v i) ^ 2 / 2) := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1; ring


/-! One-dimensional standard Gaussian factors. -/

theorem integral_exp_neg_sq_div_two : ∫ x : ℝ, Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1 / 2)
  have hfun : (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) = fun x => Real.exp (-x ^ 2 / 2) := by
    funext x; congr 1; ring
  rw [hfun] at h
  rw [h]
  congr 1
  field_simp

theorem integral_sq_mul_exp_neg_sq_div_two :
    ∫ x : ℝ, x * x * Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
  have h := Laplace.OneD.integral_pow_mul_exp_neg_sq_half 1
  norm_num [Nat.doubleFactorial] at h
  simpa [sq] using h

theorem integral_id_mul_exp_neg_sq_div_two : ∫ x : ℝ, x * Real.exp (-x ^ 2 / 2) = 0 := by
  have h := Laplace.OneD.integral_pow_mul_exp_neg_sq_odd 0
  simpa using h

theorem integrable_pow_mul_exp_neg_sq_div_two (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-x ^ 2 / 2)) := by
  have h := Laplace.OneD.integrable_pow_mul_exp_neg_half_sq n
  simpa using h

omit [DecidableEq ι] in
theorem integral_std_gaussian_pi :
    ∫ v : ι → ℝ, Real.exp (-(1 / 2) * ∑ i, v i * v i) =
      Real.sqrt (2 * Real.pi) ^ Fintype.card ι := by
  simp_rw [exp_neg_half_sum_sq]
  rw [integral_fintype_prod_volume_eq_prod (fun (_ : ι) (x : ℝ) => Real.exp (-x ^ 2 / 2))]
  simp [integral_exp_neg_sq_div_two, Finset.prod_const, Finset.card_univ]


theorem integral_coord_mul_std_gaussian_pi (k l : ι) :
    ∫ v : ι → ℝ, v k * v l * Real.exp (-(1 / 2) * ∑ i, v i * v i) =
      if k = l then Real.sqrt (2 * Real.pi) ^ Fintype.card ι else 0 := by
  have hprod : ∀ v : ι → ℝ, v k * v l * Real.exp (-(1 / 2) * ∑ i, v i * v i) =
      ∏ i, ((if i = k then v i else 1) * (if i = l then v i else 1) *
        Real.exp (-(v i) ^ 2 / 2)) := by
    intro v
    rw [exp_neg_half_sum_sq, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.prod_ite_eq']
    simp
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (x : ℝ) =>
    (if i = k then x else 1) * (if i = l then x else 1) * Real.exp (-x ^ 2 / 2))]
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl]
    have hfac : ∀ i ∈ Finset.univ, (∫ x : ℝ, (if i = k then x else 1) * (if i = k then x else 1) *
        Real.exp (-x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
      intro i _
      split_ifs with h
      · exact integral_sq_mul_exp_neg_sq_div_two
      · simpa using integral_exp_neg_sq_div_two
    rw [Finset.prod_congr rfl hfac, Finset.prod_const, Finset.card_univ]
  · rw [if_neg hkl]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    have := integral_id_mul_exp_neg_sq_div_two
    simpa [hkl] using this


omit [DecidableEq ι] in
theorem integrable_std_gaussian_pi :
    Integrable (fun v : ι → ℝ => Real.exp (-(1 / 2) * ∑ i, v i * v i)) := by
  simp_rw [exp_neg_half_sum_sq]
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun (_ : ι) (x : ℝ) => Real.exp (-x ^ 2 / 2))
    fun _ => by simpa using integrable_pow_mul_exp_neg_sq_div_two 0


omit [DecidableEq ι] in
theorem integrable_coord_mul_std_gaussian_pi (k l : ι) :
    Integrable (fun v : ι → ℝ => v k * v l * Real.exp (-(1 / 2) * ∑ i, v i * v i)) := by
  classical
  have hprod : ∀ v : ι → ℝ, v k * v l * Real.exp (-(1 / 2) * ∑ i, v i * v i) =
      ∏ i, ((if i = k then v i else 1) * (if i = l then v i else 1) *
        Real.exp (-(v i) ^ 2 / 2)) := by
    intro v
    rw [exp_neg_half_sum_sq, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.prod_ite_eq']
    simp
  simp_rw [hprod]
  rw [volume_pi]
  refine Integrable.fintype_prod (f := fun (i : ι) (x : ℝ) =>
    (if i = k then x else 1) * (if i = l then x else 1) * Real.exp (-x ^ 2 / 2)) fun i => ?_
  split_ifs
  · simpa [sq] using integrable_pow_mul_exp_neg_sq_div_two 2
  · simpa using integrable_pow_mul_exp_neg_sq_div_two 1
  · simpa using integrable_pow_mul_exp_neg_sq_div_two 1
  · simpa using integrable_pow_mul_exp_neg_sq_div_two 0


/-! ### The Gaussian weight of a positive definite matrix -/

omit [DecidableEq ι] in
/-- Expansion of a product of two coordinates of `M v` against a weight. -/
theorem mulVec_apply_mul_mulVec_apply_mul (M : Matrix ι ι ℝ) (i j : ι) (v : ι → ℝ) (w : ℝ) :
    (M *ᵥ v) i * (M *ᵥ v) j * w = ∑ a, ∑ b, M i a * M j b * (v a * v b * w) := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Expansion of `u j (P u) i` against a weight. -/
theorem coord_mul_matCLM_apply_mul (P : Matrix ι ι ℝ) (i j : ι) (u : ι → ℝ) (w : ℝ) :
    u j * (matCLM P u) i * w = ∑ k, P i k * (u k * u j * w) := by
  simp only [matCLM_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem continuous_coord_mul_gaussianWeight (P : Matrix ι ι ℝ) (i j : ι) :
    Continuous (fun u : ι → ℝ => u i * u j * gaussianWeight (matCLM P) u) :=
  ((continuous_apply i).mul (continuous_apply j)).mul (continuous_gaussianWeight _)

theorem gaussianWeight_matCLM_whitening {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) :
    gaussianWeight (matCLM P) (whitening hP *ᵥ v) = Real.exp (-(1 / 2) * ∑ i, v i * v i) := by
  unfold gaussianWeight
  rw [quadForm_matCLM]
  congr 2
  have h := dotProduct_conj_mulVec (whitening hP)ᵀ P v v
  rw [transpose_transpose, whitening_transpose_mul_mul hP, one_mulVec] at h
  exact h


/-- **The partition function**: `Z = (2π)^{d/2} / √(det P)`. -/
theorem gaussianZ_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    gaussianZ (matCLM P) = Real.sqrt (2 * Real.pi) ^ Fintype.card ι * (Real.sqrt P.det)⁻¹ := by
  unfold gaussianZ
  rw [integral_comp_mulVec (whitening hP) (det_whitening_ne_zero hP) _
    (continuous_gaussianWeight _).aestronglyMeasurable]
  simp_rw [gaussianWeight_matCLM_whitening hP]
  rw [integral_std_gaussian_pi, abs_det_whitening hP]
  ring

theorem gaussianZ_matCLM_pos {P : Matrix ι ι ℝ} (hP : P.PosDef) : 0 < gaussianZ (matCLM P) := by
  rw [gaussianZ_matCLM hP]
  have := hP.det_pos
  positivity


theorem integrable_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    Integrable (gaussianWeight (matCLM P)) := by
  rw [← integrable_comp_mulVec_iff (whitening hP) (det_whitening_ne_zero hP) _
    (continuous_gaussianWeight _).aestronglyMeasurable]
  simp_rw [gaussianWeight_matCLM_whitening hP]
  exact integrable_std_gaussian_pi


theorem integrable_coord_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) (i j : ι) :
    Integrable (fun u : ι → ℝ => u i * u j * gaussianWeight (matCLM P) u) := by
  rw [← integrable_comp_mulVec_iff (whitening hP) (det_whitening_ne_zero hP) _
    (continuous_coord_mul_gaussianWeight P i j).aestronglyMeasurable]
  simp_rw [gaussianWeight_matCLM_whitening hP, mulVec_apply_mul_mulVec_apply_mul]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_coord_mul_std_gaussian_pi a b).const_mul _


/-- **Second moments**: `∫ uᵢ uⱼ e^{-½uᵀPu} = Z (P⁻¹)ᵢⱼ`. -/
theorem integral_coord_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) (i j : ι) :
    ∫ u : ι → ℝ, u i * u j * gaussianWeight (matCLM P) u = gaussianZ (matCLM P) * P⁻¹ i j := by
  rw [integral_comp_mulVec (whitening hP) (det_whitening_ne_zero hP) _
    (continuous_coord_mul_gaussianWeight P i j).aestronglyMeasurable]
  simp_rw [gaussianWeight_matCLM_whitening hP, mulVec_apply_mul_mulVec_apply_mul]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_coord_mul_std_gaussian_pi a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ => (integrable_coord_mul_std_gaussian_pi _ b).const_mul _,
    integral_const_mul, integral_coord_mul_std_gaussian_pi, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hMM : P⁻¹ i j = ∑ a, whitening hP i a * whitening hP j a := by
    rw [← whitening_mul_transpose hP, mul_apply]
    simp only [transpose_apply]
  rw [gaussianZ_matCLM hP, ← abs_det_whitening hP, hMM, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring


theorem integrable_coord_mul_apply_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (i j : ι) :
    Integrable (fun u : ι → ℝ => u j * (matCLM P u) i * gaussianWeight (matCLM P) u) := by
  simp_rw [coord_mul_matCLM_apply_mul]
  exact integrable_finsetSum _ fun k _ =>
    (integrable_coord_mul_gaussianWeight_matCLM hP k j).const_mul _


/-- **The Fubini-IBP hypothesis holds** for a positive definite precision. -/
theorem fubiniIBPHypothesis_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) (i j : ι) :
    FubiniIBPHypothesis (matCLM P) i j := by
  unfold FubiniIBPHypothesis
  have hI1 : Integrable
      (fun u : ι → ℝ => (if i = j then (1 : ℝ) else 0) * gaussianWeight (matCLM P) u) :=
    (integrable_gaussianWeight_matCLM hP).const_mul _
  have hI2 := integrable_coord_mul_apply_gaussianWeight_matCLM hP i j
  rw [integral_sub hI1 hI2, integral_const_mul]
  have h2 : ∫ u : ι → ℝ, u j * (matCLM P u) i * gaussianWeight (matCLM P) u =
      ∑ k, P i k * ∫ u : ι → ℝ, u k * u j * gaussianWeight (matCLM P) u := by
    simp_rw [coord_mul_matCLM_apply_mul]
    rw [integral_finsetSum _ fun k _ =>
      (integrable_coord_mul_gaussianWeight_matCLM hP k j).const_mul _]
    simp_rw [integral_const_mul]
  rw [h2]
  simp_rw [integral_coord_mul_gaussianWeight_matCLM hP]
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP.det_pos.ne')
  have h3 : ∑ k, P i k * (gaussianZ (matCLM P) * P⁻¹ k j) =
      gaussianZ (matCLM P) * (P * P⁻¹) i j := by
    rw [mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hZ : ∫ u : ι → ℝ, gaussianWeight (matCLM P) u = gaussianZ (matCLM P) := rfl
  rw [h3, hPP, one_apply, hZ]
  split_ifs <;> ring


/-! ### Adapters: the seabed's Gaussian theorems for a positive definite matrix -/

theorem matCLM_mul (P Q : Matrix ι ι ℝ) : (matCLM P).comp (matCLM Q) = matCLM (P * Q) := by
  ext u
  simp [matCLM_apply, mulVec_mulVec]

theorem matCLM_one : matCLM (1 : Matrix ι ι ℝ) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  ext u
  simp [matCLM_apply]

theorem matCLM_comp_inv {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    (matCLM P).comp (matCLM P⁻¹) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  rw [matCLM_mul, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP.det_pos.ne'), matCLM_one]

theorem matCLM_injective {P : Matrix ι ι ℝ} (hP : P.PosDef) : Function.Injective (matCLM P) := by
  intro u v huv
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP.det_pos.ne')
  have h := congrArg (fun w => P⁻¹ *ᵥ w) huv
  simpa [matCLM_apply, mulVec_mulVec, hPP] using h

/-- **Gaussian quadratic expectation for a positive definite precision**, with no hypothesis
package: `∫ ⟨u, H u⟩ e^{-½ uᵀ P u} = Z · ∑ᵢⱼ Hᵢⱼ (P⁻¹)ᵢⱼ`. -/
theorem gaussian_quadForm_integral_posDef {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    ∫ u : ι → ℝ, quadForm H u * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * hessInvPairing H (matCLM P⁻¹) :=
  gaussian_quadForm_integral H (matCLM P) (matCLM P⁻¹) (matCLM_comp_inv hP) (matCLM_injective hP)
    (integrable_gaussianWeight_matCLM hP)
    (fun k j => integrable_coord_mul_gaussianWeight_matCLM hP k j)
    (fun j i => integrable_coord_mul_apply_gaussianWeight_matCLM hP i j)
    (fun i j => fubiniIBPHypothesis_matCLM hP i j)

theorem matCLM_single (P : Matrix ι ι ℝ) (j i : ι) :
    (matCLM P (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i = P i j := by
  simp [matCLM_apply, Matrix.col_apply]

theorem hessInvPairing_matCLM (H Pinv : Matrix ι ι ℝ) :
    hessInvPairing (matCLM H) (matCLM Pinv) = ∑ i, ∑ j, H i j * Pinv i j := by
  unfold hessInvPairing
  simp_rw [matCLM_single]

/-- **The Gaussian LLC for a positive definite Hessian**, with no hypothesis package:
`t E[½ ⟨u, H u⟩] = d/2` under `e^{-½ t uᵀ H u}`. -/
theorem gaussian_llc_posDef {H : Matrix ι ι ℝ} (hH : H.PosDef) {t : ℝ} (ht : 0 < t) :
    t * ((∫ u : ι → ℝ, (1 / 2 * quadForm (matCLM H) u) * gaussianWeight (matCLM (t • H)) u) /
      gaussianZ (matCLM (t • H))) = Fintype.card ι / 2 := by
  have hP : (t • H).PosDef := hH.smul ht
  have hdet : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  have hinv : (t • H)⁻¹ = t⁻¹ • H⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht.ne', one_smul,
      Matrix.mul_nonsing_inv H hdet]
  have hhalf : (∫ u : ι → ℝ, (1 / 2 * quadForm (matCLM H) u) * gaussianWeight (matCLM (t • H)) u) =
      1 / 2 * ∫ u : ι → ℝ, quadForm (matCLM H) u * gaussianWeight (matCLM (t • H)) u := by
    rw [← integral_const_mul]
    congr 1; funext u; ring
  have hsym : ∀ i j, H⁻¹ i j = H⁻¹ j i := fun i j => by
    have := (Matrix.posDef_inv_iff.mpr hH).1.apply i j
    simpa using this.symm
  have htr : ∑ i, ∑ j, H i j * (t⁻¹ • H⁻¹) i j = Fintype.card ι / t := by
    have h1 : ∀ i, ∑ j, H i j * (t⁻¹ • H⁻¹) i j = t⁻¹ := fun i => by
      have hrow : ∑ j, H i j * H⁻¹ j i = 1 := by
        have := congrFun (congrFun (Matrix.mul_nonsing_inv H hdet) i) i
        rwa [mul_apply, one_apply_eq] at this
      calc ∑ j, H i j * (t⁻¹ • H⁻¹) i j = t⁻¹ * ∑ j, H i j * H⁻¹ j i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Matrix.smul_apply, smul_eq_mul, hsym i j]
            ring
        _ = t⁻¹ := by rw [hrow, mul_one]
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [hhalf, gaussian_quadForm_integral_posDef hP, hinv, hessInvPairing_matCLM, htr]
  have hZ := (gaussianZ_matCLM_pos hP).ne'
  field_simp

end Laplace.Multi
