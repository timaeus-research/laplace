/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GaussianMomentsPosDef
import Laplace.Multi.CovarianceExplicit

/-!
# Gaussian integration by parts and the higher-moment packages for a positive definite precision

For `P.PosDef` and `gW := gaussianWeight (matCLM P)`, i.e. `gW u = e^{-½ uᵀ P u}`, Mathlib's
integration by parts on `ι → ℝ` (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) gives, for
a monomial `f u = ∏ s, u (A s)` with `A : Fin n → ι`,

  `∫ (∂ₗ f) gW = ∫ f (P u)ₗ gW`,

which is the seabed's Fubini-IBP hypothesis in cubic (`n = 3`) and quintic (`n = 5`) form.
Together with the integrability of monomials against `gW` (whitening and the product structure of
the standard Gaussian) this discharges `LaplaceCovHypotheses`, `LaplaceCov4MomentHypotheses` and
`LaplaceCov6MomentHypotheses` for `H = matCLM P`, `Hinv = matCLM P⁻¹`, so the seabed's Wick
formulas (`gaussian_fourth_moment_formula`, `gaussian_sixth_moment_formula`) and the explicit
second-order covariance apply with only `P.PosDef`. Contracting the IBP identity with `P⁻¹` gives
Isserlis' theorem in Stein form (`gaussian_stein_prod_coord_matCLM`).

The products `∏_{s ≠ r}` are written as `∏ s, if s = r then 1 else u (A s)`, which keeps every
product indexed by `Fin n`.
-/

open MeasureTheory Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Products with one factor replaced by `1` -/

omit [DecidableEq ι] in
theorem prod_erase_eq_prod_ite {σ : Type*} [Fintype σ] [DecidableEq σ] (f : σ → ℝ) (r : σ) :
    ∏ s ∈ Finset.univ.erase r, f s = ∏ s, (if s = r then 1 else f s) := by
  rw [← Finset.prod_erase (s := Finset.univ) (f := fun s => if s = r then (1 : ℝ) else f s)
    (a := r) (by simp)]
  exact Finset.prod_congr rfl fun s hs => (if_neg (Finset.ne_of_mem_erase hs)).symm

omit [DecidableEq ι] in
theorem prod_ite_eq_prod_succAbove {n : ℕ} (f : Fin (n + 1) → ℝ) (r : Fin (n + 1)) :
    ∏ s, (if s = r then 1 else f s) = ∏ s : Fin n, f (r.succAbove s) := by
  rw [Fin.prod_univ_succAbove (fun s => if s = r then (1 : ℝ) else f s) r, if_pos rfl, one_mul]
  exact Finset.prod_congr rfl fun s _ => if_neg (Fin.succAbove_ne r s)

/-! ### Derivatives of the quadratic form, the Gaussian weight and monomials -/

omit [DecidableEq ι] in
theorem hasFDerivAt_quadForm (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    HasFDerivAt (quadForm H)
      (∑ i, (u i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp H +
        (H u) i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)) u := by
  have h : quadForm H = ∑ i, (fun u : ι → ℝ => u i * (H u) i) := by
    funext u
    simp [quadForm, Finset.sum_apply]
  rw [h]
  refine HasFDerivAt.sum fun i _ => ?_
  exact (hasFDerivAt_apply i u).mul
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp H).hasFDerivAt

omit [DecidableEq ι] in
theorem fderiv_quadForm_apply (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k) (u v : ι → ℝ) :
    fderiv ℝ (quadForm H) u v = 2 * ∑ i, v i * (H u) i := by
  rw [(hasFDerivAt_quadForm H u).fderiv]
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [Finset.sum_add_distrib, hSymm u v, two_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq ι] in
theorem hasFDerivAt_gaussianWeight (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    HasFDerivAt (gaussianWeight H)
      (gaussianWeight H u • ((-(1 / 2 : ℝ)) • fderiv ℝ (quadForm H) u)) u := by
  have hq : HasFDerivAt (quadForm H) (fderiv ℝ (quadForm H) u) u :=
    (hasFDerivAt_quadForm H u).differentiableAt.hasFDerivAt
  exact (hq.const_mul (-(1 / 2 : ℝ))).exp

omit [DecidableEq ι] in
theorem differentiable_gaussianWeight (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    Differentiable ℝ (gaussianWeight H) :=
  fun u => (hasFDerivAt_gaussianWeight H u).differentiableAt

omit [DecidableEq ι] in
theorem fderiv_gaussianWeight_apply (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hSymm : ∀ x y, ∑ k, x k * (H y) k = ∑ k, y k * (H x) k) (u v : ι → ℝ) :
    fderiv ℝ (gaussianWeight H) u v = -(∑ i, v i * (H u) i) * gaussianWeight H u := by
  rw [(hasFDerivAt_gaussianWeight H u).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, fderiv_quadForm_apply H hSymm]
  ring

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
theorem hasFDerivAt_prod_coord {n : ℕ} (A : Fin n → ι) (u : ι → ℝ) :
    HasFDerivAt (fun u : ι → ℝ => ∏ s, u (A s))
      (∑ r, (∏ s ∈ Finset.univ.erase r, u (A s)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) (A r)) u := by
  exact HasFDerivAt.finsetProd (u := Finset.univ) (g := fun s (u : ι → ℝ) => u (A s))
    (g' := fun s => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) (A s)) (x := u)
    (fun s _ => hasFDerivAt_apply (A s) u)

set_option linter.unusedFintypeInType false in
theorem fderiv_prod_coord_apply {n : ℕ} (A : Fin n → ι) (u : ι → ℝ) (l : ι) :
    fderiv ℝ (fun u : ι → ℝ => ∏ s, u (A s)) u (Pi.single l 1) =
      ∑ r, if l = A r then ∏ s, (if s = r then 1 else u (A s)) else 0 := by
  rw [(hasFDerivAt_prod_coord A u).fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [prod_erase_eq_prod_ite]
  by_cases h : l = A r
  · simp [h]
  · simp [h, Ne.symm h]

/-! ### Integrability of monomials against the Gaussian weight -/

omit [DecidableEq ι] in
theorem integrable_monomial_std_gaussian_pi {n : ℕ} (k : Fin n → ι) :
    Integrable (fun v : ι → ℝ => (∏ s, v (k s)) * Real.exp (-(1 / 2) * ∑ i, v i * v i)) := by
  classical
  have hprod : ∀ v : ι → ℝ, (∏ s, v (k s)) * Real.exp (-(1 / 2) * ∑ i, v i * v i) =
      ∏ i, (v i ^ (Finset.univ.filter fun s => k s = i).card * Real.exp (-(v i) ^ 2 / 2)) := by
    intro v
    rw [exp_neg_half_sum_sq, ← Finset.prod_fiberwise Finset.univ k (fun s => v (k s)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    rw [Finset.prod_congr rfl fun s hs => congrArg v (Finset.mem_filter.mp hs).2, Finset.prod_const]
  simp_rw [hprod]
  rw [volume_pi]
  exact Integrable.fintype_prod
    (f := fun (i : ι) (x : ℝ) => x ^ (Finset.univ.filter fun s => k s = i).card *
      Real.exp (-x ^ 2 / 2)) fun i => integrable_pow_mul_exp_neg_sq_div_two _

omit [DecidableEq ι] in
theorem prod_mulVec_apply_eq_sum {n : ℕ} (M : Matrix ι ι ℝ) (A : Fin n → ι) (v : ι → ℝ) :
    ∏ s, (M *ᵥ v) (A s) = ∑ k : Fin n → ι, (∏ s, M (A s) (k s)) * ∏ s, v (k s) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun k _ => Finset.prod_mul_distrib

omit [DecidableEq ι] in
theorem continuous_prod_coord_mul_gaussianWeight (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) {n : ℕ}
    (A : Fin n → ι) :
    Continuous (fun u : ι → ℝ => (∏ s, u (A s)) * gaussianWeight H u) := by
  refine (continuous_finsetProd _ fun s _ => continuous_apply (A s)).mul ?_
  unfold gaussianWeight quadForm
  fun_prop

theorem integrable_prod_coord_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {n : ℕ} (A : Fin n → ι) :
    Integrable (fun u : ι → ℝ => (∏ s, u (A s)) * gaussianWeight (matCLM P) u) := by
  rw [← integrable_comp_mulVec_iff (whiteningOf hP) (det_whiteningOf_ne_zero hP) _
    (continuous_prod_coord_mul_gaussianWeight (matCLM P) A).aestronglyMeasurable]
  simp_rw [gaussianWeight_matCLM_whiteningOf hP, prod_mulVec_apply_eq_sum, Finset.sum_mul,
    mul_assoc]
  exact integrable_finsetSum _ fun k _ => (integrable_monomial_std_gaussian_pi k).const_mul _

theorem integrable_prod_coord_mul_apply_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {n : ℕ} (A : Fin n → ι) (l : ι) :
    Integrable (fun u : ι → ℝ =>
      (∏ s, u (A s)) * (matCLM P u) l * gaussianWeight (matCLM P) u) := by
  have h : ∀ u : ι → ℝ, (∏ s, u (A s)) * (matCLM P u) l * gaussianWeight (matCLM P) u =
      ∑ k, P l k *
        ((∏ s, u ((Fin.cons k A : Fin (n + 1) → ι) s)) * gaussianWeight (matCLM P) u) := by
    intro u
    simp only [matCLM_apply, Matrix.mulVec, dotProduct, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [h]
  exact integrable_finsetSum _ fun k _ =>
    (integrable_prod_coord_mul_gaussianWeight_matCLM hP
      (Fin.cons k A : Fin (n + 1) → ι)).const_mul _

theorem integrable_prod_coord_ite_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {n : ℕ} (A : Fin n → ι) (r : Fin n) :
    Integrable (fun u : ι → ℝ =>
      (∏ s, (if s = r then 1 else u (A s))) * gaussianWeight (matCLM P) u) := by
  cases n with
  | zero => exact r.elim0
  | succ m =>
    simp_rw [prod_ite_eq_prod_succAbove]
    exact integrable_prod_coord_mul_gaussianWeight_matCLM hP (A ∘ r.succAbove)

theorem integrable_ite_prod_coord_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {n : ℕ} (A : Fin n → ι) (l : ι) (r : Fin n) :
    Integrable (fun u : ι → ℝ =>
      (if l = A r then ∏ s, (if s = r then 1 else u (A s)) else 0) *
        gaussianWeight (matCLM P) u) := by
  by_cases h : l = A r
  · simp only [if_pos h]
    exact integrable_prod_coord_ite_mul_gaussianWeight_matCLM hP A r
  · simp only [if_neg h, zero_mul]
    exact integrable_zero _ _ _

theorem integrable_delta_sum_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {n : ℕ} (A : Fin n → ι) (l : ι) :
    Integrable (fun u : ι → ℝ =>
      (∑ r, if l = A r then ∏ s, (if s = r then 1 else u (A s)) else 0) *
        gaussianWeight (matCLM P) u) := by
  simp_rw [Finset.sum_mul]
  exact integrable_finsetSum _ fun r _ =>
    integrable_ite_prod_coord_mul_gaussianWeight_matCLM hP A l r

/-! ### Integration by parts -/

theorem quadForm_symm_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) (x y : ι → ℝ) :
    ∑ k, x k * (matCLM P y) k = ∑ k, y k * (matCLM P x) k := by
  have hPt : Pᵀ = P := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  simp only [matCLM_apply]
  change x ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P *ᵥ x)
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPt, dotProduct_comm]

/-- **Gaussian integration by parts for monomials**:
`∫ (∏ₛ u_{A s}) (P u)ₗ gW = ∫ (∑ᵣ δ_{l, A r} ∏_{s ≠ r} u_{A s}) gW`. -/
theorem gaussian_ibp_prod_coord_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {n : ℕ} (A : Fin n → ι) (l : ι) :
    ∫ u : ι → ℝ, (∏ s, u (A s)) * (matCLM P u) l * gaussianWeight (matCLM P) u =
      ∫ u : ι → ℝ, (∑ r, if l = A r then ∏ s, (if s = r then 1 else u (A s)) else 0) *
        gaussianWeight (matCLM P) u := by
  have hSymm := quadForm_symm_matCLM hP
  have hf'g : Integrable (fun u : ι → ℝ =>
      fderiv ℝ (fun u : ι → ℝ => ∏ s, u (A s)) u (Pi.single l 1) *
        gaussianWeight (matCLM P) u) := by
    refine (integrable_delta_sum_mul_gaussianWeight_matCLM hP A l).congr
      (Filter.Eventually.of_forall fun u => ?_)
    simp only [fderiv_prod_coord_apply]
  have hfg' : Integrable (fun u : ι → ℝ =>
      (∏ s, u (A s)) * fderiv ℝ (gaussianWeight (matCLM P)) u (Pi.single l 1)) := by
    refine (integrable_prod_coord_mul_apply_gaussianWeight_matCLM hP A l).neg.congr
      (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.neg_apply, fderiv_gaussianWeight_apply _ hSymm, Pi.single_apply, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hfg : Integrable (fun u : ι → ℝ => (∏ s, u (A s)) * gaussianWeight (matCLM P) u) :=
    integrable_prod_coord_mul_gaussianWeight_matCLM hP A
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun u _ => (hasFDerivAt_prod_coord A u).differentiableAt)
    (fun u _ => (hasFDerivAt_gaussianWeight _ u).differentiableAt)
  have h1 : ∫ u : ι → ℝ, (∏ s, u (A s)) * fderiv ℝ (gaussianWeight (matCLM P)) u (Pi.single l 1) =
      -∫ u : ι → ℝ, (∏ s, u (A s)) * (matCLM P u) l * gaussianWeight (matCLM P) u := by
    rw [← integral_neg]
    congr 1
    funext u
    simp only [fderiv_gaussianWeight_apply _ hSymm, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have h2 : ∫ u : ι → ℝ,
      fderiv ℝ (fun u : ι → ℝ => ∏ s, u (A s)) u (Pi.single l 1) * gaussianWeight (matCLM P) u =
      ∫ u : ι → ℝ, (∑ r, if l = A r then ∏ s, (if s = r then 1 else u (A s)) else 0) *
        gaussianWeight (matCLM P) u := by
    congr 1
    funext u
    rw [fderiv_prod_coord_apply]
  rw [h1, h2] at key
  linarith

/-- **Isserlis' theorem in Stein form**:
`∫ uⱼ (∏ₛ u_{A s}) gW = ∑ᵣ (P⁻¹)_{j, A r} ∫ (∏_{s ≠ r} u_{A s}) gW`. -/
theorem gaussian_stein_prod_coord_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {n : ℕ} (A : Fin n → ι) (j : ι) :
    ∫ u : ι → ℝ, u j * (∏ s, u (A s)) * gaussianWeight (matCLM P) u =
      ∑ r, P⁻¹ j (A r) *
        ∫ u : ι → ℝ, (∏ s, (if s = r then 1 else u (A s))) * gaussianWeight (matCLM P) u := by
  have hdet : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hinv : ∀ u : ι → ℝ, u j = ∑ l, P⁻¹ j l * (matCLM P u) l := by
    intro u
    have h : P⁻¹ *ᵥ (P *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hdet, Matrix.one_mulVec]
    calc u j = (P⁻¹ *ᵥ (P *ᵥ u)) j := by rw [h]
      _ = ∑ l, P⁻¹ j l * (matCLM P u) l := by simp [Matrix.mulVec, dotProduct]
  have hexp : ∀ u : ι → ℝ, u j * (∏ s, u (A s)) * gaussianWeight (matCLM P) u =
      ∑ l, P⁻¹ j l * ((∏ s, u (A s)) * (matCLM P u) l * gaussianWeight (matCLM P) u) := by
    intro u
    rw [hinv u, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hterm : ∀ l : ι,
      ∫ u : ι → ℝ, (∑ r, if l = A r then ∏ s, (if s = r then 1 else u (A s)) else 0) *
        gaussianWeight (matCLM P) u =
      ∑ r, if l = A r then
        ∫ u : ι → ℝ, (∏ s, (if s = r then 1 else u (A s))) * gaussianWeight (matCLM P) u
      else 0 := by
    intro l
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ fun r _ =>
      integrable_ite_prod_coord_mul_gaussianWeight_matCLM hP A l r]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : l = A r
    · simp only [if_pos h]
    · simp only [if_neg h, zero_mul, integral_zero]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun l _ =>
    (integrable_prod_coord_mul_apply_gaussianWeight_matCLM hP A l).const_mul _]
  simp_rw [integral_const_mul, gaussian_ibp_prod_coord_matCLM hP A, hterm, Finset.mul_sum,
    mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_ite_eq']
  simp

/-! ### The hypothesis packages -/

/-- The seabed's covariance hypothesis package for a positive definite precision. -/
theorem laplaceCovHypotheses_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    LaplaceCovHypotheses (matCLM P) (matCLM P⁻¹) where
  H_symm := quadForm_symm_matCLM hP
  H_inv_right := matCLM_comp_inv hP
  H_inj := matCLM_injective hP
  Z_pos := gaussianZ_matCLM_pos hP
  int_gW := integrable_gaussianWeight_matCLM hP
  int_uk_uj_gW := fun k j => integrable_coord_mul_gaussianWeight_matCLM hP k j
  int_uj_Hi_gW := fun j i => integrable_coord_mul_apply_gaussianWeight_matCLM hP i j
  fubini_ibp := fun i j => fubiniIBPHypothesis_matCLM hP i j

theorem fubiniIBPHypothesisCubic_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) (a b c l : ι) :
    FubiniIBPHypothesisCubic (matCLM P) a b c l := by
  unfold FubiniIBPHypothesisCubic
  have h := gaussian_ibp_prod_coord_matCLM hP ![a, b, c] l
  have hI1 := integrable_delta_sum_mul_gaussianWeight_matCLM hP ![a, b, c] l
  have hI2 := integrable_prod_coord_mul_apply_gaussianWeight_matCLM hP ![a, b, c] l
  simp only [Fin.prod_univ_three, Fin.isValue, cons_val_zero, cons_val_one, cons_val, mul_ite,
    mul_one, ite_mul, one_mul, Fin.sum_univ_three, Fin.reduceEq, ↓reduceIte, one_ne_zero,
    zero_ne_one] at h hI1 hI2
  rw [integral_sub hI1 hI2, h, sub_self]

theorem fubiniIBPHypothesisQuintic_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (a b c d e l : ι) :
    FubiniIBPHypothesisQuintic (matCLM P) a b c d e l := by
  unfold FubiniIBPHypothesisQuintic
  have h := gaussian_ibp_prod_coord_matCLM hP ![a, b, c, d, e] l
  have hI1 := integrable_delta_sum_mul_gaussianWeight_matCLM hP ![a, b, c, d, e] l
  have hI2 := integrable_prod_coord_mul_apply_gaussianWeight_matCLM hP ![a, b, c, d, e] l
  simp only [Fin.prod_univ_five, Fin.isValue, cons_val_zero, cons_val_one, cons_val, mul_ite,
    mul_one, ite_mul, one_mul, Fin.sum_univ_five, Fin.reduceEq, ↓reduceIte, one_ne_zero,
    zero_ne_one] at h hI1 hI2
  rw [integral_sub hI1 hI2, h, sub_self]

/-- The seabed's fourth-moment package for a positive definite precision. -/
theorem laplaceCov4MomentHypotheses_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    LaplaceCov4MomentHypotheses (matCLM P) (matCLM P⁻¹) where
  toLaplaceCovHypotheses := laplaceCovHypotheses_matCLM hP
  int_4moment := fun a b c d => by
    simpa [Fin.prod_univ_four] using
      integrable_prod_coord_mul_gaussianWeight_matCLM hP ![a, b, c, d]
  int_3_Hl := fun a b c l => by
    simpa [Fin.prod_univ_three] using
      integrable_prod_coord_mul_apply_gaussianWeight_matCLM hP ![a, b, c] l
  fubini_ibp_cubic := fubiniIBPHypothesisCubic_matCLM hP

/-- The seabed's sixth-moment package for a positive definite precision. -/
theorem laplaceCov6MomentHypotheses_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    LaplaceCov6MomentHypotheses (matCLM P) (matCLM P⁻¹) where
  toLaplaceCov4MomentHypotheses := laplaceCov4MomentHypotheses_matCLM hP
  int_6moment := fun a b c d e f => by
    simpa [Fin.prod_univ_six] using
      integrable_prod_coord_mul_gaussianWeight_matCLM hP ![a, b, c, d, e, f]
  int_5_Hl := fun a b c d e l => by
    simpa [Fin.prod_univ_five] using
      integrable_prod_coord_mul_apply_gaussianWeight_matCLM hP ![a, b, c, d, e] l
  fubini_ibp_quintic := fubiniIBPHypothesisQuintic_matCLM hP

/-! ### Wick's formulas with only positive definiteness -/

/-- **Fourth moments**, `S = P⁻¹`:
`∫ u_a u_b u_c u_d gW = Z (S_ad S_bc + S_bd S_ac + S_cd S_ab)`. -/
theorem gaussian_fourth_moment_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) (a b c d : ι) :
    ∫ u : ι → ℝ, u a * u b * u c * u d * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * (P⁻¹ a d * P⁻¹ b c + P⁻¹ b d * P⁻¹ a c + P⁻¹ c d * P⁻¹ a b) := by
  rw [gaussian_fourth_moment_formula (laplaceCov4MomentHypotheses_matCLM hP)]
  simp only [matCLM_single]

/-- **Sixth moments**: the fifteen pairings, grouped by the partner of `f`. -/
theorem gaussian_sixth_moment_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef) (a b c d e f : ι) :
    ∫ u : ι → ℝ, u a * u b * u c * u d * u e * u f * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) *
        (P⁻¹ a f * (P⁻¹ b c * P⁻¹ d e + P⁻¹ b d * P⁻¹ c e + P⁻¹ b e * P⁻¹ c d) +
         P⁻¹ b f * (P⁻¹ a c * P⁻¹ d e + P⁻¹ a d * P⁻¹ c e + P⁻¹ a e * P⁻¹ c d) +
         P⁻¹ c f * (P⁻¹ a b * P⁻¹ d e + P⁻¹ a d * P⁻¹ b e + P⁻¹ a e * P⁻¹ b d) +
         P⁻¹ d f * (P⁻¹ a b * P⁻¹ c e + P⁻¹ a c * P⁻¹ b e + P⁻¹ a e * P⁻¹ b c) +
         P⁻¹ e f * (P⁻¹ a b * P⁻¹ c d + P⁻¹ a c * P⁻¹ b d + P⁻¹ a d * P⁻¹ b c)) := by
  rw [gaussian_sixth_moment_formula (laplaceCov6MomentHypotheses_matCLM hP)]
  simp only [matCLM_single]
  ring

end Laplace.Multi
