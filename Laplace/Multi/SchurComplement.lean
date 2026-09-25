/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ContractionIdentity
import Laplace.Multi.FullMeanGeometry

/-!
# The Schur complement: the slice metric is the minimal lift of the full metric

The full Fisher matrix of the joint family at the natural point `θ` is the block matrix
`G = [[σ², cᵀ], [c, C]]` with `σ² = Var(L₀)`, `c = Cov(R, L₀)` (`natc`) and `C = Cov(R, R)` (`natC`)
(`jointCov_mulVec_none`, `jointCov_mulVec_some`). Its Schur complement is the residual variance
`δ = σ² − cᵀC⁻¹c = Var(H)`, `H = L₀ − b·R`, `b = C⁻¹c` (`natCov_natH_self`), positive under joint
nondegeneracy (`natVarH_pos`). Solving the block system gives the inverse full metric on a full
mean velocity `(u̇, Ṁ)`:

  `(u̇, Ṁ) ⬝ G⁻¹ (u̇, Ṁ) = Ṁ ⬝ C⁻¹ Ṁ + (u̇ − b·Ṁ)² / δ`   (`dotProduct_jointCov_inv`).

So the slice inverse-covariance metric `Ṁ ⬝ C⁻¹ Ṁ` is the **minimum** of the full inverse-covariance
cost over all lifts `u̇` of a prescribed response velocity, attained exactly at the slice tangent
`u̇ = b·Ṁ` (`dotProduct_natC_inv_le_jointCov_inv`, `dotProduct_jointCov_inv_slice_tangent`): the
temperature slice is the leaf along which the full geometry is cheapest per unit of response, which
is the metric face of the profile geometry (`ProfileGeometry`) and of the mixed-coordinate
orthogonality `δ dt² + dMᵀC⁻¹dM` (`natForm_sliceInv_deriv`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [DecidableEq ι] [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π)
  (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
  {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  (hjnd : ∀ v : Option ι → ℝ, v ≠ 0 →
    ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss (jointStat L₀ R) v x = c)

omit [DecidableEq ι] [Nonempty X] in
/-- The base row of the full covariance: `(G w)₀ = σ² w₀ + c·w_R`. -/
theorem jointCov_mulVec_none (θ : Option ι → ℝ) (w : Option ι → ℝ) :
    (featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ).mulVec w none =
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) L₀ L₀ 1 * w none +
        dotProduct (natc μ π L₀ R θ) (fun i ↦ w (some i)) := by
  simp only [Matrix.mulVec, dotProduct, featCov, Matrix.of_apply, Fintype.sum_option, natc,
    jointStat, Option.elim_none, Option.elim_some]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [priorCov_comm]

omit [DecidableEq ι] [Nonempty X] in
/-- The feature rows of the full covariance: `(G w)_R = c w₀ + C w_R`. -/
theorem jointCov_mulVec_some (θ : Option ι → ℝ) (w : Option ι → ℝ) (i : ι) :
    (featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ).mulVec w (some i) =
      natc μ π L₀ R θ i * w none + (natC μ π L₀ R θ).mulVec (fun j ↦ w (some j)) i := by
  simp only [Matrix.mulVec, dotProduct, featCov, Matrix.of_apply, Fintype.sum_option, natc, natC,
    jointStat, Option.elim_none, Option.elim_some]

include hπm hπi hπ hπpos hL₀m hL₀ hR hnd hjnd

omit hnd in
/-- **The residual variance is positive** under joint nondegeneracy. -/
theorem natVarH_pos {θ : Option ι → ℝ} :
    0 < priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ)
      (natH μ π L₀ R θ) 1 := by
  have hS := bdd_jointStat hL₀m hL₀ hR
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hH : Bdd (natH μ π L₀ R θ) := by
    have : natH μ π L₀ R θ = fun x ↦ L₀ x + (-1) * dirLoss R (natb μ π L₀ R θ) x := by
      funext x; simp only [natH]; ring
    rw [this]
    exact hL.add ((bdd_dirLoss hR _).const_mul _)
  rcases (priorCov_self_nonneg' hπm hπi hπ hπpos measurable_const abs_zero_fun_le hS (t := 1) θ
    hH).lt_or_eq with h | h
  · exact h
  · exfalso
    have hZ := (affZ_pos hπm hπi hπ hπpos measurable_const abs_zero_fun_le hS (t := 1) θ).ne'
    have h0 : Integrable (fun x ↦ Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ x))
        * π x) μ :=
      (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos measurable_const abs_zero_fun_le
        hS (t := 1) θ (Bdd.const 1)).congr (Eventually.of_forall fun x ↦ by simp only [one_mul])
    have h1 := integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos measurable_const abs_zero_fun_le
      hS (t := 1) θ hH
    have h2 := integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos measurable_const abs_zero_fun_le
      hS (t := 1) θ (hH.mul hH)
    have hc := ae_eq_const_of_priorCov_self_eq_zero hπ hZ h0 h1 h2 h.symm
    refine hjnd (fun j ↦ j.elim 1 fun i ↦ -natb μ π L₀ R θ i) ?_
      ⟨priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ) 1, ?_⟩
    · intro hv
      have := congrFun hv none
      simp at this
    · filter_upwards [hc] with x hx _
      rw [← hx]
      simp only [dirLoss, Fintype.sum_option, Option.elim_none, Option.elim_some, jointStat, natH,
        one_mul, neg_mul, Finset.sum_neg_distrib]
      ring

/-- **The Schur complement identity**: on a full mean velocity `d = (d₀, d_R)`,
`d ⬝ G⁻¹ d = d_R ⬝ C⁻¹ d_R + (d₀ − b·d_R)² / Var(H)`. -/
theorem dotProduct_jointCov_inv {θ : Option ι → ℝ} (hθ : 0 < θ none) (d : Option ι → ℝ) :
    dotProduct d ((featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ)⁻¹.mulVec d) =
      dotProduct (fun i ↦ d (some i)) ((natC μ π L₀ R θ)⁻¹.mulVec fun i ↦ d (some i)) +
        (d none - dotProduct (fun i ↦ d (some i)) (natb μ π L₀ R θ)) ^ 2 /
          priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ)
            (natH μ π L₀ R θ) 1 := by
  have hS := bdd_jointStat hL₀m hL₀ hR
  have hδ := natVarH_pos hπm hπi hπ hπpos hL₀m hL₀ hR hjnd (θ := θ)
  have hδeq := natCov_natH_self hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ
  have hunitG := (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_featCov hπm hπi hπ hπpos measurable_const abs_zero_fun_le hS hjnd one_pos θ)
  have hunitC := (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_natC hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ)
  obtain ⟨dR, hdR⟩ : ∃ dR : ι → ℝ, (fun i ↦ d (some i)) = dR := ⟨_, rfl⟩
  rw [hdR]
  obtain ⟨δ, hδdef⟩ : ∃ δ, priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ)
    (natH μ π L₀ R θ) (natH μ π L₀ R θ) 1 = δ := ⟨_, rfl⟩
  rw [hδdef] at hδ hδeq ⊢
  obtain ⟨τ, hτdef⟩ : ∃ τ, (d none - dotProduct dR (natb μ π L₀ R θ)) / δ = τ := ⟨_, rfl⟩
  have hτ : τ * δ = d none - dotProduct dR (natb μ π L₀ R θ) := by
    rw [← hτdef]; field_simp
  have hsym : ∀ x, dotProduct (natc μ π L₀ R θ) ((natC μ π L₀ R θ)⁻¹.mulVec x) =
      dotProduct (natb μ π L₀ R θ) x := by
    intro x
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv,
      natC_transpose]
    rfl
  obtain ⟨w, hw⟩ : ∃ w : Option ι → ℝ,
      w = fun j ↦ j.elim τ ((natC μ π L₀ R θ)⁻¹.mulVec (dR - τ • natc μ π L₀ R θ)) := ⟨_, rfl⟩
  have hGw : (featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ).mulVec w = d := by
    funext j
    cases j with
    | none =>
      rw [jointCov_mulVec_none, hw]
      simp only [Option.elim_none, Option.elim_some]
      rw [hsym, dotProduct_sub, dotProduct_smul, smul_eq_mul,
        dotProduct_comm (natb μ π L₀ R θ) dR, dotProduct_comm (natb μ π L₀ R θ)]
      linear_combination hτ - τ * hδeq
    | some i =>
      rw [jointCov_mulVec_some, hw]
      simp only [Option.elim_none, Option.elim_some]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunitC, Matrix.one_mulVec, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, ← hdR]
      ring
  have hinv : (featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ)⁻¹.mulVec d = w := by
    calc (featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ)⁻¹.mulVec d
        = (featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ)⁻¹.mulVec
            ((featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ).mulVec w) := by rw [hGw]
      _ = w := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunitG, Matrix.one_mulVec]
  rw [hinv]
  have e : dotProduct d w =
      d none * τ + dotProduct dR ((natC μ π L₀ R θ)⁻¹.mulVec (dR - τ • natc μ π L₀ R θ)) := by
    simp only [dotProduct, Fintype.sum_option, hw, Option.elim_none, Option.elim_some, ← hdR]
  rw [e, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hb : (natC μ π L₀ R θ)⁻¹.mulVec (natc μ π L₀ R θ) = natb μ π L₀ R θ := rfl
  rw [hb]
  have hsq : (d none - dotProduct dR (natb μ π L₀ R θ)) ^ 2 / δ =
      τ * (d none - dotProduct dR (natb μ π L₀ R θ)) := by
    rw [← hτ]
    field_simp
  rw [hsq]
  ring

/-- **The slice metric is the minimal lift**: for every lift `d₀` of the response velocity `d_R`,
`d_R ⬝ C⁻¹ d_R ≤ (d₀, d_R) ⬝ G⁻¹ (d₀, d_R)`. -/
theorem dotProduct_natC_inv_le_jointCov_inv {θ : Option ι → ℝ} (hθ : 0 < θ none)
    (d : Option ι → ℝ) :
    dotProduct (fun i ↦ d (some i)) ((natC μ π L₀ R θ)⁻¹.mulVec fun i ↦ d (some i)) ≤
      dotProduct d ((featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ)⁻¹.mulVec d) := by
  rw [dotProduct_jointCov_inv hπm hπi hπ hπpos hL₀m hL₀ hR hnd hjnd hθ d]
  have hδ := natVarH_pos hπm hπi hπ hπpos hL₀m hL₀ hR hjnd (θ := θ)
  have : 0 ≤ (d none - dotProduct (fun i ↦ d (some i)) (natb μ π L₀ R θ)) ^ 2 /
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ)
        (natH μ π L₀ R θ) 1 := div_nonneg (sq_nonneg _) hδ.le
  linarith

/-- **Equality at the slice tangent**: the lift `d₀ = b·d_R` costs exactly the slice metric. -/
theorem dotProduct_jointCov_inv_slice_tangent {θ : Option ι → ℝ} (hθ : 0 < θ none) (v : ι → ℝ) :
    dotProduct (fun j ↦ j.elim (dotProduct v (natb μ π L₀ R θ)) v)
        ((featCov μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ)⁻¹.mulVec
          fun j ↦ j.elim (dotProduct v (natb μ π L₀ R θ)) v) =
      dotProduct v ((natC μ π L₀ R θ)⁻¹.mulVec v) := by
  rw [dotProduct_jointCov_inv hπm hπi hπ hπpos hL₀m hL₀ hR hnd hjnd hθ]
  simp only [Option.elim_none, Option.elim_some, sub_self]
  simp

end

end Laplace.Multi
