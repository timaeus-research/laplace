/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LossHessianBlocks
import Laplace.Multi.ChartPathDerivatives
import Laplace.Multi.TwoAxisResponse
import Laplace.Patterning.Jacobi

/-!
# The contraction identity: `tr(C K) = Cov(H, Q) = −∂ₜ log det C` at fixed response

The response block of the loss Hessian at a chart point `(t, M)` is the matrix
`K_ij = κ₃(H, R_{C⁻¹eᵢ}, R_{C⁻¹eⱼ})` (`respHess`, the matrix of `lossHessian_response_response`),
with `C = Cov(R, R)` the covariance and `H = L₀ − b·R` the loss residual. Its contraction with the
covariance is a scalar summary of the bending of the response chart, and it has two other faces:

* **Cumulant form** — by the multilinearity of `κ₃` (`priorCum3_dirLoss_slot`),
  `K = C⁻¹ T C⁻¹` with `T_pq = κ₃(H, R_p, R_q)` (`respHess_eq`), so
  `tr(C K) = tr(T C⁻¹) = ∑_pq (C⁻¹)_qp κ₃(H, R_p, R_q)` (`trace_natC_respHess`);
* **Covariance form** — since `κ₃(H, φ, ψ) = Cov(H, (φ − ⟨φ⟩)(ψ − ⟨ψ⟩))`
  (`priorCum3_eq_priorCov_centred`), `tr(C K) = Cov(H, Q)` with `Q = Zᵀ C⁻¹ Z` the whitened
  squared length of the centred features (`trace_natC_respHess_eq_cov`);
* **Volume form** — along the temperature path at fixed response `M`, Jacobi's formula
  (`Laplace.Patterning.hasDerivAt_log_det`) and the third-cumulant law of the covariance
  (`hasDerivAt_natC_path`) give `d/dt log det C(t, M) = −tr(C K)`
  (`hasDerivAt_log_det_natC_tempPath`):
  the covariance volume at fixed response shrinks with temperature at the rate of the contracted
  bending, equivalently of the covariance between the residual loss and the whitened feature length.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section Cum3

variable {π L : X → ℝ} {t : ℝ} (hν : Integrable (baseWeight π L t) μ)
include hν

/-- **`κ₃` is linear in its second slot over feature combinations.** -/
theorem priorCum3_dirLoss_slot {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {φ χ : X → ℝ} (hφ : Bdd φ)
    (hχ : Bdd χ) (u : ι → ℝ) :
    priorCum3 μ π L φ (dirLoss R u) χ t = ∑ k, u k * priorCum3 μ π L φ (R k) χ t := by
  have e1 : (fun x ↦ φ x * dirLoss R u x * χ x) = dirLoss (fun k x ↦ φ x * R k x * χ x) u := by
    funext x
    simp only [dirLoss, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have e2 : (fun x ↦ φ x * dirLoss R u x) = dirLoss (fun k x ↦ φ x * R k x) u := by
    funext x
    simp only [dirLoss, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have e3 : (fun x ↦ dirLoss R u x * χ x) = dirLoss (fun k x ↦ R k x * χ x) u := by
    funext x
    simp only [dirLoss, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  unfold priorCum3
  rw [e1, e2, e3, priorExp_dirLoss hν (fun k ↦ (hφ.mul (hR k)).mul hχ) u,
    priorExp_dirLoss hν (fun k ↦ hφ.mul (hR k)) u, priorExp_dirLoss hν (fun k ↦ (hR k).mul hχ) u,
    priorExp_dirLoss hν hR u]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **`κ₃` is linear in its third slot over feature combinations.** -/
theorem priorCum3_dirLoss_slot₃ {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {φ ψ : X → ℝ} (hφ : Bdd φ)
    (hψ : Bdd ψ) (u : ι → ℝ) :
    priorCum3 μ π L φ ψ (dirLoss R u) t = ∑ k, u k * priorCum3 μ π L φ ψ (R k) t := by
  rw [priorCum3_swap₂₃, priorCum3_dirLoss_slot hν hR hφ hψ u]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [priorCum3_swap₂₃]

end Cum3

section Centred

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **The third cumulant is the covariance with the centred product**:
`κ₃(φ, ψ, χ) = Cov(φ, (ψ − ⟨ψ⟩)(χ − ⟨χ⟩))`. -/
theorem priorCum3_eq_priorCov_centred (a : ι → ℝ) {φ ψ χ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ)
    (hχ : Bdd χ) :
    priorCum3 μ π (affLoss L₀ R a) φ ψ χ t =
      priorCov μ π (affLoss L₀ R a) φ (fun x ↦ (ψ x - priorExp μ π (affLoss L₀ R a) ψ t) *
        (χ x - priorExp μ π (affLoss L₀ R a) χ t)) t := by
  obtain ⟨b, hb⟩ : ∃ b, priorExp μ π (affLoss L₀ R a) ψ t = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, priorExp μ π (affLoss L₀ R a) χ t = c := ⟨_, rfl⟩
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  rw [hb, hc]
  have e1 : (fun x ↦ φ x * ((ψ x - b) * (χ x - c))) =
      fun x ↦ φ x * ψ x * χ x + ((-b) * (φ x * χ x) + ((-c) * (φ x * ψ x) + (b * c) * φ x)) := by
    funext x; ring
  have e2 : (fun x ↦ (ψ x - b) * (χ x - c)) =
      fun x ↦ ψ x * χ x + ((-b) * χ x + ((-c) * ψ x + (fun _ ↦ b * c) x)) := by
    funext x; ring
  unfold priorCov priorCum3
  rw [e1, e2,
    priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a ((hφ.mul hψ).mul hχ)
      (((hφ.mul hχ).const_mul _).add (((hφ.mul hψ).const_mul _).add (hφ.const_mul _))),
    priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a ((hφ.mul hχ).const_mul _)
      (((hφ.mul hψ).const_mul _).add (hφ.const_mul _)),
    priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a ((hφ.mul hψ).const_mul _) (hφ.const_mul _),
    priorExp_const_mul_bdd, priorExp_const_mul_bdd, priorExp_const_mul_bdd,
    priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hψ.mul hχ)
      ((hχ.const_mul _).add ((hψ.const_mul _).add (Bdd.const _))),
    priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hχ.const_mul _)
      ((hψ.const_mul _).add (Bdd.const _)),
    priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hψ.const_mul _) (Bdd.const _),
    priorExp_const_mul_bdd, priorExp_const_mul_bdd, priorExp_const_fun hZ, hb, hc]
  ring

end Centred

section Contraction

variable [DecidableEq ι] [Nonempty ι] [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π)
  (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀)
  {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)

/-- The residual third-cumulant matrix `T_pq = κ₃(H, R_p, R_q)` at the natural point `θ`. -/
noncomputable def cum3Mat (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) :
    Matrix ι ι ℝ :=
  Matrix.of fun p q ↦ priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ)
    (natH μ π L₀ R θ) (R p) (R q) 1

/-- The response block of the loss Hessian, `K_ij = κ₃(H, R_{C⁻¹eᵢ}, R_{C⁻¹eⱼ})`. -/
noncomputable def respHess (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ)
    (natH μ π L₀ R θ) (dirLoss R ((natC μ π L₀ R θ)⁻¹.mulVec (Pi.single i 1)))
    (dirLoss R ((natC μ π L₀ R θ)⁻¹.mulVec (Pi.single j 1))) 1

/-- The whitened squared length of the centred features, `Q = Zᵀ C⁻¹ Z`. -/
noncomputable def contractObs (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (θ : Option ι → ℝ) : X → ℝ :=
  fun x ↦ ∑ p, ∑ q, (natC μ π L₀ R θ)⁻¹ q p *
    ((R p x - priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R p) 1) *
      (R q x - priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R q) 1))

omit [DecidableEq ι] [Nonempty ι] [Nonempty X] in
/-- The natural covariance matrix is symmetric. -/
theorem natC_transpose (θ : Option ι → ℝ) :
    (natC μ π L₀ R θ).transpose = natC μ π L₀ R θ := by
  ext i j
  exact natC_symm π L₀ R θ j i

omit [Nonempty ι] [Nonempty X] in
/-- The inverse covariance is symmetric. -/
theorem natC_inv_apply_symm (θ : Option ι → ℝ) (i j : ι) :
    (natC μ π L₀ R θ)⁻¹ i j = (natC μ π L₀ R θ)⁻¹ j i := by
  have h : ((natC μ π L₀ R θ)⁻¹).transpose = (natC μ π L₀ R θ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, natC_transpose]
  have := congrFun (congrFun h j) i
  simpa [Matrix.transpose_apply] using this

/-- The matrix of the response block of the loss Hessian at `(t, M)` is `respHess`. -/
theorem lossHessian_response_apply_eq_respHess {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (i j : ι) :
    priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t))
        (natH μ π L₀ R (tempPath μ π L₀ R M t))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint 0 (Pi.single i 1))))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t)).symm (jointPoint 0 (Pi.single j 1)))) 1 =
      respHess μ π L₀ R (tempPath μ π L₀ R M t) i j :=
  lossHessian_response_response hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM (Pi.single i 1)
    (Pi.single j 1)

include hπm hπi hπ hπpos hL₀m hL₀ hR hnd

omit [Nonempty ι] [Nonempty X] hnd in
/-- **The response Hessian is the doubly whitened cumulant matrix**: `K = C⁻¹ T C⁻¹`. -/
theorem respHess_eq (θ : Option ι → ℝ) :
    respHess μ π L₀ R θ = (natC μ π L₀ R θ)⁻¹ * cum3Mat μ π L₀ R θ * (natC μ π L₀ R θ)⁻¹ := by
  have hS := bdd_jointStat hL₀m hL₀ hR
  have hν : Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) 1) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const (M₀ := 0)
      (fun x ↦ by simp) hS θ θ 1).choose_spec.ν_int
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hH : Bdd (natH μ π L₀ R θ) := by
    have : natH μ π L₀ R θ = fun x ↦ L₀ x + (-1) * dirLoss R (natb μ π L₀ R θ) x := by
      funext x; simp only [natH]; ring
    rw [this]
    exact hL.add ((bdd_dirLoss hR _).const_mul _)
  ext i j
  simp only [respHess, cum3Mat, Matrix.of_apply, Matrix.mulVec_single_one]
  rw [priorCum3_dirLoss_slot hν hR hH (bdd_dirLoss hR _),
    Finset.sum_congr rfl fun p _ ↦ by rw [priorCum3_dirLoss_slot₃ hν hR hH (hR p)]]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.col_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_
  rw [natC_inv_apply_symm θ p i]
  ring

omit [Nonempty ι] in
/-- **The contraction identity, cumulant form**: `tr(C K) = tr(T C⁻¹)`. -/
theorem trace_natC_respHess {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    (natC μ π L₀ R θ * respHess μ π L₀ R θ).trace =
      (cum3Mat μ π L₀ R θ * (natC μ π L₀ R θ)⁻¹).trace := by
  have hunit := (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_natC hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ)
  rw [respHess_eq hπm hπi hπ hπpos hL₀m hL₀ hR θ, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]

omit [Nonempty ι] hnd in
/-- **The contraction identity, covariance form**: `tr(T C⁻¹) = Cov(H, Q)` with
`Q = Zᵀ C⁻¹ Z`. -/
theorem trace_cum3Mat_inv_eq_cov (θ : Option ι → ℝ) :
    (cum3Mat μ π L₀ R θ * (natC μ π L₀ R θ)⁻¹).trace =
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ)
        (contractObs μ π L₀ R θ) 1 := by
  have hS := bdd_jointStat hL₀m hL₀ hR
  have hν : Integrable (baseWeight π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) 1) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const (M₀ := 0)
      (fun x ↦ by simp) hS θ θ 1).choose_spec.ν_int
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hH : Bdd (natH μ π L₀ R θ) := by
    have : natH μ π L₀ R θ = fun x ↦ L₀ x + (-1) * dirLoss R (natb μ π L₀ R θ) x := by
      funext x; simp only [natH]; ring
    rw [this]
    exact hL.add ((bdd_dirLoss hR _).const_mul _)
  -- the centred products, indexed by pairs
  set Z : ι → X → ℝ := fun p x ↦
    R p x - priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R p) 1 with hZ
  have hZb : ∀ p, Bdd (Z p) := fun p ↦ by
    have : Z p = fun x ↦ R p x + (-1) * (fun _ ↦
        priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (R p) 1) x := by
      funext x; simp only [hZ]; ring
    rw [this]
    exact (hR p).add ((Bdd.const _).const_mul _)
  have hG : ∀ pq : ι × ι, Bdd (fun x ↦ Z pq.1 x * Z pq.2 x) := fun pq ↦ (hZb _).mul (hZb _)
  have hQ : contractObs μ π L₀ R θ =
      dirLoss (fun pq : ι × ι ↦ fun x ↦ Z pq.1 x * Z pq.2 x)
        (fun pq ↦ (natC μ π L₀ R θ)⁻¹ pq.2 pq.1) := by
    funext x
    simp only [contractObs, dirLoss, hZ]
    rw [← Fintype.sum_prod_type']
  rw [hQ, priorCov_comm, ← sum_mul_priorCov_eq hν hG hH, Fintype.sum_prod_type,
    Laplace.Patterning.trace_mul_eq_double_sum]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [cum3Mat, Matrix.of_apply]
  rw [priorCov_comm, ← priorCum3_eq_priorCov_centred hπm hπi hπ hπpos measurable_const (M₀ := 0)
    (fun x ↦ by simp) hS θ hH (hR p) (hR q), mul_comm]

omit [Nonempty ι] in
/-- **`tr(C K) = Cov(H, Q)`**. -/
theorem trace_natC_respHess_eq_cov {θ : Option ι → ℝ} (hθ : 0 < θ none) :
    (natC μ π L₀ R θ * respHess μ π L₀ R θ).trace =
      priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ)
        (contractObs μ π L₀ R θ) 1 := by
  rw [trace_natC_respHess hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ,
    trace_cum3Mat_inv_eq_cov hπm hπi hπ hπpos hL₀m hL₀ hR θ]

/-- **The volume form of the contraction identity**: along the temperature path at fixed response
`M`, `d/dt log det C(t, M) = −tr(C K)`. -/
theorem hasDerivAt_log_det_natC_tempPath {t₀ : ℝ} (ht : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ Real.log (natC μ π L₀ R (tempPath μ π L₀ R M t)).det)
      (-(natC μ π L₀ R (tempPath μ π L₀ R M t₀) *
        respHess μ π L₀ R (tempPath μ π L₀ R M t₀)).trace) t₀ := by
  have hθ := hasDerivAt_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
  have hpos := tempPath_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
  -- the velocity's score is the residual `H`
  have hp : (Pi.single none 1 : Option ι → ℝ) = jointPoint 1 0 := by
    funext j; cases j <;> simp [jointPoint]
  have hscore : dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
      (tempPath μ π L₀ R M t₀)).symm (Pi.single none 1)) =
      natH μ π L₀ R (tempPath μ π L₀ R M t₀) := by
    rw [hp, chartScore_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM 1 0]
    funext x
    simp only [one_mul, Matrix.mulVec_zero, dirLoss_zero, sub_zero]
  have hH : ∀ i j, HasDerivAt (fun t ↦ natC μ π L₀ R (tempPath μ π L₀ R M t) i j)
      ((Matrix.of fun i j ↦ -priorCum3 μ π
        (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t₀)) (R i) (R j)
        (natH μ π L₀ R (tempPath μ π L₀ R M t₀)) 1) i j) t₀ := by
    intro i j
    have h := hasDerivAt_natC_path hπm hπi hπ hπpos hL₀m hL₀ hR hθ i j
    rw [hscore] at h
    simpa using h
  have hdet : (natC μ π L₀ R (tempPath μ π L₀ R M t₀)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1
      (isUnit_natC hπm hπi hπ hπpos hL₀m hL₀ hR hnd hpos)).ne_zero
  have h := Laplace.Patterning.hasDerivAt_log_det (fun t ↦ natC μ π L₀ R (tempPath μ π L₀ R M t))
    _ t₀ hH hdet
  refine h.congr_deriv ?_
  rw [trace_natC_respHess hπm hπi hπ hπpos hL₀m hL₀ hR hnd hpos,
    Laplace.Patterning.trace_mul_eq_double_sum, Laplace.Patterning.trace_mul_eq_double_sum,
    ← Finset.sum_neg_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [Matrix.of_apply, cum3Mat]
  rw [priorCum3_swap₂₃, priorCum3_swap₁₂]
  ring

/-- **The contraction identity**: `−∂ₜ log det C|_M = tr(C K) = Cov(H, Q)`. -/
theorem hasDerivAt_log_det_natC_tempPath_cov {t₀ : ℝ} (ht : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ Real.log (natC μ π L₀ R (tempPath μ π L₀ R M t)).det)
      (-priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t₀))
        (natH μ π L₀ R (tempPath μ π L₀ R M t₀))
        (contractObs μ π L₀ R (tempPath μ π L₀ R M t₀)) 1) t₀ := by
  have h := hasDerivAt_log_det_natC_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
  rwa [trace_natC_respHess_eq_cov hπm hπi hπ hπpos hL₀m hL₀ hR hnd
    (tempPath_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM)] at h

end Contraction

end Laplace.Multi
