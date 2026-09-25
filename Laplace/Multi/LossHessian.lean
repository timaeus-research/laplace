/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ChartPathDerivatives
import Laplace.Multi.RelativeEntropyGeometry

/-!
# The unified loss Hessian: one residual-cumulant tensor

Let `h(t, M) = ⟨L₀⟩_{t,M}` be the expected loss on the joint response chart (`lossChart`), with
`b = C⁻¹c` the regression coefficients and `H = L₀ − b·R` the residual at the chart point. For a
tangent vector `X = (τ, v)` the chart velocity is `(τ, −τ b − C⁻¹ v)` and its score is
`S_X = τ H − (C⁻¹v)·R` (`chartScore_eq`).

* **Gradient**: `D h[X] = −τ Var(H) + v·b` (`hasDerivAt_lossChart_line`, `lossGrad`).
* **Hessian**: `D²h[X, Y] = κ₃(H, S_X, S_Y)` (`hasDerivAt_lossGrad_line`): the derivative of the
  gradient `D h[X]` along the chart line through `Y` is the residual third cumulant paired with the
  two chart scores. The `tt` block `κ₃(H, H, H)` is `hasDerivAt_deriv_lossSurface`; the mixed block
  is `−κ₃(H, H, (C⁻¹v)·R)` and the `MM` block `κ₃(H, (C⁻¹v)·R, (C⁻¹v')·R)`, i.e. `C⁻¹ K_H C⁻¹` with
  `(K_H)_{ij} = κ₃(H, R_i, R_j)` — **not** `−C⁻¹`, which is the Hessian of the dual potential.

The whole loss curvature is one totally symmetric residual tensor pulled back through the
constrained score map. The proof differentiates the explicit gradient along a chart line using the
path derivatives of `ChartPathDerivatives`; no second derivative of the chart is computed.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The chart domain: positive temperature and response in the interior of the moment body. -/
def chartDomain (μ : Measure X) (π : X → ℝ) (R : ι → X → ℝ) : Set (Option ι → ℝ) :=
  {p | 0 < p none ∧ (fun i ↦ p (some i)) ∈ interior (momentBody μ π R)}

omit [Fintype ι] in
theorem isOpen_chartDomain (π : X → ℝ) (R : ι → X → ℝ) : IsOpen (chartDomain μ π R) :=
  (isOpen_lt continuous_const (continuous_apply none)).inter
    (isOpen_interior.preimage (continuous_pi fun i ↦ continuous_apply (some i)))

omit [MeasurableSpace X] [Fintype ι] in
theorem jointPoint_eq (p : Option ι → ℝ) : jointPoint (p none) (fun i ↦ p (some i)) = p :=
  funext fun j ↦ by cases j <;> rfl

/-- The expected loss on the joint response chart: `h(p) = ⟨L₀⟩_{sliceInv p}`. -/
noncomputable def lossChart (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (p : Option ι → ℝ) :
    ℝ :=
  priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (sliceInv μ π L₀ R p)) L₀ 1

/-- The gradient of the loss chart at `θ` against `(τ, v)`: `−τ Var(H) + v·b`. -/
noncomputable def lossGrad [DecidableEq ι] (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (θ : Option ι → ℝ) (τ : ℝ) (v : ι → ℝ) : ℝ :=
  -τ * priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) (natH μ π L₀ R θ)
    (natH μ π L₀ R θ) 1 + dotProduct v (natb μ π L₀ R θ)

theorem priorCum3_const_mul_left (π L φ ψ χ : X → ℝ) (c t : ℝ) :
    priorCum3 μ π L (fun x ↦ c * φ x) ψ χ t = c * priorCum3 μ π L φ ψ χ t := by
  unfold priorCum3
  have e1 : (fun x ↦ c * φ x * ψ x * χ x) = fun x ↦ c * (φ x * ψ x * χ x) :=
    funext fun x ↦ by ring
  have e2 : (fun x ↦ c * φ x * ψ x) = fun x ↦ c * (φ x * ψ x) := funext fun x ↦ by ring
  have e3 : (fun x ↦ c * φ x * χ x) = fun x ↦ c * (φ x * χ x) := funext fun x ↦ by ring
  rw [e1, e2, e3, priorExp_const_mul_bdd, priorExp_const_mul_bdd, priorExp_const_mul_bdd,
    priorExp_const_mul_bdd]
  ring

/-- The symmetric inverse feature covariance passes across the dot product. -/
theorem dotProduct_natC_inv_mulVec [DecidableEq ι] (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (θ : Option ι → ℝ) (v w : ι → ℝ) :
    dotProduct ((natC μ π L₀ R θ)⁻¹.mulVec v) w = dotProduct v ((natC μ π L₀ R θ)⁻¹.mulVec w) := by
  have hsym : (natC μ π L₀ R θ).transpose = natC μ π L₀ R θ :=
    Matrix.ext fun i j ↦ by rw [Matrix.transpose_apply]; exact natC_symm π L₀ R θ j i
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_nonsing_inv, hsym, dotProduct_comm]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  [Nonempty ι] [DecidableEq ι]
include hπm hπi hπ hπpos hL₀m hL₀ hR hnd

omit [DecidableEq ι] in
theorem tempPath_none_pos {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) : 0 < tempPath μ π L₀ R M t none := by
  rw [tempPath_none hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  exact ht

omit [DecidableEq ι] in
theorem aOf_tempPath {t : ℝ} (ht : 0 < t) {M : ι → ℝ} (hM : M ∈ interior (momentBody μ π R)) :
    aOf (tempPath μ π L₀ R M t) = Function.invFun (meanMap μ π L₀ R t) M := by
  funext i
  simp only [aOf, tempPath_eq_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM, natCoord_some,
    natCoord_none]
  field_simp

omit [DecidableEq ι] in
theorem natC_tempPath {t : ℝ} (ht : 0 < t) {M : ι → ℝ} (hM : M ∈ interior (momentBody μ π R)) :
    natC μ π L₀ R (tempPath μ π L₀ R M t) =
      featCov μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) := by
  rw [natC_eq_featCov π L₀ R (tempPath_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM),
    tempPath_none hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM,
    aOf_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]

theorem natb_tempPath {t : ℝ} (ht : 0 < t) {M : ι → ℝ} (hM : M ∈ interior (momentBody μ π R)) :
    natb μ π L₀ R (tempPath μ π L₀ R M t) = regCoeff μ π L₀ R M t := by
  unfold natb regCoeff
  rw [natC_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM,
    natc_eq_featObsCov π L₀ R (tempPath_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM),
    tempPath_none hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM,
    aOf_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]

/-- **The chart score**: the score of the chart velocity of `(τ, v)` is `τ H − (C⁻¹v)·R`. -/
theorem chartScore_eq {t : ℝ} (ht : 0 < t) {M : ι → ℝ} (hM : M ∈ interior (momentBody μ π R))
    (τ : ℝ) (v : ι → ℝ) :
    dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
        (tempPath μ π L₀ R M t)).symm (jointPoint τ v)) =
      fun x ↦ τ * natH μ π L₀ R (tempPath μ π L₀ R M t) x -
        dirLoss R ((natC μ π L₀ R (tempPath μ π L₀ R M t))⁻¹.mulVec v) x := by
  rw [dirLoss_jointStat_sliceInv_deriv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM,
    natC_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]
  funext x
  simp only [natH, natb_tempPath hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM]

omit [DecidableEq ι] in
/-- **Chart lines**: through a chart point, the partial inverse along `p₀ + s Y` is (eventually) a
differentiable path in natural coordinates with velocity `D sliceInv Y`, staying at positive
temperature. -/
theorem exists_chartLine {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (Y : Option ι → ℝ) :
    ∃ θ : ℝ → Option ι → ℝ,
      (∀ᶠ s in 𝓝 (0 : ℝ), θ s = sliceInv μ π L₀ R (jointPoint t₀ M + s • Y)) ∧
      (∀ s, 0 < θ s none) ∧ θ 0 = tempPath μ π L₀ R M t₀ ∧
      HasDerivAt θ ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
        (tempPath μ π L₀ R M t₀)).symm Y) 0 := by
  classical
  have hp₀ : jointPoint t₀ M ∈ chartDomain μ π R := by
    refine ⟨ht₀, ?_⟩
    simpa using hM
  have hc : Continuous (fun s : ℝ ↦ jointPoint t₀ M + s • Y) := by fun_prop
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), jointPoint t₀ M + s • Y ∈ chartDomain μ π R := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    rw [zero_smul, add_zero]
    exact (isOpen_chartDomain π R).mem_nhds hp₀
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → ℝ, σ = fun s ↦ if jointPoint t₀ M + s • Y ∈ chartDomain μ π R
    then s else 0 := ⟨_, rfl⟩
  have hmem : ∀ s, jointPoint t₀ M + σ s • Y ∈ chartDomain μ π R := by
    intro s
    rw [hσ]
    dsimp only
    split_ifs with h
    · exact h
    · simpa using hp₀
  have hσeq : ∀ᶠ s in 𝓝 (0 : ℝ), σ s = s := by
    filter_upwards [hev] with s hs
    rw [hσ]
    exact if_pos hs
  have hσ0 : σ 0 = 0 := by
    rw [hσ]
    dsimp only
    split_ifs <;> rfl
  refine ⟨fun s ↦ sliceInv μ π L₀ R (jointPoint t₀ M + σ s • Y), ?_, ?_, ?_, ?_⟩
  · filter_upwards [hσeq] with s hs
    rw [hs]
  · intro s
    have h := sliceInv_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd (hmem s).1 (hmem s).2
    rwa [jointPoint_eq] at h
  · simp [hσ0, tempPath]
  · have hline : HasDerivAt (fun s : ℝ ↦ jointPoint t₀ M + σ s • Y) Y (0 : ℝ) :=
      (hasDerivAt_affineLine (jointPoint t₀ M) Y (0 : ℝ)).congr_of_eventuallyEq
        (hσeq.mono fun s hs ↦ by simp only [hs])
    have hstrict := hasStrictFDerivAt_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
      (tempPath_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM)
    have hsm : sliceMap μ π L₀ R (tempPath μ π L₀ R M t₀) = jointPoint t₀ M :=
      sliceMap_sliceInv hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
    rw [hsm] at hstrict
    have h0 : (fun s : ℝ ↦ jointPoint t₀ M + σ s • Y) 0 = jointPoint t₀ M := by simp [hσ0]
    rw [← h0] at hstrict
    exact hstrict.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline

/-- **The gradient of the loss chart**: along `p₀ + s (τ, v)`, `d/ds h = −τ Var(H) + v·b`. -/
theorem hasDerivAt_lossChart_line {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (τ : ℝ) (v : ι → ℝ) :
    HasDerivAt (fun s : ℝ ↦ lossChart μ π L₀ R (jointPoint t₀ M + s • jointPoint τ v))
      (lossGrad μ π L₀ R (tempPath μ π L₀ R M t₀) τ v) (0 : ℝ) := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  obtain ⟨θ, hθeq, hpos, hθ0, hθ⟩ := exists_chartLine hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
    (jointPoint τ v)
  set θ₀ := tempPath μ π L₀ R M t₀ with hθ₀
  have hpos₀ : 0 < θ₀ none := tempPath_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  have h := hasDerivAt_priorExp_natPath hπm hπi hπ hπpos hL₀m hL₀ hR hθ hL
  rw [hθ0] at h
  have hfun : (fun s : ℝ ↦ lossChart μ π L₀ R (jointPoint t₀ M + s • jointPoint τ v)) =ᶠ[𝓝 (0 : ℝ)]
      fun s ↦ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s)) L₀ 1 := by
    filter_upwards [hθeq] with s hs
    simp only [lossChart, hs]
  refine (h.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [chartScore_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM, lossGrad]
  have hH : Bdd (natH μ π L₀ R θ₀) := hL.sub (bdd_dirLoss hR _)
  have hν : Integrable (baseWeight π (affLoss L₀ R (aOf θ₀)) (θ₀ none)) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR (aOf θ₀) (aOf θ₀)
      (θ₀ none)).choose_spec.ν_int
  -- `Cov(L₀, H) = Var(H)`
  have hLH : priorCov μ π (affLoss L₀ R (aOf θ₀)) L₀ (natH μ π L₀ R θ₀) (θ₀ none) =
      priorCov μ π (affLoss L₀ R (aOf θ₀)) (natH μ π L₀ R θ₀) (natH μ π L₀ R θ₀) (θ₀ none) := by
    have h1 := natCov_natH_dirLoss hπm hπi hπ hπpos hL₀m hL₀ hR hnd hpos₀ (natb μ π L₀ R θ₀)
    rw [natCov_eq π L₀ R hpos₀] at h1
    have e2 : priorCov μ π (affLoss L₀ R (aOf θ₀)) (natH μ π L₀ R θ₀) (natH μ π L₀ R θ₀)
        (θ₀ none) = priorCov μ π (affLoss L₀ R (aOf θ₀))
          (fun x ↦ L₀ x - dirLoss R (natb μ π L₀ R θ₀) x) (natH μ π L₀ R θ₀) (θ₀ none) := rfl
    rw [e2, priorCov_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR _ hL (bdd_dirLoss hR _) hH,
      priorCov_comm π _ (dirLoss R (natb μ π L₀ R θ₀)) _ _, h1, sub_zero]
  -- `Cov(L₀, R_{C⁻¹v}) = v · b`
  have hLw : priorCov μ π (affLoss L₀ R (aOf θ₀)) L₀
      (dirLoss R ((natC μ π L₀ R θ₀)⁻¹.mulVec v)) (θ₀ none) = dotProduct v (natb μ π L₀ R θ₀) := by
    rw [priorCov_comm π _ L₀ _ _, ← sum_mul_priorCov_eq hν hR hL _]
    change _ = dotProduct v ((natC μ π L₀ R θ₀)⁻¹.mulVec (natc μ π L₀ R θ₀))
    rw [← dotProduct_natC_inv_mulVec π L₀ R θ₀]
    simp only [dotProduct, natc]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [natCov_eq π L₀ R hpos₀]
  rw [natCov_eq π L₀ R hpos₀, natCov_eq π L₀ R hpos₀,
    priorCov_sub_right hπm hπi hπ hπpos hL₀m hL₀ hR _ (Bdd.const_mul τ hH) (bdd_dirLoss hR _) hL,
    priorCov_const_mul_right', hLH, hLw]
  ring

/-- **The unified loss Hessian**: the derivative of the gradient `D h[(τ, v)]` along the chart line
through `Y` is `κ₃(H, S_{(τ,v)}, S_Y)`, the residual third cumulant paired with the chart scores. -/
theorem hasDerivAt_lossGrad_line {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) (τ : ℝ) (v : ι → ℝ) (Y : Option ι → ℝ) :
    HasDerivAt (fun s : ℝ ↦ lossGrad μ π L₀ R (sliceInv μ π L₀ R (jointPoint t₀ M + s • Y)) τ v)
      (priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (tempPath μ π L₀ R M t₀))
        (natH μ π L₀ R (tempPath μ π L₀ R M t₀))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t₀)).symm (jointPoint τ v)))
        (dirLoss (jointStat L₀ R) ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd
          (tempPath μ π L₀ R M t₀)).symm Y)) 1) (0 : ℝ) := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  obtain ⟨θ, hθeq, hpos, hθ0, hθ⟩ := exists_chartLine hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM Y
  set θ₀ := tempPath μ π L₀ R M t₀ with hθ₀
  have hpos₀ : 0 < θ₀ none := tempPath_none_pos hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  set SY := dirLoss (jointStat L₀ R)
    ((sliceMapEquiv hπm hπi hπ hπpos hL₀m hL₀ hR hnd θ₀).symm Y) with hSY
  have hSYb : Bdd SY := bdd_dirLoss (bdd_jointStat hL₀m hL₀ hR) _
  have hH : Bdd (natH μ π L₀ R θ₀) := hL.sub (bdd_dirLoss hR _)
  -- the two pieces of the gradient along the path
  have hV := hasDerivAt_natVarH_path hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ hpos
  have hb : ∀ i, HasDerivAt (fun s ↦ natb μ π L₀ R (θ s) i)
      (-(natC μ π L₀ R (θ 0))⁻¹.mulVec (fun k ↦ priorCum3 μ π
        (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ 0)) (R k) (natH μ π L₀ R (θ 0)) SY 1) i) 0 :=
    fun i ↦ hasDerivAt_natb_path hπm hπi hπ hπpos hL₀m hL₀ hR hnd hθ hpos i
  have hdot : HasDerivAt (fun s ↦ ∑ i, v i * natb μ π L₀ R (θ s) i)
      (∑ i, v i * -(natC μ π L₀ R (θ 0))⁻¹.mulVec (fun k ↦ priorCum3 μ π
        (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ 0)) (R k) (natH μ π L₀ R (θ 0)) SY 1) i) 0 :=
    HasDerivAt.fun_sum fun i _ ↦ (hb i).const_mul (v i)
  have hsum := (hV.const_mul (-τ)).add hdot
  rw [hθ0] at hsum
  have hfun : (fun s : ℝ ↦ lossGrad μ π L₀ R (sliceInv μ π L₀ R (jointPoint t₀ M + s • Y)) τ v)
      =ᶠ[𝓝 (0 : ℝ)] fun s ↦ -τ * priorCov μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (θ s))
        (natH μ π L₀ R (θ s)) (natH μ π L₀ R (θ s)) 1 + ∑ i, v i * natb μ π L₀ R (θ s) i := by
    filter_upwards [hθeq] with s hs
    simp only [lossGrad, hs, dotProduct]
  refine (hsum.congr_of_eventuallyEq hfun).congr_deriv ?_
  -- identify the derivative with the residual cumulant
  rw [chartScore_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM]
  set w := (natC μ π L₀ R θ₀)⁻¹.mulVec v with hw
  set z : ι → ℝ := fun k ↦ priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ₀) (R k)
    (natH μ π L₀ R θ₀) SY 1 with hz
  have hcum : priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ₀) (natH μ π L₀ R θ₀)
      (fun x ↦ τ * natH μ π L₀ R θ₀ x - dirLoss R w x) SY 1 =
      τ * priorCum3 μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ₀) (natH μ π L₀ R θ₀)
        (natH μ π L₀ R θ₀) SY 1 - dotProduct w z := by
    rw [priorCum3_swap₁₂, natCum3_eq π L₀ R hpos₀,
      priorCum3_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR _ (Bdd.const_mul τ hH) (bdd_dirLoss hR w)
        hH hSYb, priorCum3_const_mul_left,
      priorCum3_dirLoss_left hπm hπi hπ hπpos hL₀m hL₀ hR _ _ hH hSYb, ← natCum3_eq π L₀ R hpos₀]
    simp only [dotProduct, hz]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [natCum3_eq π L₀ R hpos₀]
  have hvz : ∑ i, v i * -(natC μ π L₀ R θ₀)⁻¹.mulVec z i = -dotProduct w z := by
    rw [hw, dotProduct_natC_inv_mulVec π L₀ R θ₀]
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  rw [hcum, hvz]
  ring

end

end Laplace.Multi
