/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MeanMapFDeriv
import Laplace.Multi.IntegratedSusceptibility

/-!
# The Jacobian of the mean map is minus `t` times the response form

The mean map `m(a) = (⟨Rᵢ⟩_{t,a})ᵢ` of an affine data family is Fréchet differentiable, with
Jacobian

  `Dm(a)[v]ᵢ = −t Cov_a(Rᵢ, R_v)`   (`hasFDerivAt_meanMap`, `meanMapDeriv_apply`),

i.e. `Dm(a) = −(1/t) G_a` where `G_a(v, u) = t² Cov_a(R_v, R_u)` is the response form. When no
nonzero direction has an almost surely constant contrast, the Jacobian is injective
(`meanMapDeriv_injective`): the mean map is an immersion, and by `meanMap_injective` an injective
immersion — the response coordinates are genuine local coordinates on the data manifold (Astra's
item D, up to the strict-differentiability step of the inverse function theorem). The proof is the
quotient rule on the numerators of `MeanMapFDeriv` with the inverse composed through
`HasDerivAt.comp_hasFDerivAt`, and `hasFDerivAt_pi` for the vector of means.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The derivative of the numerator with observable `φ` at `a₀`, as a continuous linear map. -/
noncomputable def affNumDeriv (μ : Measure X) (π L₀ φ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a₀ : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∫ x, (-(t * (φ x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x))) • dirCLM R x ∂μ

/-- The Jacobian of the mean map, `Dm(a₀)`. -/
noncomputable def meanMapDeriv (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a₀ : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    (priorZ μ π (affLoss L₀ R a₀) t)⁻¹ • affNumDeriv μ π L₀ (R i) R t a₀ -
      ((∫ x, R i x * Real.exp (-(t * affLoss L₀ R a₀ x)) * π x ∂μ) *
        (priorZ μ π (affLoss L₀ R a₀) t ^ 2)⁻¹) • affNumDeriv μ π L₀ (fun _ ↦ 1) R t a₀

variable [Nonempty X]

/-- **The mean map is Fréchet differentiable with Jacobian `meanMapDeriv`.** -/
theorem hasFDerivAt_meanMap {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
    {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t) {a₀ : ι → ℝ}
    (hZ : priorZ μ π (affLoss L₀ R a₀) t ≠ 0) :
    HasFDerivAt (meanMap μ π L₀ R t) (meanMapDeriv μ π L₀ R t a₀) a₀ := by
  unfold meanMap meanMapDeriv
  refine hasFDerivAt_pi.mpr fun i ↦ ?_
  obtain ⟨_, hZ'⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
  obtain ⟨Mi, hMi⟩ := (hR i).2
  obtain ⟨_, hN'⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := R i) (hR i).1 hMi ht a₀
  simp only [one_mul] at hZ'
  have hZ'' : HasFDerivAt (fun a ↦ priorZ μ π (affLoss L₀ R a) t)
      (affNumDeriv μ π L₀ (fun _ ↦ 1) R t a₀) a₀ := by
    unfold priorZ affNumDeriv
    simpa only [one_mul] using hZ'
  have hZinv := (hasDerivAt_inv hZ).comp_hasFDerivAt a₀ hZ''
  have hN'' : HasFDerivAt (fun a ↦ ∫ x, R i x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ)
      (affNumDeriv μ π L₀ (R i) R t a₀) a₀ := hN'
  have key := hN''.mul hZinv
  refine (key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun a ↦ ?_)).congr_fderiv ?_
  · simp only [priorExp, Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
  · ext v
    simp only [add_apply, smul_apply, sub_apply, smul_eq_mul, Function.comp_apply]
    ring

/-- The Jacobian entry: `Dm(a₀)[v]ᵢ = −t Cov_{a₀}(Rᵢ, R_v)`. -/
theorem meanMapDeriv_apply {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
    {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t) {a₀ : ι → ℝ}
    (hZ : priorZ μ π (affLoss L₀ R a₀) t ≠ 0) (v : ι → ℝ) (i : ι) :
    meanMapDeriv μ π L₀ R t a₀ v i =
      -t * priorCov μ π (affLoss L₀ R a₀) (R i) (dirLoss R v) t := by
  obtain ⟨hZint, _⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp) ht a₀
  obtain ⟨Mi, hMi⟩ := (hR i).2
  obtain ⟨hNint, _⟩ := hasFDerivAt_affNum hπm hπi hπ hL₀m hL₀ hR (φ := R i) (hR i).1 hMi ht a₀
  simp only [meanMapDeriv, ContinuousLinearMap.pi_apply, sub_apply, smul_apply, smul_eq_mul,
    affNumDeriv]
  rw [affNum_fderiv_apply hNint v, affNum_fderiv_apply hZint v]
  unfold priorCov priorExp priorZ
  simp only [one_mul]
  have hZ' : (∫ x, Real.exp (-(t * affLoss L₀ R a₀ x)) * π x ∂μ) ≠ 0 := hZ
  field_simp
  ring

omit [Nonempty X] in
/-- `∑ᵢ vᵢ Cov(Rᵢ, ψ) = Cov(R_v, ψ)` for bounded data. -/
theorem sum_mul_priorCov_eq {π L : X → ℝ} {t : ℝ} (hν : Integrable (baseWeight π L t) μ)
    {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {ψ : X → ℝ} (hψ : Bdd ψ) (v : ι → ℝ) :
    ∑ i, v i * priorCov μ π L (R i) ψ t = priorCov μ π L (dirLoss R v) ψ t := by
  have hR' : ∀ i, Bdd (fun x ↦ R i x * ψ x) := fun i ↦ (hR i).mul hψ
  have e1 : (fun x ↦ dirLoss R v x * ψ x) = dirLoss (fun i x ↦ R i x * ψ x) v := by
    funext x
    simp only [dirLoss, Finset.sum_mul, mul_assoc]
  unfold priorCov
  rw [e1, priorExp_dirLoss hν hR' v, priorExp_dirLoss hν hR v, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **The Jacobian of the mean map is injective** for non-degenerate contrasts: the mean map is an
immersion. -/
theorem meanMapDeriv_injective {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (a₀ : ι → ℝ) :
    Function.Injective (meanMapDeriv μ π L₀ R t a₀) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  by_contra hv0
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a₀ v t
  have hZ : priorZ μ π (affLoss L₀ R a₀) t ≠ 0 := h.ν_pos.ne'
  have hpos := h.mixCov_self_pos (hnd v hv0) 0
  have e0 : mixCov μ π (affLoss L₀ R a₀) (dirLoss R v) (dirLoss R v) (dirLoss R v) t 0 =
      priorCov μ π (affLoss L₀ R a₀) (dirLoss R v) (dirLoss R v) t := by
    unfold mixCov
    rw [show pathLoss (affLoss L₀ R a₀) (dirLoss R v) 0 = affLoss L₀ R a₀ from
      funext fun x ↦ by simp [pathLoss]]
  rw [e0] at hpos
  have hsum : ∑ i, v i * meanMapDeriv μ π L₀ R t a₀ v i =
      -t * priorCov μ π (affLoss L₀ R a₀) (dirLoss R v) (dirLoss R v) t := by
    simp_rw [meanMapDeriv_apply hπm hπi hπ hL₀m hL₀ hR ht hZ v]
    rw [← sum_mul_priorCov_eq h.ν_int hR (bdd_dirLoss hR v) v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hv] at hsum
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hsum
  nlinarith

end Laplace.Multi
