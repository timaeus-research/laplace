/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.AffineConvexity
import Laplace.Multi.IntegratedSusceptibility

/-!
# The mean map is injective: response coordinates on the data manifold

On an affine family of data `L_a = L₀ + ∑ aᵢ Rᵢ` the **mean map**

  `m(a) = (⟨Rᵢ⟩_{t,a})ᵢ`   (`meanMap`)

is the gradient of the concave free energy (Legendre duality: `D_v log Z = −t ⟨R_v⟩ = −t ∑ vᵢ mᵢ`,
`hasDerivAt_affLogZ_dir'`). If no nonzero direction has an almost surely constant loss contrast on
the support of the prior, the mean map is **injective** (`meanMap_injective`): the point of the data
manifold is determined by the responses `⟨Rᵢ⟩`. The proof is one line of geometry on the mixture
line from `a` to `b`: the mean of the contrast `R_{b−a}` is strictly decreasing along it
(`mixExp_strictAnti`), so it cannot take the same value at both ends — but `∑ (b−a)ᵢ mᵢ` would be
the same at both ends if `m(a) = m(b)`.

This is the multivariate strict identifiability of the response programme: on the identifiable
quotient the loss expectations are global coordinates (Astra, round 22).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The mean map `a ↦ (⟨Rᵢ⟩_{t,a})ᵢ` of the affine family. -/
noncomputable def meanMap (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    ι → ℝ :=
  fun i ↦ priorExp μ π (affLoss L₀ R a) (R i) t

/-- Linearity of the posterior expectation in the observable, for a direction loss. -/
theorem priorExp_dirLoss {π L : X → ℝ} {t : ℝ} (hν : Integrable (baseWeight π L t) μ)
    {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (v : ι → ℝ) :
    priorExp μ π L (dirLoss R v) t = ∑ i, v i * priorExp μ π L (R i) t := by
  have hint : ∀ i, Integrable (fun x ↦ v i * (R i x * (Real.exp (-(t * L x)) * π x))) μ := by
    intro i
    obtain ⟨hm, M, hM⟩ := hR i
    exact (hν.bdd_mul hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hM x)).const_mul _
  unfold priorExp
  have hnum : ∫ x, dirLoss R v x * Real.exp (-(t * L x)) * π x ∂μ =
      ∑ i, v i * ∫ x, R i x * Real.exp (-(t * L x)) * π x ∂μ := by
    have e : ∀ x, dirLoss R v x * Real.exp (-(t * L x)) * π x =
        ∑ i, v i * (R i x * (Real.exp (-(t * L x)) * π x)) := fun x ↦ by
      simp only [dirLoss, Finset.sum_mul, mul_assoc]
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [MeasureTheory.integral_const_mul]
    simp only [mul_assoc]
  rw [hnum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ ↦ mul_div_assoc _ _ _

variable [Nonempty X]

/-- **Legendre duality**: `D_v log Z_t(L_a) = −t ∑ᵢ vᵢ mᵢ(a)` — the mean map is (minus `1/t`
times) the gradient of the log-partition function. -/
theorem TiltData.hasDerivAt_affLogZ_dir' {π L₀ : X → ℝ} {R : ι → X → ℝ} {a : ι → ℝ} {t M₀ : ℝ}
    (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀) (hR : ∀ i, Bdd (R i))
    (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ affLogZ μ π L₀ R t (a + ε • v))
      (-t * ∑ i, v i * meanMap μ π L₀ R t a i) 0 := by
  have := h.hasDerivAt_affLogZ_dir hR v
  rwa [priorExp_dirLoss h.ν_int hR] at this

/-- **The mean map is injective** when no nonzero direction has an almost surely constant loss
contrast on the support of the prior: the responses `⟨Rᵢ⟩_{t,a}` are coordinates on the data
manifold. -/
theorem meanMap_injective {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) :
    Function.Injective (meanMap μ π L₀ R t) := by
  intro a b hab
  by_contra hne
  have hv : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a (b - a) t
  obtain ⟨M', h'⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR b (b - a) t
  have hlt := h.mixExp_strictAnti ht (hnd _ hv) zero_lt_one
  have e0 : mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t 0 =
      priorExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) t := by
    unfold mixExp
    rw [show pathLoss (affLoss L₀ R a) (dirLoss R (b - a)) 0 = affLoss L₀ R a from
      funext fun x ↦ by simp [pathLoss]]
  have e1 : mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t 1 =
      priorExp μ π (affLoss L₀ R b) (dirLoss R (b - a)) t := by
    unfold mixExp
    rw [← affLoss_add_smul, one_smul, add_sub_cancel]
  simp only at hlt
  rw [e0, e1, priorExp_dirLoss h.ν_int hR, priorExp_dirLoss h'.ν_int hR] at hlt
  have hm : ∀ i, priorExp μ π (affLoss L₀ R a) (R i) t = priorExp μ π (affLoss L₀ R b) (R i) t :=
    fun i ↦ by simpa [meanMap] using congrFun hab i
  simp only [hm] at hlt
  exact lt_irrefl _ hlt

end Laplace.Multi
