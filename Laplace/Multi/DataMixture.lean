/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SegmentDivergence

/-!
# The data manifold: mixtures of data distributions are affine loss paths

A data distribution is a probability measure `ν` on the sample space `Z`; with a bounded per-sample
loss `ℓ x z` the population loss is `L_ν(x) = ∫ ℓ(x, z) dν(z)` (`dataLoss`), which is *affine* in
`ν`. Hence the segment `ν_s = (1 − s) ν₀ + s ν₁` in the space of data distributions
(`mixMeasure`) is the affine loss path `L_{ν_s} = L_{ν₀} + s (L_{ν₁} − L_{ν₀})`
(`popLoss_mixMeasure`), and the whole response theory of affine loss paths applies verbatim:

* `hasDerivAt_dataMixture_exp`: `d/ds ⟨φ⟩_{t, ν_s} = −t Cov_{t, ν_s}(φ, L_{ν₁} − L_{ν₀})`;
* `dataMixture_KL_eq`, `dataMixture_KL_eq'`:
  `KL(P_{ν₁} ‖ P_{ν₀}) = t² ∫₀¹ s Var_{ν_s}(L_{ν₁} − L_{ν₀}) ds` and
  `KL(P_{ν₀} ‖ P_{ν₁}) = t² ∫₀¹ (1 − s) Var_{ν_s}(…) ds`.

This is the bridge between perturbations of the data distribution and the response of posterior
expectations: the "data direction" is the loss contrast `L_{ν₁} − L_{ν₀}`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {Z : Type*} [MeasurableSpace Z]

/-- The population loss of the data distribution `ν`. -/
noncomputable def dataLoss (ℓ : X → Z → ℝ) (ν : Measure Z) : X → ℝ := fun x ↦ ∫ z, ℓ x z ∂ν

/-- The mixture `(1 − s) ν₀ + s ν₁` of two data distributions. -/
noncomputable def mixMeasure (ν₀ ν₁ : Measure Z) (s : ℝ) : Measure Z :=
  ENNReal.ofReal (1 - s) • ν₀ + ENNReal.ofReal s • ν₁

section

variable {ν₀ ν₁ : Measure Z} [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
  {ℓ : X → Z → ℝ} (hℓ : Measurable (Function.uncurry ℓ)) {M : ℝ} (hM : ∀ x z, |ℓ x z| ≤ M)
include hℓ hM

omit hM in
theorem measurable_ℓ_right (x : X) : Measurable (ℓ x) :=
  hℓ.comp (measurable_const.prodMk measurable_id)

theorem integrable_ℓ_right (ν : Measure Z) [IsProbabilityMeasure ν] (x : X) :
    Integrable (ℓ x) ν :=
  Integrable.of_bound (measurable_ℓ_right hℓ x).aestronglyMeasurable M
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hM x z)

omit hM in
theorem measurable_popLoss (ν : Measure Z) [SFinite ν] : Measurable (dataLoss ℓ ν) :=
  (hℓ.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

omit [MeasurableSpace X] hℓ in
theorem abs_popLoss_le (ν : Measure Z) [IsProbabilityMeasure ν] (x : X) : |dataLoss ℓ ν x| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := ℓ x) (C := M)
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hM x z)
  simpa [dataLoss, measureReal_def] using h

/-- **The population loss is affine along a mixture of data distributions.** -/
theorem popLoss_mixMeasure {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (x : X) :
    dataLoss ℓ (mixMeasure ν₀ ν₁ s) x =
      dataLoss ℓ ν₀ x + s * (dataLoss ℓ ν₁ x - dataLoss ℓ ν₀ x) := by
  unfold dataLoss mixMeasure
  rw [integral_add_measure ((integrable_ℓ_right hℓ hM ν₀ x).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_ℓ_right hℓ hM ν₁ x).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by linarith [hs.2]),
    ENNReal.toReal_ofReal hs.1, smul_eq_mul, smul_eq_mul]
  ring

/-- The loss contrast between two data distributions. -/
noncomputable def lossContrast (ℓ : X → Z → ℝ) (ν₀ ν₁ : Measure Z) : X → ℝ :=
  fun x ↦ dataLoss ℓ ν₁ x - dataLoss ℓ ν₀ x

theorem popLoss_mixMeasure_eq_pathLoss {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    dataLoss ℓ (mixMeasure ν₀ ν₁ s) = pathLoss (dataLoss ℓ ν₀) (lossContrast ℓ ν₀ ν₁) s :=
  funext fun x ↦ by rw [popLoss_mixMeasure hℓ hM hs x]; rfl

/-- The mixture family as a one-parameter affine family (`ι = Unit`). -/
theorem popLoss_mixMeasure_eq_affLoss {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    dataLoss ℓ (mixMeasure ν₀ ν₁ s) =
      affLoss (dataLoss ℓ ν₀) (fun _ : Unit ↦ lossContrast ℓ ν₀ ν₁) (fun _ ↦ s) := by
  funext x
  rw [popLoss_mixMeasure hℓ hM hs x]
  simp [affLoss, lossContrast]

theorem bdd_lossContrast_unit : ∀ _ : Unit, Bdd (lossContrast ℓ ν₀ ν₁) := fun _ ↦
  ⟨(measurable_popLoss hℓ ν₁).sub (measurable_popLoss hℓ ν₀), 2 * M, fun x ↦ by
    calc |dataLoss ℓ ν₁ x - dataLoss ℓ ν₀ x| ≤ |dataLoss ℓ ν₁ x| + |dataLoss ℓ ν₀ x| := abs_sub _ _
      _ ≤ M + M := add_le_add (abs_popLoss_le hM ν₁ x) (abs_popLoss_le hM ν₀ x)
      _ = 2 * M := by ring⟩

variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {t : ℝ}
include hπm hπi hπ hπpos

omit [Nonempty X] in
theorem tiltData_dataMixture (t : ℝ) :
    TiltData μ (baseWeight π (dataLoss ℓ ν₀) t) (lossContrast ℓ ν₀ ν₁) (2 * M) := by
  refine tiltData_baseWeight_of_bounded (μ := μ) hπm hπi (fun x ↦ (hπ x).le) hπpos
    (measurable_popLoss hℓ ν₀) (abs_popLoss_le hM ν₀)
    ((measurable_popLoss hℓ ν₁).sub (measurable_popLoss hℓ ν₀)) (fun x ↦ ?_) t
  calc |dataLoss ℓ ν₁ x - dataLoss ℓ ν₀ x| ≤ |dataLoss ℓ ν₁ x| + |dataLoss ℓ ν₀ x| := abs_sub _ _
    _ ≤ M + M := add_le_add (abs_popLoss_le hM ν₁ x) (abs_popLoss_le hM ν₀ x)
    _ = 2 * M := by ring

/-- **Response to a perturbation of the data distribution**: along `ν_s = (1 − s) ν₀ + s ν₁`,
`d/ds ⟨φ⟩_{t, ν_s} = −t Cov_{t, ν_s}(φ, L_{ν₁} − L_{ν₀})` for `s ∈ (0, 1)`. -/
theorem hasDerivAt_dataMixture_exp {φ : X → ℝ} (hφ : Bdd φ) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ priorExp μ π (dataLoss ℓ (mixMeasure ν₀ ν₁ s)) φ t)
      (-t * priorCov μ π (dataLoss ℓ (mixMeasure ν₀ ν₁ s₀)) φ (lossContrast ℓ ν₀ ν₁) t) s₀ := by
  have hT := tiltData_dataMixture hℓ hM hπm hπi hπ hπpos (ν₀ := ν₀) (ν₁ := ν₁) t
  have h := hT.hasDerivAt_mixExp hφ s₀
  have hfun : (fun s ↦ priorExp μ π (dataLoss ℓ (mixMeasure ν₀ ν₁ s)) φ t) =ᶠ[𝓝 s₀]
      fun s ↦ mixExp μ π (dataLoss ℓ ν₀) (lossContrast ℓ ν₀ ν₁) φ t s := by
    filter_upwards [Ioo_mem_nhds hs₀.1 hs₀.2] with s hs
    unfold mixExp
    rw [popLoss_mixMeasure_eq_pathLoss hℓ hM (Ioo_subset_Icc_self hs)]
  refine (h.congr_of_eventuallyEq hfun).congr_deriv ?_
  unfold mixCov
  rw [popLoss_mixMeasure_eq_pathLoss hℓ hM (Ioo_subset_Icc_self hs₀)]

/-- **The divergence between the posteriors of two data distributions**:
`KL(P_{ν₁} ‖ P_{ν₀}) = t² ∫₀¹ s Var_{t, ν_s}(L_{ν₁} − L_{ν₀}) ds`. -/
theorem dataMixture_KL_eq (ht : 0 < t) :
    mixKL μ π (dataLoss ℓ ν₁) (fun x ↦ -lossContrast ℓ ν₀ ν₁ x) t 0 1 =
      t ^ 2 * ∫ s in (0 : ℝ)..1, s * priorCov μ π (dataLoss ℓ (mixMeasure ν₀ ν₁ s))
        (lossContrast ℓ ν₀ ν₁) (lossContrast ℓ ν₀ ν₁) t := by
  have hR := bdd_lossContrast_unit hℓ hM (ν₀ := ν₀) (ν₁ := ν₁)
  have h := mixKL_eq_integral_mul_var hπm hπi hπ hπpos (measurable_popLoss hℓ ν₀)
    (abs_popLoss_le hM ν₀) hR ht (fun _ : Unit ↦ (0 : ℝ)) (fun _ ↦ 1)
  have e1 : affLoss (dataLoss ℓ ν₀) (fun _ : Unit ↦ lossContrast ℓ ν₀ ν₁) (fun _ ↦ (1 : ℝ)) =
      dataLoss ℓ ν₁ := by
    rw [← popLoss_mixMeasure_eq_affLoss hℓ hM (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)]
    unfold mixMeasure
    simp
  have e2 : dirLoss (fun _ : Unit ↦ lossContrast ℓ ν₀ ν₁) ((fun _ ↦ (0 : ℝ)) - fun _ ↦ 1) =
      fun x ↦ -lossContrast ℓ ν₀ ν₁ x := by
    funext x
    simp [dirLoss]
  rw [e1, e2] at h
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  have hs' : s ∈ Icc (0 : ℝ) 1 := by rwa [uIcc_of_le (zero_le_one' ℝ)] at hs
  simp only [segVar]
  have ea : ((fun _ : Unit ↦ (0 : ℝ)) + s • ((fun _ ↦ (1 : ℝ)) - fun _ ↦ 0)) = fun _ ↦ s := by
    funext u
    simp
  have ed : dirLoss (fun _ : Unit ↦ lossContrast ℓ ν₀ ν₁) ((fun _ ↦ (1 : ℝ)) - fun _ ↦ 0) =
      lossContrast ℓ ν₀ ν₁ := by
    funext x
    simp [dirLoss]
  rw [popLoss_mixMeasure_eq_affLoss hℓ hM hs', ea, ed]

/-- `KL(P_{ν₀} ‖ P_{ν₁}) = t² ∫₀¹ (1 − s) Var_{t, ν_s}(L_{ν₁} − L_{ν₀}) ds`. -/
theorem dataMixture_KL_eq' (ht : 0 < t) :
    mixKL μ π (dataLoss ℓ ν₀) (lossContrast ℓ ν₀ ν₁) t 0 1 =
      t ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * priorCov μ π (dataLoss ℓ (mixMeasure ν₀ ν₁ s))
        (lossContrast ℓ ν₀ ν₁) (lossContrast ℓ ν₀ ν₁) t := by
  have hR := bdd_lossContrast_unit hℓ hM (ν₀ := ν₀) (ν₁ := ν₁)
  have h := mixKL_eq_integral_one_sub_mul_var hπm hπi hπ hπpos (measurable_popLoss hℓ ν₀)
    (abs_popLoss_le hM ν₀) hR ht (fun _ : Unit ↦ (0 : ℝ)) (fun _ ↦ 1)
  have e1 : affLoss (dataLoss ℓ ν₀) (fun _ : Unit ↦ lossContrast ℓ ν₀ ν₁) (fun _ ↦ (0 : ℝ)) =
      dataLoss ℓ ν₀ := by
    funext x
    simp [affLoss]
  have e2 : dirLoss (fun _ : Unit ↦ lossContrast ℓ ν₀ ν₁) ((fun _ ↦ (1 : ℝ)) - fun _ ↦ 0) =
      lossContrast ℓ ν₀ ν₁ := by
    funext x
    simp [dirLoss]
  rw [e1, e2] at h
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  have hs' : s ∈ Icc (0 : ℝ) 1 := by rwa [uIcc_of_le (zero_le_one' ℝ)] at hs
  simp only [segVar]
  have ea : ((fun _ : Unit ↦ (0 : ℝ)) + s • ((fun _ ↦ (1 : ℝ)) - fun _ ↦ 0)) = fun _ ↦ s := by
    funext u
    simp
  have ed : dirLoss (fun _ : Unit ↦ lossContrast ℓ ν₀ ν₁) ((fun _ ↦ (1 : ℝ)) - fun _ ↦ 0) =
      lossContrast ℓ ν₀ ν₁ := by
    funext x
    simp [dirLoss]
  rw [popLoss_mixMeasure_eq_affLoss hℓ hM hs', ea, ed]

end

end Laplace.Multi
