/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolyhedralCompletion

/-!
# Polyhedral completion VI: the deformation retraction of `L¹` probability densities

On a charged polytope, the response map `R f = [dq_{E_f S}/dν]` is a continuous, mean-preserving,
idempotent retraction of the set of **all** probability densities in `L¹(ν)` onto the completed
family (`continuousOn_retractL1`, `meanL1_retractL1`, `retractL1_eq_self_iff`), and
`H_t f = (1 − t) f + t R f` is a strong deformation retraction, fibrewise mean-preserving
(`continuousOn_deformationL1`, `meanL1_deformationL1`, `retractL1_deformationL1`). No
bounded-density or finite-entropy restriction on the ambient law is needed: only its mean enters.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Ambient

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- The probability densities in `L¹(ν)`. -/
def probL1 : Set (X →₁[ν] ℝ) := {f | 0 ≤ᵐ[ν] ⇑f ∧ ∫ x, f x ∂ν = 1}

variable {ν}

/-- Convex combinations of `L¹` functions, pointwise a.e. -/
theorem coeFn_combo_ae (f g : X →₁[ν] ℝ) (t : ℝ) :
    ⇑((1 - t) • f + t • g) =ᵐ[ν] fun x ↦ (1 - t) * f x + t * g x := by
  filter_upwards [Lp.coeFn_add ((1 - t) • f) (t • g), Lp.coeFn_smul (1 - t) f,
    Lp.coeFn_smul t g] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

/-- The probability densities form a convex set. -/
theorem combo_mem_probL1 {f g : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) (hg : g ∈ probL1 ν) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) • f + t • g ∈ probL1 ν := by
  refine ⟨?_, ?_⟩
  · filter_upwards [coeFn_combo_ae f g t, hf.1, hg.1] with x h hfx hgx
    rw [Pi.zero_apply] at hfx hgx ⊢
    rw [h]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) hfx, mul_nonneg ht0 hgx]
  · rw [integral_congr_ae (coeFn_combo_ae f g t),
      integral_add ((L1.integrable_coeFn f).const_mul _) ((L1.integrable_coeFn g).const_mul _),
      integral_const_mul, integral_const_mul, hf.2, hg.2]
    ring

end Ambient

section Mean

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem meanL1_apply (f : X →₁[ν] ℝ) (j : J) : meanL1 hS ν f j = ∫ x, S j x * f x ∂ν := by
  unfold meanL1
  rw [obsL1_apply]

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem meanL1_add (f g : X →₁[ν] ℝ) : meanL1 hS ν (f + g) = meanL1 hS ν f + meanL1 hS ν g := by
  funext j
  simp [meanL1, map_add]

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem meanL1_smul (c : ℝ) (f : X →₁[ν] ℝ) : meanL1 hS ν (c • f) = c • meanL1 hS ν f := by
  funext j
  simp [meanL1, map_smul]

/-- The response projections are probability densities. -/
theorem projL1_mem_probL1 {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) : projL1 hS ν M ∈ probL1 ν := by
  refine ⟨?_, ?_⟩
  · filter_upwards [(integrable_projDens hS ν M).coeFn_toL1] with x hx
    rw [Pi.zero_apply]
    change 0 ≤ ((integrable_projDens hS ν M).toL1 _) x
    rw [hx]
    exact projDens_nonneg hS ν M x
  · change ∫ x, ((integrable_projDens hS ν M).toL1 _) x ∂ν = 1
    rw [integral_congr_ae (integrable_projDens hS ν M).coeFn_toL1]
    exact integral_eq_one_of_isProbabilityMeasure_withDensity ν (projDens_nonneg hS ν M)
      (integrable_projDens hS ν M) (isProbabilityMeasure_withDensity_projDens hS ν hfin)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- The essential range is monotone under absolute continuity. -/
theorem essRange_subset_of_absolutelyContinuous {D : Measure X} (hD : D ≪ ν) :
    essRange D (fun _ ↦ (1 : ℝ)) S ⊆ essRange ν (fun _ ↦ (1 : ℝ)) S := by
  intro y hy
  rw [mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS] at hy ⊢
  intro r hr
  have := hy r hr
  rw [pos_iff_ne_zero] at this ⊢
  exact fun h ↦ this (hD h)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
theorem momentBody_subset_of_absolutelyContinuous {D : Measure X} (hD : D ≪ ν) :
    momentBody D (fun _ ↦ (1 : ℝ)) S ⊆ momentBody ν (fun _ ↦ (1 : ℝ)) S :=
  closure_mono (convexHull_mono (essRange_subset_of_absolutelyContinuous hS ν hD))

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- **The mean of any probability density lies in the moment body.** -/
theorem meanL1_mem_momentBody {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    meanL1 hS ν f ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
  have hfi := L1.integrable_coeFn f
  have hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (f x)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfi hf.1, hf.2, ENNReal.ofReal_one]
  have hmean : (fun i ↦ ∫ x, S i x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (f x))) =
      meanL1 hS ν f := by
    funext j
    rw [meanL1_apply hS ν, integral_withDensity_eq_integral_toReal_smul₀
      (Lp.aestronglyMeasurable f).aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hf.1] with x hx
    rw [Pi.zero_apply] at hx
    rw [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]
  rw [← hmean]
  exact momentBody_subset_of_absolutelyContinuous hS ν (withDensity_absolutelyContinuous _ _)
    (mean_mem_momentBody_general hS _)

end Mean

section Retraction

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (hV : ∀ v ∈ V, 0 < ν.real (statFibre S v))
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
include hS

/-- **The retraction** `f ↦ [dq_{E_f S}/dν]` of `L¹` probability densities onto the completed
family. -/
noncomputable def retractL1 (f : X →₁[ν] ℝ) : X →₁[ν] ℝ := projL1 hS ν (meanL1 hS ν f)

include hpoly

omit [Nonempty J] [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
theorem meanL1_mem_polytope {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    meanL1 hS ν f ∈ convexHull ℝ (V : Set (J → ℝ)) :=
  hpoly ▸ meanL1_mem_momentBody hS ν hf

include hV

omit [Nonempty J] in
theorem genRate_meanL1_ne_top {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    genRate ν S (meanL1 hS ν f) ≠ ⊤ :=
  genRate_ne_top_of_mem_convexHull_vertices hS ν V hV (meanL1_mem_polytope hS ν V hpoly hf)

omit hV in
theorem retractL1_mem_completedFamilyL1 {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    retractL1 hS ν f ∈ completedFamilyL1 hS ν V :=
  ⟨_, meanL1_mem_polytope hS ν V hpoly hf, rfl⟩

/-- **The retraction preserves the mean.** -/
theorem meanL1_retractL1 {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    meanL1 hS ν (retractL1 hS ν f) = meanL1 hS ν f :=
  meanL1_projL1 hS ν (genRate_meanL1_ne_top hS ν V hV hpoly hf)

omit hpoly in
theorem completedFamilyL1_subset_probL1 : completedFamilyL1 hS ν V ⊆ probL1 ν := by
  rintro _ ⟨M, hM, rfl⟩
  exact projL1_mem_probL1 hS ν (genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM)

omit hpoly in
theorem retractL1_of_mem_completedFamilyL1 {f : X →₁[ν] ℝ} (hf : f ∈ completedFamilyL1 hS ν V) :
    retractL1 hS ν f = f :=
  projL1_meanL1_of_mem hS ν V hV hf

theorem retractL1_idempotent {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    retractL1 hS ν (retractL1 hS ν f) = retractL1 hS ν f :=
  retractL1_of_mem_completedFamilyL1 hS ν V hV (retractL1_mem_completedFamilyL1 hS ν V hpoly hf)

/-- **The completed family is exactly the fixed-point set of the retraction.** -/
theorem retractL1_eq_self_iff {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    retractL1 hS ν f = f ↔ f ∈ completedFamilyL1 hS ν V :=
  ⟨fun h ↦ h ▸ retractL1_mem_completedFamilyL1 hS ν V hpoly hf,
    retractL1_of_mem_completedFamilyL1 hS ν V hV⟩

/-- **The retraction is continuous on the probability densities.** -/
theorem continuousOn_retractL1 [Nonempty V] : ContinuousOn (retractL1 hS ν) (probL1 ν) :=
  (continuousOn_projL1_polytope hS ν V hV).comp (continuous_meanL1 hS ν).continuousOn
    fun _ hf ↦ meanL1_mem_polytope hS ν V hpoly hf

omit hV hpoly in
/-- The straight-line deformation `H_t f = (1 − t) f + t R f`. -/
noncomputable def deformationL1 (t : ℝ) (f : X →₁[ν] ℝ) : X →₁[ν] ℝ :=
  (1 - t) • f + t • retractL1 hS ν f

omit hV hpoly in
theorem deformationL1_zero (f : X →₁[ν] ℝ) : deformationL1 hS ν 0 f = f := by
  simp [deformationL1]

omit hV hpoly in
theorem deformationL1_one (f : X →₁[ν] ℝ) : deformationL1 hS ν 1 f = retractL1 hS ν f := by
  simp [deformationL1]

theorem deformationL1_mem_probL1 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {f : X →₁[ν] ℝ}
    (hf : f ∈ probL1 ν) : deformationL1 hS ν t f ∈ probL1 ν :=
  combo_mem_probL1 hf (completedFamilyL1_subset_probL1 hS ν V hV
    (retractL1_mem_completedFamilyL1 hS ν V hpoly hf)) ht0 ht1

/-- **The deformation preserves the mean at every time.** -/
theorem meanL1_deformationL1 (t : ℝ) {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    meanL1 hS ν (deformationL1 hS ν t f) = meanL1 hS ν f := by
  unfold deformationL1
  rw [meanL1_add, meanL1_smul, meanL1_smul, meanL1_retractL1 hS ν V hV hpoly hf, ← add_smul]
  simp

/-- **The retraction is constant along the deformation**: `R ∘ H_t = R`. -/
theorem retractL1_deformationL1 (t : ℝ) {f : X →₁[ν] ℝ} (hf : f ∈ probL1 ν) :
    retractL1 hS ν (deformationL1 hS ν t f) = retractL1 hS ν f := by
  unfold retractL1
  rw [meanL1_deformationL1 hS ν V hV hpoly t hf]

omit hpoly in
/-- The deformation fixes the completed family pointwise. -/
theorem deformationL1_of_mem_completedFamilyL1 (t : ℝ) {f : X →₁[ν] ℝ}
    (hf : f ∈ completedFamilyL1 hS ν V) : deformationL1 hS ν t f = f := by
  unfold deformationL1
  rw [retractL1_of_mem_completedFamilyL1 hS ν V hV hf, ← add_smul]
  simp

/-- **The deformation is continuous** on `[0, 1] × (probability densities)` (indeed on
`ℝ × (probability densities)`). -/
theorem continuousOn_deformationL1 [Nonempty V] :
    ContinuousOn (fun z : ℝ × (X →₁[ν] ℝ) ↦ deformationL1 hS ν z.1 z.2) (univ ×ˢ probL1 ν) := by
  have hr : ContinuousOn (fun z : ℝ × (X →₁[ν] ℝ) ↦ retractL1 hS ν z.2) (univ ×ˢ probL1 ν) :=
    (continuousOn_retractL1 hS ν V hV hpoly).comp continuousOn_snd fun z hz ↦ hz.2
  exact ((continuousOn_const.sub continuousOn_fst).smul continuousOn_snd).add
    (continuousOn_fst.smul hr)

end Retraction

end Laplace.Multi
