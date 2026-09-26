/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CompactMeanLiftRigidity

/-!
# The exact boundary-ray formula

Let `u` expose a face of the moment body, `⟨u, S⟩ ≤ β` a.e., with charged face fibre
`F = {⟨u, S⟩ = β}`, and let `g = β − ⟨u, S⟩ ≥ 0` be the slack. Along the natural ray `θ − t u`
the family density is `w e^{−t g}/(A + B_t)` with `w = e^{−⟨θ,S⟩}`, `A = ∫_F w`,
`B_t = ∫_{Fᶜ} w e^{−t g}`, and its total-variation distance to the face law `1_F w / A` is
**exactly**

`‖q_{θ − t u} − q_F‖₁ = 2 B_t / (A + B_t)`   (`integral_abs_famDens_ray_sub_faceDens`),

which tends to `0` by dominated convergence (`tendsto_offFaceMass`, `tendsto_tv_ray`). The face
law is the exponential family of the conditioned reference measure (`familyMeasure_faceMeasure_eq`),
so every boundary response in the relative interior of a charged exposed face is reached by an
explicit natural-parameter ray with this exact rate (`exists_ray_tendsto_responseProjection`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Ray

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (θ u : J → ℝ) (β : ℝ)
include hS

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The loss along the natural ray. -/
theorem dirLoss_ray (t : ℝ) (x : X) :
    dirLoss S (θ - t • u) x = dirLoss S θ x - t * dirLoss S u x := by
  simp only [dirLoss, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The weight along the natural ray factorises through the slack `g = β − ⟨u, S⟩`. -/
theorem famWeight_ray (t : ℝ) (x : X) :
    famWeight S (θ - t • u) x =
      Real.exp (t * β) * (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) := by
  unfold famWeight
  rw [dirLoss_ray, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem measurableSet_faceFibre : MeasurableSet {x | dirLoss S u x = β} :=
  measurableSet_eq_fun (bdd_dirLoss hS u).1 measurable_const

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- The face mass `A = ∫_F e^{−⟨θ,S⟩}`. -/
noncomputable def faceMass : ℝ := ∫ x in {x | dirLoss S u x = β}, famWeight S θ x ∂ν

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- The off-face mass `B_t = ∫_{Fᶜ} e^{−⟨θ,S⟩} e^{−t g}`. -/
noncomputable def offFaceMass (t : ℝ) : ℝ :=
  ∫ x in {x | dirLoss S u x = β}ᶜ, famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))) ∂ν

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- The face law's density `1_F e^{−⟨θ,S⟩} / A`. -/
noncomputable def faceDens (x : X) : ℝ :=
  {x | dirLoss S u x = β}.indicator (fun x ↦ famWeight S θ x / faceMass S ν θ u β) x

omit [Nonempty X] [Nonempty J] in
theorem faceMass_pos (hp : 0 < ν.real {x | dirLoss S u x = β}) : 0 < faceMass S ν θ u β := by
  unfold faceMass
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun x ↦ (famWeight_pos θ x).le)
    (integrable_famWeight hS ν θ).integrableOn,
    Function.support_eq_univ (f := fun x ↦ famWeight S θ x) fun x ↦ (famWeight_pos θ x).ne',
    univ_inter]
  exact (ENNReal.toReal_pos_iff.1 hp).1

omit [Nonempty X] [Nonempty J] in
theorem integrable_offFace (t : ℝ) :
    Integrable (fun x ↦ famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ν := by
  have e : (fun x ↦ famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) =
      fun x ↦ (Real.exp (t * β))⁻¹ * famWeight S (θ - t • u) x := by
    funext x
    rw [famWeight_ray, ← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
  rw [e]
  exact (integrable_famWeight hS ν _).const_mul _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem offFaceMass_nonneg (t : ℝ) : 0 ≤ offFaceMass S ν θ u β t :=
  setIntegral_nonneg (measurableSet_faceFibre hS u β).compl fun x _ ↦
    mul_nonneg (famWeight_pos θ x).le (Real.exp_pos _).le

omit [Nonempty X] [Nonempty J] in
/-- The normaliser along the ray: `Z(θ − t u) = e^{tβ} (A + B_t)`. -/
theorem famZ_ray (t : ℝ) :
    famZ S ν (θ - t • u) = Real.exp (t * β) * (faceMass S ν θ u β + offFaceMass S ν θ u β t) := by
  have hF := measurableSet_faceFibre hS u β
  unfold famZ
  simp only [famWeight_ray θ u β t]
  rw [integral_const_mul,
    ← integral_add_compl₀ hF.nullMeasurableSet (integrable_offFace hS ν θ u β t)]
  unfold faceMass offFaceMass
  congr 2
  refine setIntegral_congr_fun hF fun x hx ↦ ?_
  have hx' : dirLoss S u x = β := hx
  rw [hx', sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]

omit [Nonempty X] [Nonempty J] in
/-- The family density along the ray: `p_{θ − t u} = w e^{−t g} / (A + B_t)`. -/
theorem famDens_ray (t : ℝ) (x : X) :
    famDens S ν (θ - t • u) x =
      famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))) /
        (faceMass S ν θ u β + offFaceMass S ν θ u β t) := by
  unfold famDens
  rw [famWeight_ray, famZ_ray hS ν θ u β, mul_div_mul_left _ _ (Real.exp_pos _).ne']

omit [Nonempty X] [Nonempty J] in
theorem integrable_faceDens : Integrable (faceDens S ν θ u β) ν :=
  ((integrable_famWeight hS ν θ).div_const _).indicator (measurableSet_faceFibre hS u β)

omit [Nonempty X] [Nonempty J] in
/-- **The exact boundary-ray formula**: `‖p_{θ − t u} − 1_F w/A‖₁ = 2 B_t / (A + B_t)`. -/
theorem integral_abs_famDens_ray_sub_faceDens (hp : 0 < ν.real {x | dirLoss S u x = β}) (t : ℝ) :
    ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν =
      2 * offFaceMass S ν θ u β t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hB := offFaceMass_nonneg hS ν θ u β t
  have hAB : 0 < faceMass S ν θ u β + offFaceMass S ν θ u β t := by linarith
  have hF := measurableSet_faceFibre hS u β
  have hint : Integrable (fun x ↦ |famDens S ν (θ - t • u) x - faceDens S ν θ u β x|) ν :=
    ((integrable_famDens hS ν _).sub (integrable_faceDens hS ν θ u β)).abs
  rw [← integral_add_compl₀ hF.nullMeasurableSet hint]
  have e1 : ∫ x in {x | dirLoss S u x = β}, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν =
      ∫ x in {x | dirLoss S u x = β}, famWeight S θ x *
        (1 / faceMass S ν θ u β - 1 / (faceMass S ν θ u β + offFaceMass S ν θ u β t)) ∂ν := by
    refine setIntegral_congr_fun hF fun x hx ↦ ?_
    have hx' : dirLoss S u x = β := hx
    rw [famDens_ray hS ν θ u β, faceDens, Set.indicator_of_mem hx, hx', sub_self, mul_zero,
      neg_zero, Real.exp_zero, mul_one, abs_of_nonpos (sub_nonpos.2
        (div_le_div_of_nonneg_left (famWeight_pos θ x).le hA (by linarith)))]
    ring
  have e2 : ∫ x in {x | dirLoss S u x = β}ᶜ,
      |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν =
      ∫ x in {x | dirLoss S u x = β}ᶜ, famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))) /
        (faceMass S ν θ u β + offFaceMass S ν θ u β t) ∂ν := by
    refine setIntegral_congr_fun hF.compl fun x hx ↦ ?_
    rw [famDens_ray hS ν θ u β, faceDens, Set.indicator_of_notMem hx, sub_zero,
      abs_of_nonneg (div_nonneg (mul_nonneg (famWeight_pos θ x).le (Real.exp_pos _).le) hAB.le)]
  rw [e1, e2, integral_mul_const, integral_div]
  change faceMass S ν θ u β * (1 / faceMass S ν θ u β -
    1 / (faceMass S ν θ u β + offFaceMass S ν θ u β t)) +
    offFaceMass S ν θ u β t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) = _
  field_simp
  ring

omit [Nonempty X] [Nonempty J] in
/-- **The off-face mass vanishes along the ray** (dominated convergence). -/
theorem tendsto_offFaceMass (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) :
    Tendsto (offFaceMass S ν θ u β) atTop (𝓝 0) := by
  have hF := measurableSet_faceFibre hS u β
  have hmw : Measurable (famWeight S θ) := Real.measurable_exp.comp (bdd_dirLoss hS θ).1.neg
  have hmg : Measurable fun x ↦ β - dirLoss S u x := (bdd_dirLoss hS u).1.const_sub β
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := ν.restrict {x | dirLoss S u x = β}ᶜ) (l := (atTop : Filter ℝ))
    (F := fun t x ↦ famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))))
    (f := fun _ ↦ (0 : ℝ)) (famWeight S θ)
    (Eventually.of_forall fun t ↦ (hmw.mul ((hmg.const_mul t).neg.exp)).aestronglyMeasurable) ?_
    (integrable_famWeight hS ν θ).integrableOn ?_
  · unfold offFaceMass
    simpa using h
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    filter_upwards [ae_restrict_of_ae hβ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (famWeight_pos θ x).le (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (famWeight_pos θ x).le
      (Real.exp_le_one_iff.2 (by nlinarith [sub_nonneg.2 hx]))
  · rw [ae_restrict_iff' hF.compl]
    filter_upwards [hβ] with x hx hxF
    have hne : dirLoss S u x ≠ β := hxF
    have hg : 0 < β - dirLoss S u x := lt_of_le_of_ne (sub_nonneg.2 hx) fun h ↦ hne (by linarith)
    have hmul : Tendsto (fun t : ℝ ↦ t * (β - dirLoss S u x)) atTop atTop :=
      Tendsto.atTop_mul_const hg tendsto_id
    have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
    simpa [Function.comp_def] using hlim.const_mul (famWeight S θ x)

omit [Nonempty X] [Nonempty J] in
/-- **The natural ray converges to the face law in total variation**, with the exact rate
`2 B_t/(A + B_t)`. -/
theorem tendsto_tv_ray (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    Tendsto (fun t : ℝ ↦ ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν) atTop
      (𝓝 0) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hB := tendsto_offFaceMass hS ν θ u β hβ
  have h := (hB.const_mul 2).div (tendsto_const_nhds.add hB) (by rw [add_zero]; exact hA.ne')
  simp only [mul_zero, add_zero, zero_div] at h
  exact h.congr fun t ↦ (integral_abs_famDens_ray_sub_faceDens hS ν θ u β hp t).symm

omit [Nonempty X] [Nonempty J] in
/-- **The face law is the exponential family of the conditioned reference measure.** -/
theorem familyMeasure_faceMeasure_eq (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        θ =
      ν.withDensity fun x ↦ ENNReal.ofReal (faceDens S ν θ u β x) := by
  have hF := measurableSet_faceFibre hS u β
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  have hA := faceMass_pos hS ν θ u β hp
  have hm : Measurable (affLoss (fun _ ↦ (0 : ℝ)) S θ) := by
    unfold affLoss
    exact measurable_const.add (Finset.measurable_sum _ fun i _ ↦ (hS i).1.const_mul _)
  have haff : ∀ x, Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * (fun _ : X ↦ (1 : ℝ)) x =
      famWeight S θ x := fun x ↦ by
    simp [affLoss, dirLoss, famWeight]
  have hZ : priorZ (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
      (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 =
        (ν.real {x | dirLoss S u x = β})⁻¹ * faceMass S ν θ u β := by
    unfold priorZ faceMass
    rw [integral_faceMeasure]
    congr 1
    exact setIntegral_congr_fun hF fun x _ ↦ haff x
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = priorZ (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
    (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := ⟨_, rfl⟩
  rw [← hZdef] at hZ
  have hdens : Measurable fun x ↦ ENNReal.ofReal
      (Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * (fun _ : X ↦ (1 : ℝ)) x / Z) :=
    (((hm.const_mul 1).neg.exp.mul measurable_const).div_const _).ennreal_ofReal
  unfold familyMeasure
  rw [← hZdef, faceMeasure_eq_withDensity ν hF,
    ← withDensity_mul ν (measurable_const.indicator hF) hdens]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ {x | dirLoss S u x = β}
  · rw [Set.indicator_of_mem hx, faceDens, Set.indicator_of_mem hx, haff, hZ]
    have e : (ν {x | dirLoss S u x = β})⁻¹ = ENNReal.ofReal (ν.real {x | dirLoss S u x = β})⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hp, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top ν _)]
    rw [e, ← ENNReal.ofReal_mul (inv_nonneg.2 hp.le)]
    congr 1
    field_simp
  · rw [Set.indicator_of_notMem hx, faceDens, Set.indicator_of_notMem hx, zero_mul,
      ENNReal.ofReal_zero]

/-- **Every boundary response in the relative interior of a charged exposed face is the
total-variation limit of an explicit natural ray, with the exact rate `2 B_t/(A + B_t)`.** -/
theorem exists_ray_tendsto_responseProjection (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {M : J → ℝ} (hM : dotJ u M = β)
    (hrel : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S)) :
    ∃ θ : J → ℝ,
      responseProjection hS ν M = ν.withDensity (fun x ↦ ENNReal.ofReal (faceDens S ν θ u β x)) ∧
      (∀ t, ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν =
        2 * offFaceMass S ν θ u β t / (faceMass S ν θ u β + offFaceMass S ν θ u β t)) ∧
      Tendsto (fun t : ℝ ↦ ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν) atTop
        (𝓝 0) := by
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  have hfinF := genRate_ne_top_of_mem_intrinsicInterior hS (faceMeasure ν _) hrel
  obtain ⟨θ, hθ⟩ := responseProjection_eq_tilted hS (faceMeasure ν {x | dirLoss S u x = β}) hrel
  refine ⟨θ, ?_, integral_abs_famDens_ray_sub_faceDens hS ν θ u β hp,
    tendsto_tv_ray hS ν θ u β hβ hp⟩
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hπpos : (0 : ℝ) < ∫ x, (fun _ : X ↦ (1 : ℝ)) x ∂faceMeasure ν {x | dirLoss S u x = β} := by
    simp
  have hπi : Integrable (fun _ : X ↦ (1 : ℝ)) (faceMeasure ν {x | dirLoss S u x = β}) :=
    integrable_const _
  have hπ : ∀ x, (0 : ℝ) < (fun _ : X ↦ (1 : ℝ)) x := fun _ ↦ one_pos
  rw [responseProjection_faceMeasure hS ν hβ hp hM hfinF, hθ,
    ← familyMeasure_faceMeasure_eq hS ν θ u β hp,
    familyMeasure_eq_tilted measurable_const hπi hπ hπpos measurable_const h0 hS
      (one_pos : (0 : ℝ) < 1) θ, familyMeasure_one_zero]

end Ray

end Laplace.Multi
