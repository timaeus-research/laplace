/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ExposedFace
import Laplace.Multi.FaceLimit

/-!
# The wall ray converges in total variation to the face law

Along the feature ray `a = s v`, `s → ∞`, with `α` the essential lower bound of `R_v` and the face
`F = {R_v = α}` of positive mass under the featureless member `Q = P_{t,0}`, the member `P_{t,sv}`
converges to the conditional law `Q_F = Q(· | F)` (`faceMeasure`) **in total variation**, with the
exact bound

  `|P_{t,sv}(A) − Q_F(A)| ≤ 1 − P_{t,sv}(F)`   for every measurable `A`
  (`abs_familyMeasure_real_sub_faceLaw_le`),

and `P_{t,sv}(F) → 1` (`tendsto_familyMeasure_real_face`), hence `P_{t,sv}(A) → Q_F(A)` for every
measurable `A` (`tendsto_familyMeasure_real_ray`). The mechanism is exact: on `F` the ray density is
proportional to that of `Q`, so `P_{t,sv}(· ∩ F) = P_{t,sv}(F) · Q_F(·)`
(`familyMeasure_real_inter_face`),
and the remaining mass `1 − P_{t,sv}(F)` sits off the face. This is the probabilistic reading of the
wall: a positive-mass face is a genuine limiting posterior, reached in total variation, at the
information cost `−log Q(F)` (`tendsto_mixKL_zero_face`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit [Nonempty X] ht in
/-- The mass of a measurable set under a member is the expectation of its indicator. -/
theorem familyMeasure_real_eq_priorExp (a : ι → ℝ) {A : Set X} (hA : MeasurableSet A) :
    (familyMeasure μ π L₀ R t a).real A =
      priorExp μ π (affLoss L₀ R a) (A.indicator 1) t := by
  rw [← integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a, integral_indicator_one hA]

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
/-- The ray numerator over a subset of the face is the face-scaled tilted prior mass. -/
theorem ray_numerator_subset_face (v : ι → ℝ) {α : ℝ} {B : Set X} (hB : MeasurableSet B)
    (hBF : ∀ x ∈ B, dirLoss R v x = α) (s : ℝ) :
    ∫ x, B.indicator 1 x * Real.exp (-(t * affLoss L₀ R (s • v) x)) * π x ∂μ =
      Real.exp (-(t * s * α)) * ∫ x in B, tiltedPrior π L₀ t x ∂μ := by
  have e : (fun x ↦ B.indicator 1 x * Real.exp (-(t * affLoss L₀ R (s • v) x)) * π x) =
      B.indicator fun x ↦ Real.exp (-(t * affLoss L₀ R (s • v) x)) * π x := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [e, integral_indicator hB, ← integral_const_mul]
  refine setIntegral_congr_fun hB fun x hx ↦ ?_
  unfold tiltedPrior
  have hv : dirLoss R v x = α := hBF x hx
  have hL : affLoss L₀ R (s • v) x = L₀ x + s * dirLoss R v x := by
    simp only [affLoss, dirLoss, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hL, hv, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

omit [Nonempty X] ht in
/-- **On the face the ray is proportional to the featureless member**:
`P_{t,sv}(A ∩ F) = P_{t,sv}(F) · Q_F(A)`. -/
theorem familyMeasure_real_inter_face (v : ι → ℝ) {α : ℝ} (s : ℝ)
    (hp : 0 < ∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) {A : Set X}
    (hA : MeasurableSet A) :
    (familyMeasure μ π L₀ R t (s • v)).real (A ∩ {x | dirLoss R v x = α}) =
      (familyMeasure μ π L₀ R t (s • v)).real {x | dirLoss R v x = α} *
        ((∫ x in A ∩ {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) /
          ∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) := by
  obtain ⟨hvm, _, _⟩ := bdd_dirLoss hR v
  have hF : MeasurableSet {x | dirLoss R v x = α} := measurableSet_eq_fun hvm measurable_const
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) (s • v)).ne'
  rw [familyMeasure_real_eq_priorExp hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _ (hA.inter hF),
    familyMeasure_real_eq_priorExp hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _ hF]
  unfold priorExp
  rw [ray_numerator_subset_face (μ := μ) (π := π) (L₀ := L₀) (R := R) (t := t) v (hA.inter hF)
    (fun x hx ↦ hx.2) s,
    ray_numerator_subset_face (μ := μ) (π := π) (L₀ := L₀) (R := R) (t := t) v hF
    (fun x hx ↦ hx) s]
  field_simp

omit [Nonempty X] in
/-- **The ray mass of the face tends to one.** -/
theorem tendsto_familyMeasure_real_face (v : ι → ℝ) {α : ℝ}
    (hα : ∀ᵐ x ∂μ, α ≤ dirLoss R v x)
    (hp : 0 < ∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) :
    Tendsto (fun s : ℝ ↦ (familyMeasure μ π L₀ R t (s • v)).real {x | dirLoss R v x = α}) atTop
      (𝓝 1) := by
  obtain ⟨hvm, _, _⟩ := bdd_dirLoss hR v
  have hF : MeasurableSet {x | dirLoss R v x = α} := measurableSet_eq_fun hvm measurable_const
  have h := tendsto_priorExp_ray_face hπm hπi hπ hL₀m hL₀ hR ht v hα hp
    (φ := ({x | dirLoss R v x = α}).indicator 1) (measurable_one.indicator hF) (Mφ := 1)
    (fun x ↦ by rw [Set.indicator_apply]; split_ifs <;> simp)
  have e : (∫ x in {x | dirLoss R v x = α},
      ({x | dirLoss R v x = α}).indicator 1 x * tiltedPrior π L₀ t x ∂μ) /
      ∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ = 1 := by
    rw [setIntegral_congr_fun hF (g := fun x ↦ tiltedPrior π L₀ t x)
      (fun x hx ↦ by rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul]), div_self hp.ne']
  rw [e] at h
  refine h.congr fun s ↦ ?_
  rw [familyMeasure_real_eq_priorExp hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _ hF]

omit ht in
/-- The face law `Q_F = Q(· | F)` in terms of the tilted prior. -/
theorem faceLaw_real_eq (v : ι → ℝ) {α : ℝ}
    (hp : 0 < ∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) {A : Set X}
    (hA : MeasurableSet A) :
    (faceMeasure (familyMeasure μ π L₀ R t 0) {x | dirLoss R v x = α}).real A =
      (∫ x in A ∩ {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) /
        ∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ := by
  obtain ⟨hvm, _, _⟩ := bdd_dirLoss hR v
  have hF : MeasurableSet {x | dirLoss R v x = α} := measurableSet_eq_fun hvm measurable_const
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0).ne'
  have hQF : (familyMeasure μ π L₀ R t 0).real {x | dirLoss R v x = α} =
      (∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) /
        priorZ μ π (affLoss L₀ R 0) t := by
    rw [familyMeasure_real_eq_priorExp hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _ hF]
    unfold priorExp
    have h := ray_numerator_subset_face (μ := μ) (π := π) (L₀ := L₀) (R := R) (t := t) v hF
      (fun x hx ↦ hx) 0
    rw [zero_smul] at h
    rw [h]
    simp
  have hQAF : (familyMeasure μ π L₀ R t 0).real (A ∩ {x | dirLoss R v x = α}) =
      (∫ x in A ∩ {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) /
        priorZ μ π (affLoss L₀ R 0) t := by
    rw [familyMeasure_real_eq_priorExp hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _ (hA.inter hF)]
    unfold priorExp
    have h := ray_numerator_subset_face (μ := μ) (π := π) (L₀ := L₀) (R := R) (t := t) v
      (hA.inter hF) (fun x hx ↦ hx.2) 0
    rw [zero_smul] at h
    rw [h]
    simp
  have hZ' := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  rw [faceMeasure, measureReal_def, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, hQF, hQAF]
  field_simp

/-- **The exact total-variation bound**: `|P_{t,sv}(A) − Q_F(A)| ≤ 1 − P_{t,sv}(F)`. -/
theorem abs_familyMeasure_real_sub_faceLaw_le (v : ι → ℝ) {α : ℝ} (s : ℝ)
    (hp : 0 < ∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) {A : Set X}
    (hA : MeasurableSet A) :
    |(familyMeasure μ π L₀ R t (s • v)).real A -
        (faceMeasure (familyMeasure μ π L₀ R t 0) {x | dirLoss R v x = α}).real A| ≤
      1 - (familyMeasure μ π L₀ R t (s • v)).real {x | dirLoss R v x = α} := by
  obtain ⟨hvm, _, _⟩ := bdd_dirLoss hR v
  have hF : MeasurableSet {x | dirLoss R v x = α} := measurableSet_eq_fun hvm measurable_const
  have hPs := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) (s • v)
  set P := familyMeasure μ π L₀ R t (s • v) with hPdef
  set F := {x | dirLoss R v x = α} with hFdef
  set c := (∫ x in A ∩ F, tiltedPrior π L₀ t x ∂μ) / ∫ x in F, tiltedPrior π L₀ t x ∂μ with hc
  have hsplit : P.real A = P.real (A ∩ F) + P.real (A \ F) :=
    (measureReal_inter_add_sdiff (s := A) hF).symm
  have hinter : P.real (A ∩ F) = P.real F * c :=
    familyMeasure_real_inter_face hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) v s hp hA
  have hlaw := faceLaw_real_eq hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) v hp hA
  rw [← hc] at hlaw
  have htp : ∀ x, 0 ≤ tiltedPrior π L₀ t x := fun x ↦
    (mul_pos (Real.exp_pos _) (hπ x)).le
  have hc0 : 0 ≤ c := div_nonneg (setIntegral_nonneg (hA.inter hF) fun x _ ↦ htp x) hp.le
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one hp]
    exact setIntegral_mono_set (integrable_tiltedPrior hπi hL₀m hL₀ ht).integrableOn
      (ae_of_all _ htp) (ae_of_all _ fun x hx ↦ hx.2)
  have hFc : P.real Fᶜ = 1 - P.real F := by
    rw [measureReal_compl hF]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
  have hdiff : P.real (A \ F) ≤ 1 - P.real F := by
    rw [← hFc]
    exact measureReal_mono fun x hx ↦ hx.2
  have hd0 : 0 ≤ P.real (A \ F) := measureReal_nonneg
  have hF1 : P.real F ≤ 1 := by
    rw [measureReal_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have hprod1 : (1 - P.real F) * c ≤ 1 - P.real F :=
    mul_le_of_le_one_right (by linarith) hc1
  have hprod0 : 0 ≤ (1 - P.real F) * c := mul_nonneg (by linarith) hc0
  rw [hlaw, hsplit, hinter, abs_le]
  constructor <;> nlinarith

/-- **The wall ray converges in total variation to the face law**: `P_{t,sv}(A) → Q_F(A)` for every
measurable `A`. -/
theorem tendsto_familyMeasure_real_ray (v : ι → ℝ) {α : ℝ} (hα : ∀ᵐ x ∂μ, α ≤ dirLoss R v x)
    (hp : 0 < ∫ x in {x | dirLoss R v x = α}, tiltedPrior π L₀ t x ∂μ) {A : Set X}
    (hA : MeasurableSet A) :
    Tendsto (fun s : ℝ ↦ (familyMeasure μ π L₀ R t (s • v)).real A) atTop
      (𝓝 ((faceMeasure (familyMeasure μ π L₀ R t 0) {x | dirLoss R v x = α}).real A)) := by
  have hF := tendsto_familyMeasure_real_face hπm hπi hπ hπpos hL₀m hL₀ hR ht v hα hp
  have h0 : Tendsto (fun s : ℝ ↦ 1 - (familyMeasure μ π L₀ R t (s • v)).real
      {x | dirLoss R v x = α}) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hF
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun s ↦ norm_nonneg _) (fun s ↦ ?_) h0
  rw [Real.norm_eq_abs]
  exact abs_familyMeasure_real_sub_faceLaw_le hπm hπi hπ hπpos hL₀m hL₀ hR ht v s hp hA

end

end Laplace.Multi
