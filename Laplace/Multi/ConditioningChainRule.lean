/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RelativeMomentBody
import Laplace.Multi.EntropyProjection

/-!
# Conditioning on a positive-mass event: chain rules

The measure-theoretic bookkeeping of the completion principle. For a probability law `ν` and a
measurable event `F` of positive mass, with `ν_F = ν(· | F)` (`faceMeasure`):

* the density of `ν_F` is `1_F / ν(F)` (`faceMeasure_rnDeriv`), and `ν_F` is carried by `F`;
* a law `ρ ≪ ν` carried by `F` is dominated by `ν_F` (`absolutelyContinuous_faceMeasure`), and then
  `llr(ρ‖ν) = llr(ρ‖ν_F) − log ν(F)` `ρ`-a.e. (`llr_faceMeasure_ae`), so
  **`KL(ρ ‖ ν) = KL(ρ ‖ ν_F) − log ν(F)`** in `ℝ≥0∞` (`klDiv_eq_klDiv_faceMeasure_add`): the entry
  cost of the event adds to the information;
* a law with the mean on a supporting hyperplane of the features is carried by the corresponding
  face (`compl_eq_zero_of_mean_face`);
* the moment body of `ν_F` lies in the moment body of `ν` and in the face hyperplane
  (`momentBody_faceMeasure_subset`, `momentBody_faceMeasure_subset_hyperplane`), so the affine
  dimension of the moment body **strictly drops** under conditioning on a proper supporting face
  (`finrank_dirSpan_faceMeasure_lt`);
* the featureless member of the family with prior density `1` and base loss `0` is the law itself
  (`familyMeasure_one_zero`), so the general rate is the family rate (`genRate_eq_rateFun`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]

section Conditioning

variable (ν : Measure X) [IsProbabilityMeasure ν] {F : Set X} (hF : MeasurableSet F)
include hF

omit [Fintype J] in
/-- The density of the face law is `1_F / ν(F)`. -/
theorem faceMeasure_rnDeriv :
    (faceMeasure ν F).rnDeriv ν =ᵐ[ν] F.indicator fun _ ↦ (ν F)⁻¹ := by
  rw [faceMeasure_eq_withDensity ν hF]
  exact Measure.rnDeriv_withDensity ν (measurable_const.indicator hF)

omit [Fintype J] [IsProbabilityMeasure ν] in
theorem ae_mem_faceMeasure : ∀ᵐ x ∂faceMeasure ν F, x ∈ F := by
  unfold faceMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem hF) _

omit [Fintype J] in
/-- A law dominated by `ν` and carried by `F` is dominated by the face law. -/
theorem absolutelyContinuous_faceMeasure {ρ : Measure X} (hρν : ρ ≪ ν) (hρF : ρ Fᶜ = 0) :
    ρ ≪ faceMeasure ν F := by
  intro A hA
  unfold faceMeasure at hA
  rw [Measure.smul_apply, Measure.restrict_apply' hF, smul_eq_mul, mul_eq_zero] at hA
  have hAF : ρ (A ∩ F) = 0 := by
    rcases hA with h | h
    · exact absurd (ENNReal.inv_eq_zero.1 h) (measure_ne_top ν F)
    · exact hρν h
  refine le_antisymm ?_ zero_le
  calc ρ A ≤ ρ (A ∩ F) + ρ (A \ F) := measure_le_inter_add_sdiff _ _ _
    _ ≤ 0 + ρ Fᶜ := add_le_add hAF.le (measure_mono fun x hx ↦ hx.2)
    _ = 0 := by rw [hρF, add_zero]

omit [Fintype J] in
/-- **The log-likelihood ratio under conditioning**: `llr(ρ‖ν) = llr(ρ‖ν_F) − log ν(F)` for a law
`ρ` dominated by `ν_F`. -/
theorem llr_faceMeasure_ae (hp : 0 < ν.real F) {ρ : Measure X} [IsProbabilityMeasure ρ]
    (hρ : ρ ≪ faceMeasure ν F) :
    llr ρ ν =ᵐ[ρ] fun x ↦ llr ρ (faceMeasure ν F) x - Real.log (ν.real F) := by
  have hF0 : ν F ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hac : faceMeasure ν F ≪ ν := by
    rw [faceMeasure_eq_withDensity ν hF]
    exact withDensity_absolutelyContinuous _ _
  have hρν : ρ ≪ ν := hρ.trans hac
  have hchain := Measure.rnDeriv_mul_rnDeriv hρ (κ := ν)
  filter_upwards [hρν.ae_le hchain, hρν.ae_le (faceMeasure_rnDeriv ν hF),
    hρ.ae_le (ae_mem_faceMeasure ν hF), Measure.rnDeriv_pos hρ,
    hρ.ae_le (Measure.rnDeriv_lt_top ρ (faceMeasure ν F))] with x hx hxF hxmem hpos hlt
  unfold llr
  rw [← hx, Pi.mul_apply, hxF, Set.indicator_of_mem hxmem, ENNReal.toReal_mul, ENNReal.toReal_inv,
    Real.log_mul (ENNReal.toReal_pos hpos.ne' hlt.ne).ne'
      (inv_ne_zero (ENNReal.toReal_pos hF0 (measure_ne_top _ _)).ne'), Real.log_inv]
  simp only [measureReal_def]
  ring

omit [Fintype J] in
/-- **The information chain rule under conditioning**: `KL(ρ ‖ ν) = KL(ρ ‖ ν_F) + (−log ν(F))` for a
law `ρ` dominated by `ν_F`, in `ℝ≥0∞`. -/
theorem klDiv_eq_klDiv_faceMeasure_add (hp : 0 < ν.real F) (ρ : Measure X)
    [IsProbabilityMeasure ρ] (hρ : ρ ≪ faceMeasure ν F) :
    klDiv ρ ν = klDiv ρ (faceMeasure ν F) + ENNReal.ofReal (-Real.log (ν.real F)) := by
  have hF0 : ν F ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hac : faceMeasure ν F ≪ ν := by
    rw [faceMeasure_eq_withDensity ν hF]
    exact withDensity_absolutelyContinuous _ _
  have hρν : ρ ≪ ν := hρ.trans hac
  have hllr := llr_faceMeasure_ae ν hF hp hρ
  have hlog0 : 0 ≤ -Real.log (ν.real F) := by
    rw [neg_nonneg]
    refine Real.log_nonpos hp.le ?_
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  by_cases hint : Integrable (llr ρ (faceMeasure ν F)) ρ
  · have hint' : Integrable (llr ρ ν) ρ := (hint.sub (integrable_const _)).congr hllr.symm
    rw [klDiv_of_ac_of_integrable hρν hint', klDiv_of_ac_of_integrable hρ hint,
      ← ENNReal.ofReal_add (integral_llr_add_sub_measure_univ_nonneg hρ hint) hlog0,
      integral_congr_ae hllr, integral_sub hint (integrable_const _), integral_const]
    congr 1
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    ring
  · have hint' : ¬ Integrable (llr ρ ν) ρ := fun h ↦
      hint ((h.add (integrable_const _)).congr (by
        filter_upwards [hllr] with x hx
        simp only [Pi.add_apply]
        rw [hx]
        ring))
    rw [klDiv_of_not_integrable hint, klDiv_of_not_integrable hint', top_add]

omit [IsProbabilityMeasure ν] hF in
/-- **A law whose mean lies on a supporting hyperplane is carried by the face.** -/
theorem compl_eq_zero_of_mean_face {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ρ : Measure X)
    [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν) {e : J → ℝ} {β : ℝ}
    (hβ : ∀ᵐ x ∂ν, dirLoss S e x ≤ β) (hM : dotJ e (fun i ↦ ∫ x, S i x ∂ρ) = β) :
    ρ {x | dirLoss S e x = β}ᶜ = 0 := by
  have hβρ : ∀ᵐ x ∂ρ, dirLoss S e x ≤ β := hρν.ae_le hβ
  rw [dotJ_integral_eq ρ hS e] at hM
  have hzero : (fun x ↦ β - dirLoss S e x) =ᵐ[ρ] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_
      (integrable_of_bdd_prob ρ ((Bdd.const β).sub (bdd_dirLoss hS e)))).1 ?_
    · filter_upwards [hβρ] with x hx
      simp only [Pi.zero_apply]
      linarith
    · rw [integral_sub (integrable_const _) (integrable_of_bdd_prob ρ (bdd_dirLoss hS e)), hM,
        integral_const]
      simp
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hzero] with x hx
  simp only [Pi.zero_apply] at hx
  rw [Set.notMem_compl_iff]
  change dirLoss S e x = β
  linarith

set_option linter.unusedFintypeInType false in
/-- The essential range shrinks under conditioning. -/
theorem essRange_faceMeasure_subset {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (hp : 0 < ν.real F) :
    essRange (faceMeasure ν F) (fun _ ↦ (1 : ℝ)) S ⊆ essRange ν (fun _ ↦ (1 : ℝ)) S := by
  have hF0 : ν F ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hac : faceMeasure ν F ≪ ν := by
    rw [faceMeasure_eq_withDensity ν hF]
    exact withDensity_absolutelyContinuous _ _
  intro y hy
  rw [mem_essRange_iff measurable_const (fun _ ↦ one_pos) hS] at hy ⊢
  intro r hr
  by_contra h0
  exact (hy r hr).ne' (hac (le_antisymm (not_lt.1 h0) zero_le))

set_option linter.unusedFintypeInType false in
/-- The moment body shrinks under conditioning. -/
theorem momentBody_faceMeasure_subset {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (hp : 0 < ν.real F) :
    momentBody (faceMeasure ν F) (fun _ ↦ (1 : ℝ)) S ⊆ momentBody ν (fun _ ↦ (1 : ℝ)) S :=
  closure_mono (convexHull_mono (essRange_faceMeasure_subset ν hF hS hp))

/-- The moment body of the face law lies in the face hyperplane. -/
theorem momentBody_faceMeasure_subset_hyperplane {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
    (hp : 0 < ν.real F) {e : J → ℝ} {β : ℝ} (hFdef : F = {x | dirLoss S e x = β}) :
    momentBody (faceMeasure ν F) (fun _ ↦ (1 : ℝ)) S ⊆ {y | dotJ e y = β} := by
  have hF0 : ν F ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hae : ∀ᵐ x ∂faceMeasure ν F, dirLoss S e x = β := by
    filter_upwards [ae_mem_faceMeasure ν hF] with x hx
    rw [hFdef] at hx
    exact hx
  have hle := momentBody_subset_halfspace (μ := faceMeasure ν F) measurable_const
    (fun _ ↦ one_pos) hS (hae.mono fun x hx ↦ hx.le)
  have hge := momentBody_subset_halfspace (μ := faceMeasure ν F) measurable_const
    (fun _ ↦ one_pos) hS (u := -e) (β := -β) (by
      filter_upwards [hae] with x hx
      rw [show -e = (-1 : ℝ) • e by rw [neg_one_smul], dirLoss_smul]
      change (-1 : ℝ) * dirLoss S e x ≤ -β
      rw [hx]
      linarith)
  intro y hy
  have h1 := hle hy
  have h2 := hge hy
  simp only [Set.mem_ofPred_eq, dotJ_neg_left] at h1 h2 ⊢
  linarith

/-- **The affine dimension strictly drops under conditioning on a proper supporting face.** -/
theorem finrank_dirSpan_faceMeasure_lt {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (hp : 0 < ν.real F)
    {e : J → ℝ} {β : ℝ} (hFdef : F = {x | dirLoss S e x = β}) {y₀ y₁ : J → ℝ}
    (hy₀ : y₀ ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S) (hy₁ : y₁ ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S)
    (hne : dotJ e y₀ ≠ dotJ e y₁) :
    Module.finrank ℝ (dirSpan (faceMeasure ν F) (fun _ ↦ (1 : ℝ)) S) <
      Module.finrank ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S) := by
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ (J → ℝ),
      W = LinearMap.ker (IsLinearMap.mk' (dotJ e) (isLinearMap_dotJ e)) := ⟨_, rfl⟩
  have hsub := momentBody_faceMeasure_subset ν hF hS hp
  have hhyp := momentBody_faceMeasure_subset_hyperplane ν hF hS hp hFdef
  have hle1 : dirSpan (faceMeasure ν F) (fun _ ↦ (1 : ℝ)) S ≤ dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
    AffineSubspace.direction_le (affineSpan_mono ℝ hsub)
  have hle2 : dirSpan (faceMeasure ν F) (fun _ ↦ (1 : ℝ)) S ≤ W := by
    unfold dirSpan
    rw [direction_affineSpan, vectorSpan_def]
    refine Submodule.span_le.2 fun v hv ↦ ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_vsub.1 hv
    have h1 : dotJ e y = β := hhyp hy
    have h2 : dotJ e z = β := hhyp hz
    rw [SetLike.mem_coe, hW, LinearMap.mem_ker, IsLinearMap.mk'_apply, vsub_eq_sub,
      (isLinearMap_dotJ e).map_sub, h1, h2, sub_self]
  have hnot : ¬ dirSpan ν (fun _ ↦ (1 : ℝ)) S ≤ W := fun h ↦ by
    have hv : y₀ - y₁ ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := by
      have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hy₀) (mem_affineSpan ℝ hy₁)
      simpa [vsub_eq_sub] using this
    have := h hv
    rw [hW, LinearMap.mem_ker, IsLinearMap.mk'_apply, (isLinearMap_dotJ e).map_sub,
      sub_eq_zero] at this
    exact hne this
  have hlt : dirSpan (faceMeasure ν F) (fun _ ↦ (1 : ℝ)) S < dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
    lt_of_le_of_ne hle1 fun h ↦ hnot (by rw [← h]; exact hle2)
  exact Submodule.finrank_lt_finrank_of_lt hlt

end Conditioning

section Base

variable (ν : Measure X) [IsProbabilityMeasure ν] (S : J → X → ℝ)

/-- With prior density `1` and base loss `0`, the featureless member is the law itself. -/
theorem familyMeasure_one_zero :
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 = ν := by
  unfold familyMeasure
  have hZ : priorZ ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S 0) 1 = 1 := by
    unfold priorZ
    simp [affLoss]
  rw [hZ]
  have : (fun x ↦ ENNReal.ofReal (Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S 0 x)) * 1 / 1)) =
      (1 : X → ℝ≥0∞) := by
    funext x
    simp [affLoss]
  rw [this, withDensity_one]

/-- The general rate of a law is the family rate with prior density `1` and base loss `0`. -/
theorem genRate_eq_rateFun (M : J → ℝ) :
    genRate ν S M = rateFun ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 M := by
  unfold rateFun chernoffScore baseCgf
  rw [familyMeasure_one_zero ν S]
  rfl

end Base

end Laplace.Multi
