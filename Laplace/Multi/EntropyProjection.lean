/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NullFace
import Laplace.Multi.TiltLowerBound

/-!
# The rate as a constrained relative entropy (the I-projection theorem)

Write `Q = P_{t,0}` for the featureless member of the affine family and, for a response `M`,
  `𝓔(M) = inf { KL(ρ ‖ Q) : ρ a probability law on `X` with E_ρ R = M }`   (`entropyProj`),
with `KL = InformationTheory.klDiv` (Mathlib's Kullback–Leibler divergence, valued in `ℝ≥0∞`).

* **Donsker–Varadhan.** For every bounded `f` and every probability law `ρ`,
  `E_ρ f − log E_Q e^f ≤ KL(ρ ‖ Q)` (`integral_sub_log_le_toReal_klDiv`,
  `ofReal_integral_sub_log_le_klDiv`): the difference is `KL(ρ ‖ Q_f)` for the tilt `Q_f`, which is
  nonnegative by Gibbs' inequality. Taking `f = q·R` gives every Chernoff score, hence
  **the rate is a lower bound for the constrained relative entropy**: `𝓘(M) ≤ 𝓔(M)`
  (`genRate_le_klDiv`, `genRate_le_entropyProj`).
* **The family is a Mathlib tilt.** `P_{t,a} = Q.tilted (−t a·R)` (`familyMeasure_eq_tilted`), and
  the family's own information distance is the Kullback–Leibler divergence:
  `KL(P_{t,a} ‖ Q) = famKL a 0` (`klDiv_familyMeasure_zero`; general tilts:
  `klDiv_tilted_eq`).
* **The I-projection theorem.** On the response space the bound is attained by the family
  member: `𝓔(m_t(a)) = 𝓘(m_t(a)) = KL(P_{t,a} ‖ Q)` (`entropyProj_meanMap`), with the exact
  Pythagorean decomposition `KL(ρ ‖ Q) = KL(ρ ‖ P_{t,a}) + KL(P_{t,a} ‖ Q)` for every law `ρ` with
  response `m_t(a)` (`klDiv_eq_add_of_mean`), so the minimiser is unique
  (`klDiv_eq_rateFun_iff`).
* **Positive faces.** The conditioned featureless member `Q_F = Q(· | F)` has
  `KL(Q_F ‖ Q) = −log Q(F)` (`klDiv_faceMeasure`), and at the conditional mean of a positive
  supporting face the projection identity holds with minimiser `Q_F` (`entropyProj_condMean`).

Interior response charts, accessible conditional walls with additive entry costs, and
infinite-rate inaccessible boundary points are all readings of this one constrained relative
entropy.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- **The constrained relative entropy** `𝓔_ν(M) = inf { KL(ρ ‖ ν) : E_ρ R = M }` over probability
laws `ρ` on the sample space. -/
noncomputable def entropyProj (ν : Measure X) (R : ι → X → ℝ) (M : ι → ℝ) : ℝ≥0∞ :=
  ⨅ (ρ : Measure X) (_ : IsProbabilityMeasure ρ) (_ : (fun i ↦ ∫ x, R i x ∂ρ) = M), klDiv ρ ν

section General

variable (ν : Measure X) [IsProbabilityMeasure ν]

omit [Fintype ι] in
/-- Integrability of `e^f` for a bounded `f`. -/
theorem integrable_exp_of_bdd {f : X → ℝ} (hf : Bdd f) :
    Integrable (fun x ↦ Real.exp (f x)) ν := by
  simpa using integrable_exp_mul_of_bdd ν hf 1

omit [Fintype ι] in
/-- **The Donsker–Varadhan inequality** for a bounded `f`: `E_ρ f − log E_ν e^f ≤ KL(ρ ‖ ν)`. -/
theorem integral_sub_log_le_toReal_klDiv (ρ : Measure X) [IsProbabilityMeasure ρ] (hρ : ρ ≪ ν)
    (hint : Integrable (llr ρ ν) ρ) {f : X → ℝ} (hf : Bdd f) :
    ∫ x, f x ∂ρ - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ (klDiv ρ ν).toReal := by
  have hfν := integrable_exp_of_bdd ν hf
  have hfρ : Integrable f ρ := integrable_of_bdd_prob ρ hf
  have hac : ρ ≪ ν.tilted f := hρ.trans (absolutelyContinuous_tilted hfν)
  have hint' : Integrable (llr ρ (ν.tilted f)) ρ := integrable_llr_tilted_right hρ hfρ hint hfν
  have hprob : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have h0 := integral_llr_add_sub_measure_univ_nonneg hac hint'
  rw [integral_llr_tilted_right hρ hfρ hfν hint] at h0
  rw [toReal_klDiv_of_measure_eq hρ (by simp [measure_univ])]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at h0
  linarith

omit [Fintype ι] in
/-- The Donsker–Varadhan inequality in `ℝ≥0∞`, with no finiteness hypothesis. -/
theorem ofReal_integral_sub_log_le_klDiv (ρ : Measure X) [IsProbabilityMeasure ρ] {f : X → ℝ}
    (hf : Bdd f) :
    ENNReal.ofReal (∫ x, f x ∂ρ - Real.log (∫ x, Real.exp (f x) ∂ν)) ≤ klDiv ρ ν := by
  by_cases htop : klDiv ρ ν = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨hρ, hint⟩ := klDiv_ne_top_iff.1 htop
    exact (ENNReal.ofReal_le_iff_le_toReal htop).2
      (integral_sub_log_le_toReal_klDiv ν ρ hρ hint hf)

omit [Fintype ι] in
/-- The log-likelihood ratio of a bounded tilt, almost everywhere for the tilted measure. -/
theorem llr_tilted_ae {f : X → ℝ} (hf : Bdd f) :
    llr (ν.tilted f) ν =ᵐ[ν.tilted f] fun x ↦ f x - Real.log (∫ x, Real.exp (f x) ∂ν) := by
  have hfν := integrable_exp_of_bdd ν hf
  have hself : ν ≪ ν := fun _ h ↦ h
  have h := llr_tilted_left hself hfν hf.1.aemeasurable
  filter_upwards [(tilted_absolutelyContinuous ν f).ae_le h,
    (tilted_absolutelyContinuous ν f).ae_le (llr_self ν)] with x hx hx0
  rw [hx, hx0, Pi.zero_apply, add_zero]

omit [Fintype ι] in
/-- `∫ llr(ν_f ‖ ν) dν_f = E_{ν_f} f − log E_ν e^f`. -/
theorem integral_llr_tilted_eq {f : X → ℝ} (hf : Bdd f) :
    ∫ x, llr (ν.tilted f) ν x ∂ν.tilted f =
      ∫ x, f x ∂ν.tilted f - Real.log (∫ x, Real.exp (f x) ∂ν) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hf)
  rw [integral_congr_ae (llr_tilted_ae ν hf), integral_sub (integrable_of_bdd_prob _ hf)
    (integrable_const _), integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]

omit [Fintype ι] in
/-- Gibbs' inequality for a bounded tilt: `0 ≤ E_{ν_f} f − log E_ν e^f`. -/
theorem integral_sub_log_nonneg {f : X → ℝ} (hf : Bdd f) :
    0 ≤ ∫ x, f x ∂ν.tilted f - Real.log (∫ x, Real.exp (f x) ∂ν) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hf)
  have hint : Integrable (llr (ν.tilted f) ν) (ν.tilted f) :=
    ((integrable_of_bdd_prob _ hf).sub (integrable_const _)).congr (llr_tilted_ae ν hf).symm
  have h := integral_llr_add_sub_measure_univ_nonneg (tilted_absolutelyContinuous ν f) hint
  rw [integral_llr_tilted_eq ν hf] at h
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at h
  linarith

omit [Fintype ι] in
/-- **The Kullback–Leibler divergence of a bounded tilt**:
`KL(ν_f ‖ ν) = E_{ν_f} f − log E_ν e^f`. -/
theorem klDiv_tilted_eq {f : X → ℝ} (hf : Bdd f) :
    klDiv (ν.tilted f) ν =
      ENNReal.ofReal (∫ x, f x ∂ν.tilted f - Real.log (∫ x, Real.exp (f x) ∂ν)) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hf)
  have hint : Integrable (llr (ν.tilted f) ν) (ν.tilted f) :=
    ((integrable_of_bdd_prob _ hf).sub (integrable_const _)).congr (llr_tilted_ae ν hf).symm
  rw [klDiv_of_ac_of_integrable (tilted_absolutelyContinuous ν f) hint, integral_llr_tilted_eq ν hf]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right]

variable {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hR

/-- **The rate is a lower bound for the constrained relative entropy**: `𝓘_ν(M) ≤ KL(ρ ‖ ν)` for
every probability law `ρ` with `E_ρ R = M`. -/
theorem genRate_le_klDiv (ρ : Measure X) [IsProbabilityMeasure ρ] {M : ι → ℝ}
    (hM : (fun i ↦ ∫ x, R i x ∂ρ) = M) : genRate ν R M ≤ klDiv ρ ν := by
  unfold genRate featCgf
  refine iSup_le fun q ↦ ?_
  have := ofReal_integral_sub_log_le_klDiv ν ρ (bdd_dirLoss hR q)
  rwa [← dotJ_integral_eq ρ hR q, hM] at this

theorem genRate_le_entropyProj (M : ι → ℝ) : genRate ν R M ≤ entropyProj ν R M := by
  refine le_iInf fun ρ ↦ le_iInf fun hρ ↦ le_iInf fun hM ↦ ?_
  exact genRate_le_klDiv ν hR ρ hM

omit hR [Fintype ι] [IsProbabilityMeasure ν] in
theorem entropyProj_le_klDiv (ρ : Measure X) [IsProbabilityMeasure ρ] {M : ι → ℝ}
    (hM : (fun i ↦ ∫ x, R i x ∂ρ) = M) : entropyProj ν R M ≤ klDiv ρ ν :=
  iInf_le_of_le ρ (iInf_le_of_le inferInstance (iInf_le _ hM))

omit hR [IsProbabilityMeasure ν] in
/-- The face law as a density of the base law. -/
theorem faceMeasure_eq_withDensity {F : Set X} (hF : MeasurableSet F) :
    faceMeasure ν F = ν.withDensity (F.indicator fun _ ↦ (ν F)⁻¹) := by
  rw [faceMeasure, withDensity_indicator hF, withDensity_const]

omit hR in
/-- **The entry cost of a face is its Kullback–Leibler divergence**: `KL(ν_F ‖ ν) = −log ν(F)`. -/
theorem klDiv_faceMeasure {F : Set X} (hF : MeasurableSet F) (hp : 0 < ν.real F) :
    klDiv (faceMeasure ν F) ν = ENNReal.ofReal (-Real.log (ν.real F)) := by
  have hF0 : ν F ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hac : faceMeasure ν F ≪ ν := by
    rw [faceMeasure_eq_withDensity ν hF]
    exact withDensity_absolutelyContinuous _ _
  have hmeas : Measurable (F.indicator fun _ : X ↦ (ν F)⁻¹) := measurable_const.indicator hF
  have hrn : (faceMeasure ν F).rnDeriv ν =ᵐ[ν] F.indicator fun _ ↦ (ν F)⁻¹ := by
    rw [faceMeasure_eq_withDensity ν hF]
    exact Measure.rnDeriv_withDensity ν hmeas
  have hmemF : ∀ᵐ x ∂faceMeasure ν F, x ∈ F := by
    unfold faceMeasure
    exact Measure.ae_smul_measure (ae_restrict_mem hF) _
  have hllr : llr (faceMeasure ν F) ν =ᵐ[faceMeasure ν F] fun _ ↦ -Real.log (ν F).toReal := by
    filter_upwards [hac.ae_le hrn, hmemF] with x hx hxF
    change Real.log ((faceMeasure ν F).rnDeriv ν x).toReal = _
    rw [hx, Set.indicator_of_mem hxF, ENNReal.toReal_inv, Real.log_inv]
  have hint : Integrable (llr (faceMeasure ν F) ν) (faceMeasure ν F) :=
    (integrable_const _).congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul,
    add_sub_cancel_right]

/-- **At the conditional mean of a positive face the projection identity holds**, with the
conditioned law as minimiser. -/
theorem entropyProj_condMean {u : ι → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss R u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss R u x = β}) :
    entropyProj ν R (fun i ↦ ∫ x, R i x ∂faceMeasure ν {x | dirLoss R u x = β}) =
        klDiv (faceMeasure ν {x | dirLoss R u x = β}) ν ∧
      klDiv (faceMeasure ν {x | dirLoss R u x = β}) ν =
        genRate ν R (fun i ↦ ∫ x, R i x ∂faceMeasure ν {x | dirLoss R u x = β}) := by
  have hF0 : ν {x | dirLoss R u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  have hF : MeasurableSet {x | dirLoss R u x = β} :=
    measurableSet_eq_fun (bdd_dirLoss hR u).1 measurable_const
  have hkl := klDiv_faceMeasure ν hF hp
  have hrate := genRate_condMean ν hR hβ hp
  refine ⟨le_antisymm (entropyProj_le_klDiv ν _ rfl) ?_, by rw [hkl, hrate]⟩
  rw [hkl, ← hrate]
  exact genRate_le_entropyProj ν hR _

end General

section Family

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- `E_Q e^{−t a·R} = exp(A_t(a) − A_t(0))`. -/
theorem integral_exp_neg_mul_dirLoss_familyMeasure_zero (a : ι → ℝ) :
    ∫ y, Real.exp (-t * dirLoss R a y) ∂familyMeasure μ π L₀ R t 0 =
      Real.exp (affLogZ μ π L₀ R t a - affLogZ μ π L₀ R t 0) := by
  have hQ := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hc := featCgf_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR ht.ne' 0 ((-t) • a)
  have e1 : (0 : ι → ℝ) - t⁻¹ • ((-t) • a) = a := by
    rw [smul_smul, mul_neg, inv_mul_cancel₀ ht.ne', neg_one_smul, zero_sub, neg_neg]
  rw [e1] at hc
  unfold featCgf at hc
  rw [dirLoss_smul] at hc
  have hpos : 0 < ∫ y, Real.exp (-t * dirLoss R a y) ∂familyMeasure μ π L₀ R t 0 :=
    integral_exp_pos (integrable_exp_mul_of_bdd _ (bdd_dirLoss hR a) (-t))
  rw [← hc, Real.exp_log hpos]

/-- **The family member is a Mathlib exponential tilt of the featureless member**:
`P_{t,a} = Q.tilted (−t a·R)`. -/
theorem familyMeasure_eq_tilted (a : ι → ℝ) :
    familyMeasure μ π L₀ R t a =
      (familyMeasure μ π L₀ R t 0).tilted (fun x ↦ -t * dirLoss R a x) := by
  have h := familyMeasure_eq_withDensity_tilt hπm hπi hπ hπpos hL₀m hL₀ hR ht a a t
  rw [div_self ht.ne', one_smul, sub_self] at h
  rw [h]
  unfold Measure.tilted
  congr 1
  funext x
  beta_reduce
  congr 1
  rw [integral_exp_neg_mul_dirLoss_familyMeasure_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht a,
    famCgf_smul, div_self ht.ne', one_smul, sub_self, ← Real.exp_sub]
  congr 1
  ring

/-- **The family's information distance is the Kullback–Leibler divergence**:
`KL(P_{t,a} ‖ P_{t,0}) = famKL a 0`. -/
theorem klDiv_familyMeasure_zero (a : ι → ℝ) :
    klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R t 0) =
      ENNReal.ofReal (famKL μ π L₀ R t a 0) := by
  have hQ := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hP := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have hbdd : Bdd fun x ↦ -t * dirLoss R a x := Bdd.const_mul (-t) (bdd_dirLoss hR a)
  rw [familyMeasure_eq_tilted hπm hπi hπ hπpos hL₀m hL₀ hR ht a, klDiv_tilted_eq _ hbdd,
    ← familyMeasure_eq_tilted hπm hπi hπ hπpos hL₀m hL₀ hR ht a,
    integral_exp_neg_mul_dirLoss_familyMeasure_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht a,
    Real.log_exp, integral_const_mul, ← dotJ_integral_eq _ hR a,
    famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a 0]
  have hm : (fun i ↦ ∫ x, R i x ∂familyMeasure μ π L₀ R t a) = meanMap μ π L₀ R t a :=
    funext fun i ↦ integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR a (R i)
  rw [hm]
  congr 1
  simp only [dotJ, Pi.zero_apply, zero_sub, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **The I-projection theorem**: on the response space the constrained relative entropy is the
rate, attained by the family member. -/
theorem entropyProj_meanMap (a : ι → ℝ) :
    entropyProj (familyMeasure μ π L₀ R t 0) R (meanMap μ π L₀ R t a) =
      rateFun μ π L₀ R t (meanMap μ π L₀ R t a) := by
  have hQ := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hP := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  refine le_antisymm ?_ (genRate_le_entropyProj _ hR _)
  rw [rateFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht a,
    ← klDiv_familyMeasure_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht a]
  exact entropyProj_le_klDiv _ (familyMeasure μ π L₀ R t a)
    (funext fun i ↦ integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR a (R i))

/-- **Pythagoras for the I-projection**: for every probability law `ρ` with response `m_t(a)`,
`KL(ρ ‖ Q) = KL(ρ ‖ P_{t,a}) + KL(P_{t,a} ‖ Q)`. -/
theorem klDiv_eq_add_of_mean (a : ι → ℝ) (ρ : Measure X) [IsProbabilityMeasure ρ]
    (hM : (fun i ↦ ∫ x, R i x ∂ρ) = meanMap μ π L₀ R t a) :
    klDiv ρ (familyMeasure μ π L₀ R t 0) =
      klDiv ρ (familyMeasure μ π L₀ R t a) +
        klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R t 0) := by
  have hQ := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hP := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  obtain ⟨f, hf⟩ : ∃ f : X → ℝ, f = fun x ↦ -t * dirLoss R a x := ⟨_, rfl⟩
  have hbdd : Bdd f := hf ▸ Bdd.const_mul (-t) (bdd_dirLoss hR a)
  have hPt : familyMeasure μ π L₀ R t a = (familyMeasure μ π L₀ R t 0).tilted f := by
    rw [hf]
    exact familyMeasure_eq_tilted hπm hπi hπ hπpos hL₀m hL₀ hR ht a
  have hfν := integrable_exp_of_bdd (familyMeasure μ π L₀ R t 0) hbdd
  have hmeanρ : ∫ x, f x ∂ρ = -t * dotJ a (meanMap μ π L₀ R t a) := by
    rw [hf, integral_const_mul, ← dotJ_integral_eq ρ hR a, hM]
  have hmeanP : ∫ x, f x ∂familyMeasure μ π L₀ R t a = -t * dotJ a (meanMap μ π L₀ R t a) := by
    rw [hf, integral_const_mul, ← dotJ_integral_eq _ hR a]
    congr 2
    exact funext fun i ↦ integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR a (R i)
  rw [hPt] at hmeanP ⊢
  by_cases hac : ρ ≪ familyMeasure μ π L₀ R t 0
  · by_cases hint : Integrable (llr ρ (familyMeasure μ π L₀ R t 0)) ρ
    · have hac' : ρ ≪ (familyMeasure μ π L₀ R t 0).tilted f :=
        hac.trans (absolutelyContinuous_tilted hfν)
      have hint' := integrable_llr_tilted_right hac (integrable_of_bdd_prob ρ hbdd) hint hfν
      have hprob : IsProbabilityMeasure ((familyMeasure μ π L₀ R t 0).tilted f) :=
        isProbabilityMeasure_tilted hfν
      rw [klDiv_of_ac_of_integrable hac hint, klDiv_of_ac_of_integrable hac' hint',
        klDiv_tilted_eq _ hbdd, ← ENNReal.ofReal_add
          (integral_llr_add_sub_measure_univ_nonneg hac' hint') (integral_sub_log_nonneg _ hbdd),
        integral_llr_tilted_right hac (integrable_of_bdd_prob ρ hbdd) hfν hint]
      congr 1
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
      rw [hmeanρ, hmeanP]
      ring
    · have hint' : ¬ Integrable (llr ρ ((familyMeasure μ π L₀ R t 0).tilted f)) ρ := fun h ↦
        hint (((h.add (integrable_of_bdd_prob ρ hbdd)).sub (integrable_const _)).congr (by
          filter_upwards [llr_tilted_right hac hfν] with x hx
          simp only [Pi.sub_apply, Pi.add_apply]
          rw [hx]
          ring))
      rw [klDiv_of_not_integrable hint, klDiv_of_not_integrable hint', top_add]
  · have hac' : ¬ ρ ≪ (familyMeasure μ π L₀ R t 0).tilted f := fun h ↦
      hac (h.trans (tilted_absolutelyContinuous _ f))
    rw [klDiv_of_not_ac hac, klDiv_of_not_ac hac', top_add]

/-- **Uniqueness of the I-projection**: a law with response `m_t(a)` attains the rate iff it is the
family member. -/
theorem klDiv_eq_rateFun_iff (a : ι → ℝ) (ρ : Measure X) [IsProbabilityMeasure ρ]
    (hM : (fun i ↦ ∫ x, R i x ∂ρ) = meanMap μ π L₀ R t a) :
    klDiv ρ (familyMeasure μ π L₀ R t 0) = rateFun μ π L₀ R t (meanMap μ π L₀ R t a) ↔
      ρ = familyMeasure μ π L₀ R t a := by
  have hQ := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hP := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have hfin : klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R t 0) ≠ ⊤ := by
    rw [klDiv_familyMeasure_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht a]
    exact ENNReal.ofReal_ne_top
  rw [rateFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht a,
    ← klDiv_familyMeasure_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht a,
    klDiv_eq_add_of_mean hπm hπi hπ hπpos hL₀m hL₀ hR ht a ρ hM, ← klDiv_eq_zero_iff]
  nth_rewrite 2 [← zero_add (klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R t 0))]
  exact ENNReal.add_left_inj hfin

end Family

end Laplace.Multi
