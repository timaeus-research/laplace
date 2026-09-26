/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AtlasEnergy

/-!
# The Fisher energy of the bridge in the full simplex

For a data law `D = rν` with density `r`, the bridge `D_s = (1−s)ν + sD = (1 + s(r−1))ν` is the
straight path in the full simplex. Its Fisher speed is `k_D(s) = ∫ (r−1)²/(1+s(r−1)) dν`, and
the two
scalar identities

  `∫₀¹ (1−s) (r−1)²/(1+s(r−1)) ds = r log r − r + 1 = klFun r`
                                                          (`integral_one_sub_mul_klKernel`)
  `∫₀¹ s (r−1)²/(1+s(r−1)) ds = r − 1 − log r`                    (`integral_mul_klKernel`)

integrate, for bounded positive densities, to `KL(D‖ν) = ∫₀¹ (1−s) k_D(s) ds`,
`KL(ν‖D) = ∫₀¹ s k_D(s) ds` and `∫₀¹ k_D = KL(D‖ν) + KL(ν‖D)`: the bridge in the full simplex obeys
the same weighted identities as the atlas path (`AtlasEnergy`) and the exponential path
(`PathEnergy`). Three straight paths from the featureless posterior — in the simplex, in response
coordinates, in natural coordinates — each carry an energy density whose two time-weightings are the
two orientations of the divergence between the endpoints.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Scalar

/-- The pointwise Fisher speed of the mixture path at density value `r`. -/
noncomputable def klKernel (r s : ℝ) : ℝ := (r - 1) ^ 2 / (1 + s * (r - 1))

theorem klKernel_denom_pos {r s : ℝ} (hr : 0 < r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < 1 + s * (r - 1) := by
  rcases eq_or_lt_of_le hs1 with rfl | hlt
  · linarith
  · nlinarith [mul_nonneg hs0 hr.le]

theorem continuousOn_klKernel {r : ℝ} (hr : 0 < r) : ContinuousOn (klKernel r) (Icc 0 1) := by
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun s hs ↦
    (klKernel_denom_pos hr hs.1 hs.2).ne'

/-- `∫₀¹ (1−s) (r−1)²/(1+s(r−1)) ds = r log r − r + 1`. -/
theorem integral_one_sub_mul_klKernel {r : ℝ} (hr : 0 < r) :
    ∫ s in (0 : ℝ)..1, (1 - s) * klKernel r s = klFun r := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ r * Real.log (1 + s * (r - 1)) - (r - 1) * s)
      ((1 - s) * klKernel r s) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hq := klKernel_denom_pos hr hs.1 hs.2
    have h1 : HasDerivAt (fun s ↦ 1 + s * (r - 1)) (r - 1) s := by
      simpa using ((hasDerivAt_id' (x := s)).mul_const (r - 1)).const_add 1
    have h2 := (h1.log hq.ne').const_mul r
    have h3 := (hasDerivAt_id' (x := s)).const_mul (r - 1)
    refine (h2.sub h3).congr_deriv ?_
    unfold klKernel
    linear_combination (r - 1) * mul_inv_cancel₀ hq.ne'
  have hint : IntervalIntegrable (fun s ↦ (1 - s) * klKernel r s) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_const.sub continuousOn_id).mul (continuousOn_klKernel hr)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [klFun, one_mul, mul_zero, sub_zero, zero_mul, add_zero, Real.log_one, mul_one]
  have : (1 : ℝ) + (r - 1) = r := by ring
  rw [this]
  ring

/-- `∫₀¹ s (r−1)²/(1+s(r−1)) ds = r − 1 − log r`. -/
theorem integral_mul_klKernel {r : ℝ} (hr : 0 < r) :
    ∫ s in (0 : ℝ)..1, s * klKernel r s = r - 1 - Real.log r := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ (r - 1) * s - Real.log (1 + s * (r - 1)))
      (s * klKernel r s) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hq := klKernel_denom_pos hr hs.1 hs.2
    have h1 : HasDerivAt (fun s ↦ 1 + s * (r - 1)) (r - 1) s := by
      simpa using ((hasDerivAt_id' (x := s)).mul_const (r - 1)).const_add 1
    have h2 := h1.log hq.ne'
    have h3 := (hasDerivAt_id' (x := s)).const_mul (r - 1)
    refine (h3.sub h2).congr_deriv ?_
    unfold klKernel
    linear_combination (-(r - 1)) * mul_inv_cancel₀ hq.ne'
  have hint : IntervalIntegrable (fun s ↦ s * klKernel r s) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_id.mul (continuousOn_klKernel hr)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, Real.log_one, sub_zero]
  have : (1 : ℝ) + (r - 1) = r := by ring
  rw [this]

/-- The unweighted energy: `∫₀¹ (r−1)²/(1+s(r−1)) ds = klFun r + (r − 1 − log r)`. -/
theorem integral_klKernel {r : ℝ} (hr : 0 < r) :
    ∫ s in (0 : ℝ)..1, klKernel r s = klFun r + (r - 1 - Real.log r) := by
  rw [← integral_one_sub_mul_klKernel hr, ← integral_mul_klKernel hr, ←
    intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr fun s _ ↦ ?_
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_const.sub continuousOn_id).mul (continuousOn_klKernel hr)
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_id.mul (continuousOn_klKernel hr)

end Scalar

section Measure

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The law with density `r` with respect to `ν`. -/
noncomputable def densLaw (r : X → ℝ) : Measure X := ν.withDensity fun x ↦ ENNReal.ofReal (r x)

/-- The Fisher speed of the bridge `(1 + s(r−1))ν` at time `s`. -/
noncomputable def mixSpeed (r : X → ℝ) (s : ℝ) : ℝ := ∫ x, klKernel (r x) s ∂ν

variable {r : X → ℝ} (hr : Measurable r) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ r x)
  (hC : ∀ x, r x ≤ C)
include hr hc0 hc hC

omit [MeasurableSpace X] hr in
theorem klKernel_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : X) :
    klKernel (r x) s ≤ (C + 1) ^ 2 / min 1 c := by
  have hrx := hc x
  have hrC := hC x
  have hden : min 1 c ≤ 1 + s * (r x - 1) := by
    rcases le_or_gt 1 (r x) with h1 | h1
    · exact (min_le_left _ _).trans (by nlinarith)
    · exact (min_le_right _ _).trans (by nlinarith)
  have hnum : (r x - 1) ^ 2 ≤ (C + 1) ^ 2 := by
    refine sq_le_sq' (by linarith) (by linarith)
  exact div_le_div₀ (sq_nonneg _) hnum (lt_min one_pos hc0) hden

omit hc0 hc hC in
theorem measurable_klKernel_uncurry :
    Measurable fun p : ℝ × X ↦ klKernel (r p.2) p.1 := by
  unfold klKernel
  exact (((hr.comp measurable_snd).sub measurable_const).pow_const 2).div
    (measurable_const.add (measurable_fst.mul ((hr.comp measurable_snd).sub measurable_const)))

/-- Tonelli for a weight times the mixture kernel: the `s`-integral of the weighted speed is the
`ν`-integral of the pointwise `s`-integral. -/
theorem integral_weight_mul_mixSpeed (w : ℝ → ℝ) (hw : Measurable w)
    (hw0 : ∀ s ∈ Ioc (0 : ℝ) 1, |w s| ≤ 1) :
    ∫ s in (0 : ℝ)..1, w s * mixSpeed ν r s =
      ∫ x, (∫ s in (0 : ℝ)..1, w s * klKernel (r x) s) ∂ν := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  unfold mixSpeed
  have hint : Integrable (Function.uncurry fun s x ↦ w s * klKernel (r x) s)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod ν) := by
    have hmeas : Measurable (Function.uncurry fun s x ↦ w s * klKernel (r x) s) :=
      (hw.comp measurable_fst).mul (measurable_klKernel_uncurry hr)
    refine Integrable.of_bound hmeas.aestronglyMeasurable ((C + 1) ^ 2 / min 1 c) ?_
    have hprod : (volume.restrict (Ioc (0 : ℝ) 1)).prod ν =
        (volume.prod ν).restrict (Ioc 0 1 ×ˢ univ) := by
      rw [← Measure.restrict_univ (μ := ν), Measure.prod_restrict, Measure.restrict_univ]
    rw [hprod, ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)]
    refine Eventually.of_forall fun p hp ↦ ?_
    have hs := hp.1
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    have hk0 : 0 ≤ klKernel (r p.2) p.1 := by
      unfold klKernel
      exact div_nonneg (sq_nonneg _)
        (klKernel_denom_pos (lt_of_lt_of_le hc0 (hc _)) hs.1.le hs.2).le
    calc |w p.1| * |klKernel (r p.2) p.1| ≤ 1 * klKernel (r p.2) p.1 := by
          rw [abs_of_nonneg hk0]
          exact mul_le_mul_of_nonneg_right (hw0 _ hs) hk0
      _ ≤ (C + 1) ^ 2 / min 1 c := by
          rw [one_mul]
          exact klKernel_le hc0 hc hC _ hs.1.le hs.2 _
  have h := integral_integral_swap hint
  have hl : ∫ s in Ioc (0 : ℝ) 1, w s * ∫ x, klKernel (r x) s ∂ν =
      ∫ s in Ioc (0 : ℝ) 1, ∫ x, w s * klKernel (r x) s ∂ν :=
    setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ (integral_const_mul _ _).symm
  rw [hl, h]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [intervalIntegral.integral_of_le zero_le_one]

omit hr hc0 hc in
theorem isFiniteMeasure_densLaw : IsFiniteMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (r x)) := by
  refine isFiniteMeasure_withDensity ?_
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top ?_
  calc ∫⁻ x, ENNReal.ofReal (r x) ∂ν ≤ ∫⁻ _x, ENNReal.ofReal C ∂ν :=
        lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hC x)
    _ = ENNReal.ofReal C := by simp

omit hc0 in
theorem integrable_klFun_comp : Integrable (fun x ↦ klFun (r x)) ν := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := c) (b := C)).exists_bound_of_continuousOn
    continuous_klFun.continuousOn
  exact Integrable.of_bound (measurable_klFun.comp hr).aestronglyMeasurable B
    (Eventually.of_forall fun x ↦ hB _ ⟨hc x, hC x⟩)

theorem integrable_sub_one_sub_log : Integrable (fun x ↦ r x - 1 - Real.log (r x)) ν := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := c) (b := C)).exists_bound_of_continuousOn
    (f := fun y ↦ y - 1 - Real.log y)
    ((continuousOn_id.sub continuousOn_const).sub
      (Real.continuousOn_log.mono fun y hy ↦ (lt_of_lt_of_le hc0 hy.1).ne'))
  exact Integrable.of_bound ((hr.sub measurable_const).sub hr.log).aestronglyMeasurable B
    (Eventually.of_forall fun x ↦ hB _ ⟨hc x, hC x⟩)

/-- `KL(rν ‖ ν) = ∫ klFun (r) dν`. -/
theorem toReal_klDiv_densLaw :
    (klDiv (densLaw ν r) ν).toReal = ∫ x, klFun (r x) ∂ν := by
  have hpos : ∀ x, 0 < r x := fun x ↦ lt_of_lt_of_le hc0 (hc x)
  have hfin := isFiniteMeasure_densLaw ν hC
  have hint := integrable_klFun_comp ν hr hc hC
  unfold densLaw
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous ν _)]
  have hae : (fun x ↦ ENNReal.ofReal
      (klFun ((ν.withDensity fun x ↦ ENNReal.ofReal (r x)).rnDeriv ν x).toReal)) =ᵐ[ν]
      fun x ↦ ENNReal.ofReal (klFun (r x)) := by
    filter_upwards [Measure.rnDeriv_withDensity ν hr.ennreal_ofReal] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpos x).le]
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x ↦ klFun_nonneg (hpos x).le),
    ENNReal.toReal_ofReal (integral_nonneg fun x ↦ klFun_nonneg (hpos x).le)]

/-- `KL(ν ‖ rν) = ∫ (r − 1 − log r) dν`. -/
theorem toReal_klDiv_densLaw_symm :
    (klDiv ν (densLaw ν r)).toReal = ∫ x, (r x - 1 - Real.log (r x)) ∂ν := by
  have hpos : ∀ x, 0 < r x := fun x ↦ lt_of_lt_of_le hc0 (hc x)
  have hfin := isFiniteMeasure_densLaw ν hC
  have hint := integrable_sub_one_sub_log ν hr hc0 hc hC
  unfold densLaw
  have hDν : (ν.withDensity fun x ↦ ENNReal.ofReal (r x)) ≪ ν :=
    withDensity_absolutelyContinuous ν _
  have hνD : ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (r x) := by
    have e := withDensity_inv_same (μ := ν) hr.ennreal_ofReal
      (Eventually.of_forall fun x ↦ by simp [ENNReal.ofReal_eq_zero, hpos x])
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_ne_top)
    conv_lhs => rw [← e]
    exact withDensity_absolutelyContinuous _ _
  have hinv := Measure.inv_rnDeriv hDν
  have hrn := hDν.ae_le (Measure.rnDeriv_withDensity ν hr.ennreal_ofReal)
  rw [klDiv_eq_lintegral_klFun_of_ac hνD]
  have hae : (fun x ↦ ENNReal.ofReal
      (klFun (ν.rnDeriv (ν.withDensity fun x ↦ ENNReal.ofReal (r x)) x).toReal)) =ᵐ[ν.withDensity
        fun x ↦ ENNReal.ofReal (r x)] fun x ↦ ENNReal.ofReal (klFun (r x)⁻¹) := by
    filter_upwards [hinv, hrn] with x hx hx'
    have hx'' : (ν.withDensity fun x ↦ ENNReal.ofReal (r x)).rnDeriv ν x = ENNReal.ofReal (r x) :=
      hx'
    rw [← hx, Pi.inv_apply, hx'', ENNReal.toReal_inv, ENNReal.toReal_ofReal (hpos x).le]
  rw [lintegral_congr_ae hae]
  have hg : Measurable fun x ↦ ENNReal.ofReal (klFun (r x)⁻¹) :=
    (measurable_klFun.comp hr.inv).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul ν hr.ennreal_ofReal hg]
  have hkey : ∀ x, (r x - 1 - Real.log (r x)) = r x * klFun (r x)⁻¹ := fun x ↦ by
    unfold klFun
    rw [Real.log_inv]
    linear_combination (Real.log (r x) + 1) * mul_inv_cancel₀ (hpos x).ne'
  have hnn : ∀ x, 0 ≤ r x - 1 - Real.log (r x) := fun x ↦ by
    linarith [Real.log_le_sub_one_of_pos (hpos x)]
  have he : (fun x ↦ ((fun x ↦ ENNReal.ofReal (r x)) * fun x ↦ ENNReal.ofReal (klFun (r x)⁻¹)) x) =
      fun x ↦ ENNReal.ofReal (r x - 1 - Real.log (r x)) := by
    funext x
    rw [Pi.mul_apply, hkey x, ENNReal.ofReal_mul (hpos x).le]
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn),
    ENNReal.toReal_ofReal (integral_nonneg hnn)]

/-- **`KL(rν ‖ ν) = ∫₀¹ (1−s) k(s) ds`** along the bridge in the full simplex. -/
theorem toReal_klDiv_densLaw_eq_integral_mixSpeed :
    (klDiv (densLaw ν r) ν).toReal = ∫ s in (0 : ℝ)..1, (1 - s) * mixSpeed ν r s := by
  rw [toReal_klDiv_densLaw ν hr hc0 hc hC, integral_weight_mul_mixSpeed ν hr hc0 hc hC
    (fun s ↦ 1 - s) (measurable_const.sub measurable_id) fun s hs ↦ by
      rw [abs_of_nonneg (by linarith [hs.2])]
      linarith [hs.1]]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  exact (integral_one_sub_mul_klKernel (lt_of_lt_of_le hc0 (hc x))).symm

/-- **`KL(ν ‖ rν) = ∫₀¹ s k(s) ds`** along the bridge in the full simplex. -/
theorem toReal_klDiv_symm_densLaw_eq_integral_mixSpeed :
    (klDiv ν (densLaw ν r)).toReal = ∫ s in (0 : ℝ)..1, s * mixSpeed ν r s := by
  rw [toReal_klDiv_densLaw_symm ν hr hc0 hc hC, integral_weight_mul_mixSpeed ν hr hc0 hc hC
    (fun s ↦ s) measurable_id fun s hs ↦ by
      rw [abs_of_nonneg hs.1.le]
      exact hs.2]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  exact (integral_mul_klKernel (lt_of_lt_of_le hc0 (hc x))).symm

/-- **The Fisher energy of the bridge in the full simplex is the symmetrised divergence**. -/
theorem integral_mixSpeed_eq_symm_klDiv :
    ∫ s in (0 : ℝ)..1, mixSpeed ν r s =
      (klDiv (densLaw ν r) ν).toReal + (klDiv ν (densLaw ν r)).toReal := by
  rw [toReal_klDiv_densLaw ν hr hc0 hc hC, toReal_klDiv_densLaw_symm ν hr hc0 hc hC,
    ← integral_add (integrable_klFun_comp ν hr hc hC) (integrable_sub_one_sub_log ν hr hc0 hc hC)]
  have h := integral_weight_mul_mixSpeed ν hr hc0 hc hC (fun _ ↦ 1) measurable_const
    fun s _ ↦ by simp
  simp only [one_mul] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  exact integral_klKernel (lt_of_lt_of_le hc0 (hc x))

end Measure

end Laplace.Multi
