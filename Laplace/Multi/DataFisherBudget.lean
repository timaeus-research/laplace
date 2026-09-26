/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DualFisherMetric

/-!
# The data-side Fisher budget along the mixture bridge

The visible information along the straight path is the weighted dual-Fisher energy
(`StraightPathAtlas`). The total information of a data law `D ≪ ν` has the same shape along the
mixture bridge `D_s = (1 − s) ν + s D`: with `f = dD/dν` and `f_s = 1 − s + s f` the density of
`D_s`, the data Fisher information of the mixture path is
`𝓕_data(s) = ∫ (f − 1)² / f_s dν` (`dataFisher`), and

  `KL(D ‖ ν) = ∫₀¹ (1 − s) 𝓕_data(s) ds`   (`klDiv_eq_lintegral_dataFisher`),

as an identity in `ℝ≥0∞`, infinite values included. It rests on the scalar identity
`x log x − x + 1 = ∫₀¹ (1 − s)(x − 1)² / (1 − s + s x) ds` for `x ≥ 0` (`klFun_eq_integral`) and
Tonelli. Together with the visible budget it identifies the invisible information `KL(D ‖ Π(M))`
with `∫₀¹ (1 − s) [𝓕_data(s) − ⟨Δ, C_{θ_s}⁻¹ Δ⟩] ds`; the bracket is not pointwise nonnegative in
general, since the two Fisher quantities are computed under different laws.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Scalar

/-- **The Kullback–Leibler integrand as a Fisher integral**:
`x log x − x + 1 = ∫₀¹ (1 − s)(x − 1)² / (1 − s + s x) ds` for `x ≥ 0`. -/
theorem klFun_eq_integral {x : ℝ} (hx : 0 ≤ x) :
    klFun x = ∫ s in (0 : ℝ)..1, (1 - s) * (x - 1) ^ 2 / (1 - s + s * x) := by
  rcases hx.eq_or_lt with h0 | hpos
  · -- `x = 0`: the integrand is `1` off the endpoint
    subst h0
    have h1 : ∫ s in (0 : ℝ)..1, (1 - s) * (0 - 1) ^ 2 / (1 - s + s * 0) =
        ∫ _ in (0 : ℝ)..1, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae' ?_ ?_
      · have hne : ∀ᵐ s : ℝ ∂volume, s ≠ 1 := by
          rw [ae_iff]
          simp only [not_not]
          exact Real.volume_singleton
        filter_upwards [hne] with s hs _
        have h1s : (1 : ℝ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
        rw [show (1 : ℝ) - s + s * 0 = 1 - s by ring, zero_sub, neg_one_sq, mul_one, div_self h1s]
      · filter_upwards with s hs
        simp only [Set.mem_Ioc] at hs
        linarith [hs.1, hs.2]
    rw [h1, intervalIntegral.integral_const, klFun_zero]
    simp
  · -- `x > 0`: the antiderivative `−(x − 1) s + x log (1 + (x − 1) s)`
    have hden : ∀ s ∈ Icc (0 : ℝ) 1, 0 < 1 + (x - 1) * s := by
      intro s hs
      have e : 1 + (x - 1) * s = (1 - s) + x * s := by ring
      rw [e]
      have h1 : 0 ≤ x * s := mul_nonneg hpos.le hs.1
      rcases lt_or_eq_of_le hs.2 with h | h
      · linarith
      · rw [h]
        linarith
    have hF : ∀ s ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun s ↦ -(x - 1) * s + x * Real.log (1 + (x - 1) * s))
          ((1 - s) * (x - 1) ^ 2 / (1 - s + s * x)) s := by
      intro s hs
      have hlog : HasDerivAt (fun s ↦ Real.log (1 + (x - 1) * s))
          ((x - 1) / (1 + (x - 1) * s)) s := by
        have := (((hasDerivAt_id s).const_mul (x - 1)).const_add 1).log (hden s hs).ne'
        simpa using this
      have h := ((hasDerivAt_id s).const_mul (-(x - 1))).add (hlog.const_mul x)
      refine h.congr_deriv ?_
      obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = 1 + (x - 1) * s := ⟨_, rfl⟩
      have hd0 : d ≠ 0 := hdd ▸ (hden s hs).ne'
      rw [show 1 - s + s * x = 1 + (x - 1) * s by ring, ← hdd]
      field_simp
      rw [hdd]
      ring
    have hcont : ContinuousOn (fun s ↦ (1 - s) * (x - 1) ^ 2 / (1 - s + s * x)) (Icc 0 1) := by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs ↦ ?_
      rw [show 1 - s + s * x = 1 + (x - 1) * s by ring]
      exact (hden s hs).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs ↦ hF s (by rwa [uIcc_of_le zero_le_one] at hs))
      (hcont.intervalIntegrable_of_Icc zero_le_one)]
    simp only [klFun, mul_one, mul_zero, add_zero, Real.log_one, sub_zero, add_sub_cancel]
    ring

end Scalar

section Law

variable {X : Type*} [MeasurableSpace X] (ν D : Measure X) [IsProbabilityMeasure ν]
  [IsProbabilityMeasure D]

/-- **The data Fisher information of the mixture path** at `s`: `∫ (f − 1)² / (1 − s + s f) dν`
with `f = dD/dν`. -/
noncomputable def dataFisher (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (((D.rnDeriv ν x).toReal - 1) ^ 2 /
    (1 - s + s * (D.rnDeriv ν x).toReal)) ∂ν

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure D] in
theorem measurable_dataFisher_integrand :
    Measurable fun p : X × ℝ ↦ ENNReal.ofReal ((1 - p.2) * ((D.rnDeriv ν p.1).toReal - 1) ^ 2 /
      (1 - p.2 + p.2 * (D.rnDeriv ν p.1).toReal)) := by
  have hf : Measurable fun p : X × ℝ ↦ (D.rnDeriv ν p.1).toReal :=
    (Measure.measurable_rnDeriv D ν).ennreal_toReal.comp measurable_fst
  have hs : Measurable fun p : X × ℝ ↦ p.2 := measurable_snd
  exact Measurable.ennreal_ofReal (by fun_prop)

/-- **The data-side Fisher budget**: `KL(D ‖ ν) = ∫₀¹ (1 − s) 𝓕_data(s) ds`, in `ℝ≥0∞`. -/
theorem klDiv_eq_lintegral_dataFisher (hD : D ≪ ν) :
    klDiv D ν = ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - s) * dataFisher ν D s := by
  rw [klDiv_eq_lintegral_klFun_of_ac hD]
  -- the pointwise identity, in `ℝ≥0∞`
  have hpt : ∀ x, ENNReal.ofReal (klFun (D.rnDeriv ν x).toReal) =
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - s) * ((D.rnDeriv ν x).toReal - 1) ^ 2 /
        (1 - s + s * (D.rnDeriv ν x).toReal)) := by
    intro x
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (D.rnDeriv ν x).toReal := ⟨_, rfl⟩
    rw [← hy]
    have hy0 : 0 ≤ y := hy ▸ ENNReal.toReal_nonneg
    rw [klFun_eq_integral hy0, intervalIntegral.integral_of_le zero_le_one]
    refine ofReal_integral_eq_lintegral_ofReal ?_ ?_
    · -- integrability on `Ioc 0 1`: the integrand is bounded by `(y − 1)²`
      have hmeas : Measurable fun s : ℝ ↦ (1 - s) * (y - 1) ^ 2 / (1 - s + s * y) := by fun_prop
      refine Measure.integrableOn_of_bounded (M := (y - 1) ^ 2) measure_Ioc_lt_top.ne
        hmeas.aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with s hs
      rw [Real.norm_eq_abs]
      rcases (sub_nonneg.2 hs.2).eq_or_lt with h0 | hpos
      · -- `s = 1`
        have : s = 1 := by linarith
        subst this
        simp only [sub_self, zero_mul, zero_div, abs_zero]
        positivity
      · have hden : 0 < 1 - s + s * y := by nlinarith [hs.1]
        rw [abs_of_nonneg (div_nonneg (mul_nonneg hpos.le (sq_nonneg _)) hden.le)]
        rw [div_le_iff₀ hden]
        nlinarith [sq_nonneg (y - 1), hs.1, mul_nonneg hs.1.le hy0]
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with s hs
      have hden : 0 ≤ 1 - s + s * y := by nlinarith [hs.1, hs.2]
      exact div_nonneg (mul_nonneg (sub_nonneg.2 hs.2) (sq_nonneg _)) hden
  simp_rw [hpt]
  -- Tonelli
  have hmeas := measurable_dataFisher_integrand ν D
  rw [lintegral_lintegral_swap (f := fun x s ↦ ENNReal.ofReal ((1 - s) *
      ((D.rnDeriv ν x).toReal - 1) ^ 2 / (1 - s + s * (D.rnDeriv ν x).toReal)))
    hmeas.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
  unfold dataFisher
  have hf : Measurable fun x ↦ (D.rnDeriv ν x).toReal :=
    (Measure.measurable_rnDeriv D ν).ennreal_toReal
  have hm : Measurable fun x ↦ ENNReal.ofReal (((D.rnDeriv ν x).toReal - 1) ^ 2 /
      (1 - s + s * (D.rnDeriv ν x).toReal)) :=
    Measurable.ennreal_ofReal (by fun_prop)
  rw [← lintegral_const_mul _ hm]
  refine lintegral_congr fun x ↦ ?_
  rw [← ENNReal.ofReal_mul (sub_nonneg.2 hs.2), mul_div_assoc]

end Law

end Laplace.Multi
