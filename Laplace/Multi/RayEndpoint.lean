/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RayChart

/-!
# The far endpoint of the ray: the mean loss tends to the essential infimum

Without any regular-variation hypothesis, the ray chart `m(u) = ⟨ℓ⟩_u` of the featureless line
converges as `u → ∞` to the essential infimum `α` of the loss under the state density, as soon as
`ℓ ≥ α` a.e. and every neighbourhood `{ℓ < α + ε}` has positive mass (`tendsto_lawMean_atTop`).
Regular variation controls the *rate* and the self-similarity (`TauberianVariance`); the endpoint
itself needs only the two structural facts.

The proof is the elementary tilt estimate: with `y = ℓ − α`, `r = u − 1`,
`0 ≤ m(u) − α ≤ ε + (ε W / c_ε) e^{-rε/2}` for `r ≥ 1/ε`, where `W = ∫ e^{-ℓ} dν`,
`c_ε = ∫_{y ≤ ε/2} e^{-ℓ} dν > 0`. The pointwise input is `y e^{-ry} ≤ ε e^{-rε}` for `y ≥ ε`,
`r ≥ 1/ε` (`mul_exp_le_of_le`), from `1 + r(y − ε) ≤ e^{r(y − ε)}`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- `y e^{-ry} ≤ ε e^{-rε}` for `ε ≤ y` and `1/ε ≤ r` (`ε > 0`): the function `y ↦ y e^{-ry}` is
decreasing beyond `1/r`. -/
theorem mul_exp_le_of_le {ε r y : ℝ} (hε : 0 < ε) (hr : 1 / ε ≤ r) (hy : ε ≤ y) :
    y * Real.exp (-(r * y)) ≤ ε * Real.exp (-(r * ε)) := by
  have h1 : r * (y - ε) + 1 ≤ Real.exp (r * (y - ε)) := Real.add_one_le_exp _
  have h2 : (y - ε) / ε ≤ r * (y - ε) := by
    rw [div_le_iff₀ hε]
    have := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ y - ε)
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hε] at this
    linarith
  have h3 : y ≤ ε * Real.exp (r * (y - ε)) := by
    have : y / ε ≤ Real.exp (r * (y - ε)) := by
      have e : y / ε = (y - ε) / ε + 1 := by field_simp; ring
      linarith
    rwa [div_le_iff₀ hε, mul_comm] at this
  calc y * Real.exp (-(r * y)) ≤ ε * Real.exp (r * (y - ε)) * Real.exp (-(r * y)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = ε * Real.exp (-(r * ε)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

section

variable (ν : Measure ℝ)
  (hint : ∀ v > 0, ∀ k ≤ 1, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν)
  {α : ℝ} (hα : ∀ᵐ ℓ ∂ν, α ≤ ℓ) (hmass : ∀ ε > 0, 0 < ν {ℓ | ℓ < α + ε})
include hint hα hmass

omit hα hmass in
theorem integrable_exp_tilt {u : ℝ} (hu : 0 < u) :
    Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν := by
  simpa using hint u hu 0 (by norm_num)

omit hα hmass in
theorem integrable_mul_exp_tilt {u : ℝ} (hu : 0 < u) :
    Integrable (fun ℓ ↦ ℓ * Real.exp (-(u * ℓ))) ν := by
  simpa using hint u hu 1 le_rfl

omit hα in
/-- The partition function is positive (the state density has mass). -/
theorem lawMoment_zero_pos' {u : ℝ} (hu : 0 < u) : 0 < lawMoment ν 0 u := by
  unfold lawMoment
  simp only [pow_zero, one_mul]
  rw [integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun ℓ ↦ (Real.exp_pos _).le) (integrable_exp_tilt ν hint hu)]
  have hsupp : Function.support (fun ℓ ↦ Real.exp (-(u * ℓ))) = univ := by
    ext ℓ; simp [(Real.exp_pos _).ne']
  rw [hsupp]
  exact lt_of_lt_of_le (hmass 1 one_pos) (measure_mono (subset_univ _))

omit hα hmass in
/-- `m(u) − α = ∫ (ℓ − α) e^{-uℓ} / Z(u)`. -/
theorem lawMean_sub_eq {u : ℝ} (hu : 0 < u) (hZ : 0 < lawMoment ν 0 u) :
    lawMean ν u - α = (∫ ℓ, (ℓ - α) * Real.exp (-(u * ℓ)) ∂ν) / lawMoment ν 0 u := by
  have e : (∫ ℓ, (ℓ - α) * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 1 u - α * lawMoment ν 0 u := by
    have h1 := integrable_mul_exp_tilt ν hint hu
    have h0 := (integrable_exp_tilt ν hint hu).const_mul α
    have h1' : Integrable (fun ℓ ↦ ℓ * Real.exp (-(u * ℓ)) - α * Real.exp (-(u * ℓ))) ν :=
      h1.sub h0
    rw [show (fun ℓ ↦ (ℓ - α) * Real.exp (-(u * ℓ))) =
        fun ℓ ↦ ℓ * Real.exp (-(u * ℓ)) - α * Real.exp (-(u * ℓ)) by funext ℓ; ring,
      integral_sub h1 h0, MeasureTheory.integral_const_mul]
    unfold lawMoment
    simp only [pow_one, pow_zero, one_mul]
  rw [e, lawMean, sub_div, mul_div_assoc, div_self hZ.ne', mul_one]

omit hmass in
/-- The mean loss is at least the essential infimum. -/
theorem le_lawMean {u : ℝ} (hu : 0 < u) (hZ : 0 < lawMoment ν 0 u) : α ≤ lawMean ν u := by
  have h := lawMean_sub_eq ν hint (α := α) hu hZ
  have hN : 0 ≤ ∫ ℓ, (ℓ - α) * Real.exp (-(u * ℓ)) ∂ν :=
    integral_nonneg_of_ae (by filter_upwards [hα] with ℓ hℓ; positivity)
  have : 0 ≤ lawMean ν u - α := by rw [h]; exact div_nonneg hN hZ.le
  linarith

/-- **The tilt estimate**: for `ε > 0` and `u ≥ 1 + 1/ε`,
`m(u) − α ≤ ε + (ε W / c_ε) e^{-(u−1)ε/2}` with `W = ∫ e^{-ℓ}` and
`c_ε = ∫_{ℓ ≤ α + ε/2} e^{-ℓ} > 0`. -/
theorem lawMean_sub_le {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 + 1 / ε ≤ u) :
    lawMean ν u - α ≤ ε + ε * (∫ ℓ, Real.exp (-ℓ) ∂ν) /
      (∫ ℓ in {ℓ | ℓ ≤ α + ε / 2}, Real.exp (-ℓ) ∂ν) * Real.exp (-((u - 1) * ε / 2)) := by
  have hu0 : 0 < u := by
    have : 0 < 1 / ε := by positivity
    linarith
  have hZ := lawMoment_zero_pos' ν hint hmass hu0
  set r := u - 1 with hr
  have hε' : 0 < 1 / ε := by positivity
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : 1 / ε ≤ r := by rw [hr]; linarith
  have hW : Integrable (fun ℓ ↦ Real.exp (-ℓ)) ν := by
    have := integrable_exp_tilt ν hint one_pos
    simpa using this
  set W := ∫ ℓ, Real.exp (-ℓ) ∂ν with hWdef
  set B := {ℓ : ℝ | ℓ ≤ α + ε / 2} with hB
  have hBm : MeasurableSet B := measurableSet_Iic
  set c := ∫ ℓ in B, Real.exp (-ℓ) ∂ν with hcdef
  -- `c > 0`
  have hc : 0 < c := by
    rw [hcdef, setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun ℓ ↦ (Real.exp_pos _).le) hW.integrableOn]
    have hsupp : Function.support (fun ℓ ↦ Real.exp (-ℓ)) = univ := by
      ext ℓ; simp [(Real.exp_pos _).ne']
    rw [hsupp, univ_inter]
    refine lt_of_lt_of_le (hmass (ε / 2) (by positivity)) (measure_mono fun ℓ hℓ ↦ ?_)
    exact le_of_lt (show ℓ < α + ε / 2 from hℓ)
  -- the numerator bound
  have hnum : (∫ ℓ, (ℓ - α) * Real.exp (-(u * ℓ)) ∂ν) ≤
      ε * lawMoment ν 0 u + ε * Real.exp (-(r * (ε + α))) * W := by
    have hI1 : Integrable (fun ℓ ↦ (ℓ - α) * Real.exp (-(u * ℓ))) ν := by
      have := (integrable_mul_exp_tilt ν hint hu0).sub
        ((integrable_exp_tilt ν hint hu0).const_mul α)
      exact this.congr (Filter.Eventually.of_forall fun ℓ ↦ by simp only [Pi.sub_apply]; ring)
    have hI2 : Integrable (fun ℓ ↦ ε * Real.exp (-(u * ℓ)) +
        ε * Real.exp (-(r * (ε + α))) * Real.exp (-ℓ)) ν :=
      ((integrable_exp_tilt ν hint hu0).const_mul ε).add (hW.const_mul _)
    have hpt : ∀ᵐ ℓ ∂ν, (ℓ - α) * Real.exp (-(u * ℓ)) ≤
        ε * Real.exp (-(u * ℓ)) + ε * Real.exp (-(r * (ε + α))) * Real.exp (-ℓ) := by
      filter_upwards [hα] with ℓ hℓ
      rcases le_or_gt (ℓ - α) ε with h | h
      · have : (ℓ - α) * Real.exp (-(u * ℓ)) ≤ ε * Real.exp (-(u * ℓ)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
        have : 0 ≤ ε * Real.exp (-(r * (ε + α))) * Real.exp (-ℓ) := by positivity
        linarith
      · have key := mul_exp_le_of_le hε hr1 h.le
        have e1 : Real.exp (-(u * ℓ)) = Real.exp (-(r * (ℓ - α))) * Real.exp (-(r * α)) *
            Real.exp (-ℓ) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hr]; ring
        have e2 : ε * Real.exp (-(r * ε)) * Real.exp (-(r * α)) * Real.exp (-ℓ) =
            ε * Real.exp (-(r * (ε + α))) * Real.exp (-ℓ) := by
          rw [mul_assoc ε, ← Real.exp_add]
          congr 3
          ring
        have hpos2 : 0 < Real.exp (-(r * α)) * Real.exp (-ℓ) := by positivity
        have : (ℓ - α) * Real.exp (-(u * ℓ)) ≤ ε * Real.exp (-(r * (ε + α))) * Real.exp (-ℓ) := by
          rw [e1, ← e2]
          calc (ℓ - α) * (Real.exp (-(r * (ℓ - α))) * Real.exp (-(r * α)) * Real.exp (-ℓ)) =
                ((ℓ - α) * Real.exp (-(r * (ℓ - α)))) * (Real.exp (-(r * α)) * Real.exp (-ℓ)) := by
                  ring
            _ ≤ (ε * Real.exp (-(r * ε))) * (Real.exp (-(r * α)) * Real.exp (-ℓ)) :=
                mul_le_mul_of_nonneg_right key hpos2.le
            _ = ε * Real.exp (-(r * ε)) * Real.exp (-(r * α)) * Real.exp (-ℓ) := by ring
        have : 0 ≤ ε * Real.exp (-(u * ℓ)) := by positivity
        linarith
    calc (∫ ℓ, (ℓ - α) * Real.exp (-(u * ℓ)) ∂ν) ≤ ∫ ℓ, (ε * Real.exp (-(u * ℓ)) +
          ε * Real.exp (-(r * (ε + α))) * Real.exp (-ℓ)) ∂ν := integral_mono_ae hI1 hI2 hpt
      _ = ε * lawMoment ν 0 u + ε * Real.exp (-(r * (ε + α))) * W := by
          rw [integral_add ((integrable_exp_tilt ν hint hu0).const_mul ε) (hW.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          unfold lawMoment
          simp only [pow_zero, one_mul]
          rfl
  -- the denominator bound
  have hden : Real.exp (-(r * (α + ε / 2))) * c ≤ lawMoment ν 0 u := by
    have hZu : Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν := integrable_exp_tilt ν hint hu0
    calc Real.exp (-(r * (α + ε / 2))) * c
        = ∫ ℓ in B, Real.exp (-(r * (α + ε / 2))) * Real.exp (-ℓ) ∂ν := by
          rw [hcdef, ← MeasureTheory.integral_const_mul]
      _ ≤ ∫ ℓ in B, Real.exp (-(u * ℓ)) ∂ν := by
          refine setIntegral_mono_on (hW.const_mul _).integrableOn hZu.integrableOn hBm
            fun ℓ hℓ ↦ ?_
          have hℓ' : ℓ ≤ α + ε / 2 := hℓ
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have : r * ℓ ≤ r * (α + ε / 2) := mul_le_mul_of_nonneg_left hℓ' hr0
          rw [hr] at this ⊢
          linarith
      _ ≤ lawMoment ν 0 u := by
          unfold lawMoment
          simp only [pow_zero, one_mul]
          exact setIntegral_le_integral hZu
            (Filter.Eventually.of_forall fun ℓ ↦ (Real.exp_pos _).le)
  -- assemble
  rw [lawMean_sub_eq ν hint hu0 hZ, div_le_iff₀ hZ]
  have hden' : 0 < Real.exp (-(r * (α + ε / 2))) * c := by positivity
  calc (∫ ℓ, (ℓ - α) * Real.exp (-(u * ℓ)) ∂ν)
      ≤ ε * lawMoment ν 0 u + ε * Real.exp (-(r * (ε + α))) * W := hnum
    _ = ε * lawMoment ν 0 u + (ε * W / c * Real.exp (-(r * ε / 2))) *
        (Real.exp (-(r * (α + ε / 2))) * c) := by
          have e : Real.exp (-(r * ε / 2)) * Real.exp (-(r * (α + ε / 2))) =
              Real.exp (-(r * (ε + α))) := by
            rw [← Real.exp_add]; congr 1; ring
          field_simp
          rw [← e]
          ring
    _ ≤ ε * lawMoment ν 0 u + (ε * W / c * Real.exp (-(r * ε / 2))) * lawMoment ν 0 u := by
          gcongr
    _ = (ε + ε * W / c * Real.exp (-(r * ε / 2))) * lawMoment ν 0 u := by ring

/-- **The far endpoint of the ray**: `⟨ℓ⟩_u → ess inf ℓ` as `u → ∞`, with no regular variation. -/
theorem tendsto_lawMean_atTop : Tendsto (lawMean ν) atTop (𝓝 α) := by
  rw [tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact lt_of_lt_of_le ha (le_lawMean ν hint hα hu (lawMoment_zero_pos' ν hint hmass hu))
  · set ε := (b - α) / 3 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    set W := ∫ ℓ, Real.exp (-ℓ) ∂ν with hWdef
    set c := ∫ ℓ in {ℓ : ℝ | ℓ ≤ α + ε / 2}, Real.exp (-ℓ) ∂ν with hcdef
    have hlim : Tendsto (fun u : ℝ ↦ ε * W / c * Real.exp (-((u - 1) * ε / 2))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ ↦ (u - 1) * ε / 2) atTop atTop :=
        (((tendsto_atTop_add_const_right atTop (-1) tendsto_id).atTop_mul_const hε0).atTop_div_const
          (r := 2) (by norm_num)).congr fun u ↦ by simp only [id_eq]; ring
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (ε * W / c)
      simpa [Function.comp_def] using this
    filter_upwards [eventually_ge_atTop (1 + 1 / ε), hlim.eventually (gt_mem_nhds hε0)] with u hu
      hsmall
    have h := lawMean_sub_le ν hint hα hmass hε0 hu
    have : lawMean ν u - α < 2 * ε := by linarith
    rw [hε] at this
    linarith

end

end Laplace.Multi
