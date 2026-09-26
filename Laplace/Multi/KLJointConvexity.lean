/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.BridgeResidual

/-!
# Joint convexity of the Kullback–Leibler divergence

`KL(a P₀ + b P₁ ‖ a Q₀ + b Q₁) ≤ a KL(P₀ ‖ Q₀) + b KL(P₁ ‖ Q₁)` for probability laws with
`Pᵢ ≪ Qᵢ` and weights `a + b = 1`, `a, b > 0` (`klDiv_mixture_mixture_le`). The proof takes the
mixture `Q = a Q₀ + b Q₁` itself as the reference measure: with `hᵢ = dPᵢ/dQᵢ`, `qᵢ = dQᵢ/dQ` and
`h = dP/dQ` one has `h = a q₀ h₀ + b q₁ h₁` and `1 = a q₀ + b q₁` almost everywhere, and the
pointwise inequality `klFun h ≤ a q₀ klFun h₀ + b q₁ klFun h₁` is convexity of `klFun` with the
weights `a q₀, b q₁` (`klFun_perspective_le`). No integrability hypotheses are needed: the
inequality is between `lintegral`s of nonnegative functions.

Consequence for the atlas: the fibre information along the mixture bridge is bounded by its
endpoint value without slack, `L_s ≤ s L₁` (`fibreInformation_bridge_le'`), improving the
binary-entropy modulus of `BridgeResidual`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

/-- **The perspective inequality for `klFun`**: if `q = a q₀ + b q₁` and `q H = a q₀ H₀ + b q₁ H₁`
with all quantities nonnegative, then `q klFun H ≤ a q₀ klFun H₀ + b q₁ klFun H₁`. -/
theorem klFun_perspective_le {a b q₀ q₁ H H₀ H₁ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq₀ : 0 ≤ q₀)
    (hq₁ : 0 ≤ q₁) (hH₀ : 0 ≤ H₀) (hH₁ : 0 ≤ H₁)
    (hH : (a * q₀ + b * q₁) * H = a * q₀ * H₀ + b * q₁ * H₁) :
    (a * q₀ + b * q₁) * klFun H ≤ a * q₀ * klFun H₀ + b * q₁ * klFun H₁ := by
  have h0 : 0 ≤ a * q₀ := mul_nonneg ha hq₀
  have h1 : 0 ≤ b * q₁ := mul_nonneg hb hq₁
  rcases (add_nonneg h0 h1).eq_or_lt with hq | hq
  · have ha0 : a * q₀ = 0 := by linarith
    have hb0 : b * q₁ = 0 := by linarith
    rw [← hq, ha0, hb0]
    simp
  · obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = a * q₀ + b * q₁ := ⟨_, rfl⟩
    rw [← hqdef] at hq hH ⊢
    have hw : a * q₀ / q + b * q₁ / q = 1 := by
      rw [← add_div, ← hqdef, div_self hq.ne']
    have hconv := convexOn_klFun.2 (Set.mem_Ici.2 hH₀) (Set.mem_Ici.2 hH₁)
      (div_nonneg h0 hq.le) (div_nonneg h1 hq.le) hw
    simp only [smul_eq_mul] at hconv
    have hHeq : a * q₀ / q * H₀ + b * q₁ / q * H₁ = H := by
      field_simp
      linarith
    rw [hHeq] at hconv
    have := mul_le_mul_of_nonneg_left hconv hq.le
    calc q * klFun H ≤ q * (a * q₀ / q * klFun H₀ + b * q₁ / q * klFun H₁) := this
      _ = a * q₀ * klFun H₀ + b * q₁ * klFun H₁ := by
        field_simp

/-- The perspective inequality in `ℝ≥0∞`, for finite `q₀, q₁, p` with `1 = a q₀ + b q₁` and
`p = a h₀ q₀ + b h₁ q₁`. -/
theorem ofReal_klFun_perspective_le {a b : ℝ≥0} {q₀ q₁ h₀ h₁ p : ℝ≥0∞} (hq₀ : q₀ ≠ ⊤)
    (hq₁ : q₁ ≠ ⊤) (hp : p ≠ ⊤) (hone : (1 : ℝ≥0∞) = a * q₀ + b * q₁)
    (hp' : p = a * (h₀ * q₀) + b * (h₁ * q₁)) :
    ENNReal.ofReal (klFun p.toReal) ≤
      (a : ℝ≥0∞) * (q₀ * ENNReal.ofReal (klFun h₀.toReal)) +
        (b : ℝ≥0∞) * (q₁ * ENNReal.ofReal (klFun h₁.toReal)) := by
  have hfin : (a : ℝ≥0∞) * (h₀ * q₀) ≠ ⊤ ∧ (b : ℝ≥0∞) * (h₁ * q₁) ≠ ⊤ :=
    ENNReal.add_ne_top.1 (hp' ▸ hp)
  have hone' : (1 : ℝ) = (a : ℝ) * q₀.toReal + (b : ℝ) * q₁.toReal := by
    have := congrArg ENNReal.toReal hone
    rwa [ENNReal.toReal_one, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hq₀)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hq₁), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.coe_toReal, ENNReal.coe_toReal] at this
  have hp'' : p.toReal = (a : ℝ) * (h₀.toReal * q₀.toReal) + (b : ℝ) * (h₁.toReal * q₁.toReal) := by
    have := congrArg ENNReal.toReal hp'
    rwa [ENNReal.toReal_add hfin.1 hfin.2, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal] at this
  have hreal := klFun_perspective_le (a := a) (b := b) (q₀ := q₀.toReal) (q₁ := q₁.toReal)
    (H := p.toReal) (H₀ := h₀.toReal) (H₁ := h₁.toReal) a.coe_nonneg b.coe_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (by rw [← hone', hp'']; ring)
  rw [← hone', one_mul] at hreal
  have hk₀ := klFun_nonneg (ENNReal.toReal_nonneg (a := h₀))
  have hk₁ := klFun_nonneg (ENNReal.toReal_nonneg (a := h₁))
  have hQ0 := ENNReal.toReal_nonneg (a := q₀)
  have hQ1 := ENNReal.toReal_nonneg (a := q₁)
  calc ENNReal.ofReal (klFun p.toReal)
      ≤ ENNReal.ofReal ((a : ℝ) * q₀.toReal * klFun h₀.toReal +
          (b : ℝ) * q₁.toReal * klFun h₁.toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = (a : ℝ≥0∞) * (q₀ * ENNReal.ofReal (klFun h₀.toReal)) +
        (b : ℝ≥0∞) * (q₁ * ENNReal.ofReal (klFun h₁.toReal)) := by
        rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg a.coe_nonneg hQ0) hk₀)
          (mul_nonneg (mul_nonneg b.coe_nonneg hQ1) hk₁), mul_assoc, mul_assoc,
          ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
          ENNReal.ofReal_mul hQ0, ENNReal.ofReal_mul hQ1, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hq₀, ENNReal.ofReal_toReal hq₁]

section Joint

variable {X : Type*} [MeasurableSpace X]

/-- **Joint convexity of the Kullback–Leibler divergence**:
`KL(a P₀ + b P₁ ‖ a Q₀ + b Q₁) ≤ a KL(P₀ ‖ Q₀) + b KL(P₁ ‖ Q₁)`. -/
theorem klDiv_mixture_mixture_le (P₀ P₁ Q₀ Q₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (h₀ : P₀ ≪ Q₀) (h₁ : P₁ ≪ Q₁) {a b : ℝ≥0} (hab : a + b = 1) (ha : 0 < a) (hb : 0 < b) :
    klDiv (a • P₀ + b • P₁) (a • Q₀ + b • Q₁) ≤
      (a : ℝ≥0∞) * klDiv P₀ Q₀ + (b : ℝ≥0∞) * klDiv P₁ Q₁ := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Measure X, Q = a • Q₀ + b • Q₁ := ⟨_, rfl⟩
  have hQP : IsProbabilityMeasure Q := by
    rw [hQ]
    exact isProbabilityMeasure_mixture Q₀ Q₁ hab
  have hQ₀Q : Q₀ ≪ Q := by
    rw [hQ]
    exact (Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 ha.ne')).trans
      (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))
  have hQ₁Q : Q₁ ≪ Q := by
    rw [hQ]
    exact (Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 hb.ne')).trans
      (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  have hP₀Q : P₀ ≪ Q := h₀.trans hQ₀Q
  have hP₁Q : P₁ ≪ Q := h₁.trans hQ₁Q
  have hPQ : a • P₀ + b • P₁ ≪ Q := by
    intro A hA
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hP₀Q hA, hP₁Q hA]
    simp
  rw [← hQ, klDiv_eq_lintegral_klFun_of_ac hPQ, klDiv_eq_lintegral_klFun_of_ac h₀,
    klDiv_eq_lintegral_klFun_of_ac h₁]
  -- the divergences of the components as integrals against `Q`
  have hwd : ∀ (Qi : Measure X) [IsFiniteMeasure Qi], Qi ≪ Q → ∀ F : X → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂Qi = ∫⁻ x, Qi.rnDeriv Q x * F x ∂Q := by
    intro Qi _ hQi F hF
    have := lintegral_withDensity_eq_lintegral_mul Q (Measure.measurable_rnDeriv Qi Q) hF
    rw [Measure.withDensity_rnDeriv_eq Qi Q hQi] at this
    exact this
  have hk₀ : Measurable fun x ↦ ENNReal.ofReal (klFun (P₀.rnDeriv Q₀ x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (P₀.rnDeriv Q₀ x).toReal).ennreal_ofReal
  have hk₁ : Measurable fun x ↦ ENNReal.ofReal (klFun (P₁.rnDeriv Q₁ x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (P₁.rnDeriv Q₁ x).toReal).ennreal_ofReal
  have hq₀ := Measure.measurable_rnDeriv Q₀ Q
  have hq₁ := Measure.measurable_rnDeriv Q₁ Q
  have hg₀ : Measurable fun x ↦
      Q₀.rnDeriv Q x * ENNReal.ofReal (klFun (P₀.rnDeriv Q₀ x).toReal) := hq₀.mul hk₀
  have hg₁ : Measurable fun x ↦
      Q₁.rnDeriv Q x * ENNReal.ofReal (klFun (P₁.rnDeriv Q₁ x).toReal) := hq₁.mul hk₁
  rw [hwd Q₀ hQ₀Q _ hk₀, hwd Q₁ hQ₁Q _ hk₁, ← lintegral_const_mul _ hg₀,
    ← lintegral_const_mul _ hg₁, ← lintegral_add_left (hg₀.const_mul _)]
  refine lintegral_mono_ae ?_
  -- the almost-everywhere density identities
  have hone : Q.rnDeriv Q =ᵐ[Q] fun _ ↦ 1 := Measure.rnDeriv_self Q
  have hsum : Q.rnDeriv Q =ᵐ[Q]
      fun x ↦ (a : ℝ≥0∞) * Q₀.rnDeriv Q x + (b : ℝ≥0∞) * Q₁.rnDeriv Q x := by
    have h := Measure.rnDeriv_add' (a • Q₀) (b • Q₁) Q
    rw [← hQ] at h
    filter_upwards [h, Measure.rnDeriv_smul_left' Q₀ Q a, Measure.rnDeriv_smul_left' Q₁ Q b]
      with x hx1 hx2 hx3
    rw [hx1, Pi.add_apply, hx2, hx3]
    rfl
  have hP : (a • P₀ + b • P₁).rnDeriv Q =ᵐ[Q]
      fun x ↦ (a : ℝ≥0∞) * P₀.rnDeriv Q x + (b : ℝ≥0∞) * P₁.rnDeriv Q x := by
    filter_upwards [Measure.rnDeriv_add' (a • P₀) (b • P₁) Q, Measure.rnDeriv_smul_left' P₀ Q a,
      Measure.rnDeriv_smul_left' P₁ Q b] with x hx1 hx2 hx3
    rw [hx1, Pi.add_apply, hx2, hx3]
    rfl
  filter_upwards [hone, hsum, hP, Measure.rnDeriv_mul_rnDeriv (κ := Q) h₀,
    Measure.rnDeriv_mul_rnDeriv (κ := Q) h₁, Measure.rnDeriv_ne_top Q₀ Q,
    Measure.rnDeriv_ne_top Q₁ Q, Measure.rnDeriv_ne_top (a • P₀ + b • P₁) Q]
    with x h1 hs hp hc₀ hc₁ hq₀t hq₁t hpt
  rw [Pi.mul_apply] at hc₀ hc₁
  rw [h1] at hs
  exact ofReal_klFun_perspective_le hq₀t hq₁t hpt hs (by rw [hp, hc₀, hc₁])

end Joint

section Bridge

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : X → Y) (hS : Measurable S) (hD : D ≪ ν)
  {a b : ℝ≥0} (hab : a + b = 1) (ha : 0 < a) (hb : 0 < b)
include hS hD hab ha hb

/-- **The fibre information along the bridge is bounded by its endpoint value**:
`KL(D_s ‖ D_s↑) ≤ b KL(D ‖ D↑)` with `D_s = a ν + b D`, no slack. -/
theorem fibreInformation_bridge_le' :
    klDiv (a • ν + b • D) (statisticLift ν (a • ν + b • D) S) ≤
      (b : ℝ≥0∞) * klDiv D (statisticLift ν D S) := by
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  rw [statisticLift_bridge ν S hS D a b]
  have := klDiv_mixture_mixture_le ν D ν (statisticLift ν D S) Measure.AbsolutelyContinuous.rfl
    (absolutelyContinuous_statisticLift ν D S hS hD) hab ha hb
  rwa [klDiv_self, mul_zero, zero_add] at this

end Bridge

end Laplace.Multi
