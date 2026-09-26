/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.EntropyTaylor
import Laplace.Multi.LiftConditional
import Laplace.Multi.ObservableDefect
import Laplace.Multi.TiltRateQuadratic

/-!
# The lifted law of a tilt is the conditional expectation of its density

* `condLExp_ofReal_ae_eq`: for a nonnegative integrable `f`, the `ℝ≥0∞`-valued conditional
  expectation of `ofReal ∘ f` is `ofReal ∘ E[f | m]`.
* `statisticLift_eq_withDensity_condExp`: the statistic lift of `pν` is `E_ν[p | σ(S)] ν`.
* `tiltDens_sub_le`: the density `p_t = e^{tf}/Z_t` of the tilt satisfies
  `|p_t − 1 − t(f − E_ν f)| ≤ 9 B² t²` for `|t| ≤ 1/(4(B+1))`, `|f| ≤ B`.
* `toReal_klDiv_withDensity_ofReal_ae`: `KL(rν ‖ ν) = ∫ klFun r dν` for a.e. bounded positive `r`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section CondLExp

variable {X : Type*} {m m₀ : MeasurableSpace X} (ν : Measure[m₀] X) [IsFiniteMeasure ν]

/-- The `ℝ≥0∞` conditional expectation of a nonnegative integrable function is the `ofReal` of
its real conditional expectation. -/
theorem condLExp_ofReal_ae_eq (hm : m ≤ m₀) {f : X → ℝ} (hf : Integrable f ν) (hf0 : 0 ≤ᵐ[ν] f) :
    ν⁻[fun x ↦ ENNReal.ofReal (f x) | m] =ᵐ[ν] fun x ↦ ENNReal.ofReal ((ν[f | m]) x) := by
  symm
  refine ae_eq_condLExp hm ν (fun x ↦ ENNReal.ofReal (f x))
    (stronglyMeasurable_condExp.measurable.ennreal_ofReal) fun s hs ↦ ?_
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_condExp.integrableOn
    (ae_restrict_of_ae (condExp_nonneg hf0)),
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_restrict_of_ae hf0),
    setIntegral_condExp hm hf hs]

end CondLExp

section Lift

variable {X : Type*} [MeasurableSpace X] {J : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The statistic lift of `pν` is `E_ν[p | σ(S)] ν`.** -/
theorem statisticLift_eq_withDensity_condExp {p : X → ℝ} (hp : Measurable p) (hpi : Integrable p ν)
    (hp0 : 0 ≤ᵐ[ν] p) [IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (p x))] :
    statisticLift ν (ν.withDensity fun x ↦ ENNReal.ofReal (p x)) (statPoint S) =
      ν.withDensity fun x ↦ ENNReal.ofReal ((ν[p | statSigma S]) x) := by
  have hD : (ν.withDensity fun x ↦ ENNReal.ofReal (p x)) ≪ ν := withDensity_absolutelyContinuous ν _
  have hL := statisticLift_absolutelyContinuous ν (ν.withDensity fun x ↦ ENNReal.ofReal (p x))
    (statPoint S)
  have := isProbabilityMeasure_statisticLift ν (ν.withDensity fun x ↦ ENNReal.ofReal (p x))
    (statPoint S) (measurable_statPoint hS) hD
  rw [← Measure.withDensity_rnDeriv_eq _ _ hL]
  refine withDensity_congr_ae ?_
  have h1 := rnDeriv_statisticLift_eq_condLExp ν (ν.withDensity fun x ↦ ENNReal.ofReal (p x))
    (statPoint S) (measurable_statPoint hS) hD
  have h2 : (ν.withDensity fun x ↦ ENNReal.ofReal (p x)).rnDeriv ν =ᵐ[ν]
      fun x ↦ ENNReal.ofReal (p x) := Measure.rnDeriv_withDensity ν hp.ennreal_ofReal
  have h3 := condLExp_congr_ae (mΩ := statSigma S) h2
  have h4 := condLExp_ofReal_ae_eq ν (statSigma_le hS) hpi hp0
  exact h1.trans (h3.trans h4)

end Lift

section Tilt

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The density of the tilt `ν_t ∝ e^{tf} ν`. -/
noncomputable def tiltDens (f : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  Real.exp (t * f x) / ∫ y, Real.exp (t * f y) ∂ν

omit [IsProbabilityMeasure ν] in
theorem tilted_eq_withDensity_tiltDens (f : X → ℝ) (t : ℝ) :
    ν.tilted (fun x ↦ t * f x) = ν.withDensity fun x ↦ ENNReal.ofReal (tiltDens ν f t x) := rfl

/-- **The tilt density expansion**: `|p_t − 1 − t(f − E_ν f)| ≤ 9 B² t²` for `|t| ≤ 1/(4(B+1))`. -/
theorem tiltDens_sub_le {f : X → ℝ} (hfm : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |f x| ≤ B) {t : ℝ} (ht : |t| ≤ 1 / (4 * (B + 1))) (x : X) :
    |tiltDens ν f t x - (1 + t * (f x - ∫ y, f y ∂ν))| ≤ 9 * B ^ 2 * t ^ 2 := by
  have hf : Bdd f := ⟨hfm, B, hB⟩
  have htB : |t| * B ≤ 1 / 4 := by
    calc |t| * B ≤ 1 / (4 * (B + 1)) * B := by gcongr
      _ ≤ 1 / 4 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have ht1 : |t| ≤ 1 := by
    have : (1 : ℝ) / (4 * (B + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact ht.trans this
  have hfi := integrable_of_bdd_prob ν hf
  -- (i) pointwise: `|e^{tf} − 1 − tf| ≤ B² t²`
  have hexp : ∀ y, |Real.exp (t * f y) - 1 - t * f y| ≤ B ^ 2 * t ^ 2 := fun y ↦ by
    have h1 : |t * f y| ≤ 1 := by
      rw [abs_mul]
      calc |t| * |f y| ≤ |t| * B := by gcongr; exact hB y
        _ ≤ 1 / 4 := htB
        _ ≤ 1 := by norm_num
    refine (Real.abs_exp_sub_one_sub_id_le h1).trans ?_
    rw [mul_pow, ← sq_abs t, ← sq_abs (f y)]
    have := pow_le_pow_left₀ (abs_nonneg _) (hB y) 2
    nlinarith [sq_nonneg t, sq_nonneg (|t|)]
  -- (ii) the normaliser: `|Z − 1 − t E f| ≤ B² t²`
  have hexpi : Integrable (fun y ↦ Real.exp (t * f y)) ν :=
    integrable_exp_of_bdd ν (Bdd.const_mul t hf)
  have hZ : |(∫ y, Real.exp (t * f y) ∂ν) - 1 - t * ∫ y, f y ∂ν| ≤ B ^ 2 * t ^ 2 := by
    have e : (∫ y, Real.exp (t * f y) ∂ν) - 1 - t * ∫ y, f y ∂ν =
        ∫ y, (Real.exp (t * f y) - 1 - t * f y) ∂ν := by
      have h1 : Integrable (fun y ↦ Real.exp (t * f y) - 1) ν := hexpi.sub (integrable_const 1)
      rw [integral_sub h1 (hfi.const_mul t), integral_sub hexpi (integrable_const 1),
        integral_const, integral_const_mul, probReal_univ, one_smul]
    rw [e, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_const (B ^ 2 * t ^ 2))
      (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hexp y)).trans ?_
    rw [integral_const, probReal_univ, one_smul]
  -- (iii) `Z ≥ 1/2`
  have hEf : |∫ y, f y ∂ν| ≤ B := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_const B)
      (Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hB y)).trans ?_
    rw [integral_const, probReal_univ, one_smul]
  have hZhalf : 1 / 2 ≤ ∫ y, Real.exp (t * f y) ∂ν := by
    have h1 := (abs_le.1 hZ).1
    have h2 : |t * ∫ y, f y ∂ν| ≤ 1 / 4 := by
      rw [abs_mul]
      calc |t| * |∫ y, f y ∂ν| ≤ |t| * B := by gcongr
        _ ≤ 1 / 4 := htB
    have h3 : B ^ 2 * t ^ 2 ≤ 1 / 16 := by
      have : (|t| * B) ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (by positivity) htB 2
      rw [mul_pow, sq_abs] at this
      nlinarith
    linarith [(abs_le.1 h2).1]
  -- (iv) the numerator
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = ∫ y, Real.exp (t * f y) ∂ν := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ∫ y, f y ∂ν := ⟨_, rfl⟩
  rw [← hZdef] at hZ hZhalf
  rw [← hmdef] at hZ hEf
  have hZpos : 0 < Z := by linarith
  have hnum : |Real.exp (t * f x) - Z * (1 + t * (f x - m))| ≤ 9 / 2 * B ^ 2 * t ^ 2 := by
    have e : Real.exp (t * f x) - Z * (1 + t * (f x - m)) =
        (Real.exp (t * f x) - 1 - t * f x) - t ^ 2 * (m * (f x - m)) -
          (Z - 1 - t * m) * (1 + t * (f x - m)) := by ring
    rw [e]
    have hh : |f x - m| ≤ 2 * B := by
      calc |f x - m| ≤ |f x| + |m| := abs_sub _ _
        _ ≤ B + B := add_le_add (hB x) hEf
        _ = 2 * B := by ring
    have h1 : |t ^ 2 * (m * (f x - m))| ≤ 2 * B ^ 2 * t ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, sq_abs]
      calc t ^ 2 * (|m| * |f x - m|) ≤ t ^ 2 * (B * (2 * B)) := by gcongr
        _ = 2 * B ^ 2 * t ^ 2 := by ring
    have h2 : |1 + t * (f x - m)| ≤ 3 / 2 := by
      calc |1 + t * (f x - m)| ≤ |1| + |t| * |f x - m| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ 1 + |t| * (2 * B) := by rw [abs_one]; gcongr
        _ ≤ 1 + 1 / 2 := by nlinarith
        _ = 3 / 2 := by norm_num
    have h3 : |(Z - 1 - t * m) * (1 + t * (f x - m))| ≤ 3 / 2 * (B ^ 2 * t ^ 2) := by
      rw [abs_mul]
      calc |Z - 1 - t * m| * |1 + t * (f x - m)| ≤ B ^ 2 * t ^ 2 * (3 / 2) := by gcongr
        _ = 3 / 2 * (B ^ 2 * t ^ 2) := by ring
    calc |(Real.exp (t * f x) - 1 - t * f x) - t ^ 2 * (m * (f x - m)) -
          (Z - 1 - t * m) * (1 + t * (f x - m))|
        ≤ |Real.exp (t * f x) - 1 - t * f x| + |t ^ 2 * (m * (f x - m))| +
            |(Z - 1 - t * m) * (1 + t * (f x - m))| :=
          (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ B ^ 2 * t ^ 2 + 2 * B ^ 2 * t ^ 2 + 3 / 2 * (B ^ 2 * t ^ 2) :=
          add_le_add (add_le_add (hexp x) h1) h3
      _ = 9 / 2 * B ^ 2 * t ^ 2 := by ring
  unfold tiltDens
  rw [← hZdef, ← hmdef]
  have e : Real.exp (t * f x) / Z - (1 + t * (f x - m)) =
      (Real.exp (t * f x) - Z * (1 + t * (f x - m))) / Z := by
    field_simp
  rw [e, abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
  calc |Real.exp (t * f x) - Z * (1 + t * (f x - m))| ≤ 9 / 2 * B ^ 2 * t ^ 2 := hnum
    _ = 9 * B ^ 2 * t ^ 2 * (1 / 2) := by ring
    _ ≤ 9 * B ^ 2 * t ^ 2 * Z := by gcongr

end Tilt

section KL

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- `KL(rν ‖ ν) = ∫ klFun r dν` for an a.e. bounded positive density. -/
theorem toReal_klDiv_withDensity_ofReal_ae {r : X → ℝ} (hr : Measurable r) {c C : ℝ}
    (hc0 : 0 < c) (hc : ∀ᵐ x ∂ν, c ≤ r x) (hC : ∀ᵐ x ∂ν, r x ≤ C) :
    (klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (r x)) ν).toReal = ∫ x, klFun (r x) ∂ν := by
  have hfin : IsFiniteMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (r x)) := by
    refine isFiniteMeasure_withDensity ?_
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top ?_
    calc ∫⁻ x, ENNReal.ofReal (r x) ∂ν ≤ ∫⁻ _x, ENNReal.ofReal C ∂ν :=
          lintegral_mono_ae (hC.mono fun x hx ↦ ENNReal.ofReal_le_ofReal hx)
      _ = ENNReal.ofReal C := by simp
  have hint : Integrable (fun x ↦ klFun (r x)) ν := by
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := c) (b := C)).exists_bound_of_continuousOn
      continuous_klFun.continuousOn
    refine Integrable.of_bound (measurable_klFun.comp hr).aestronglyMeasurable B ?_
    filter_upwards [hc, hC] with x hx1 hx2
    exact hB _ ⟨hx1, hx2⟩
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous ν _)]
  have hae : (fun x ↦ ENNReal.ofReal
      (klFun ((ν.withDensity fun x ↦ ENNReal.ofReal (r x)).rnDeriv ν x).toReal)) =ᵐ[ν]
      fun x ↦ ENNReal.ofReal (klFun (r x)) := by
    filter_upwards [Measure.rnDeriv_withDensity ν hr.ennreal_ofReal, hc] with x hx hcx
    rw [hx, ENNReal.toReal_ofReal (hc0.le.trans hcx)]
  have hnn : 0 ≤ᵐ[ν] fun x ↦ klFun (r x) :=
    hc.mono fun x hx ↦ klFun_nonneg (hc0.le.trans hx)
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]

end KL

end Laplace.Multi
