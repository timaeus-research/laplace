/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.GeneralResidualSplit
import Laplace.Multi.MixtureCompensation
import Laplace.Multi.MixtureBridge

/-!
# The residual information along the mixture bridge

Along the mixture bridge `D_s = (1 − s) ν + s D` from the featureless law to the data law:

* **entropy moduli** (`klDiv_mixture_self_le`, `toReal_klDiv_mixture_ge`):
  `s H − h₂(s) ≤ KL(D_s ‖ ν) ≤ s H` with `H = KL(D ‖ ν)` and `h₂` the binary entropy, from convexity
  of the divergence and the mixture compensation identity together with the elementary bound
  `KL(P ‖ Q) ≤ log(1/a)` when `a P ≤ Q` (`klDiv_le_log_of_smul_le`);
* **the lift is affine** (`statisticLift_mixture`, `statisticLift_self`, `statisticLift_bridge`):
  `(a D₀ + b D₁)↑ = a D₀↑ + b D₁↑`, `ν↑ = ν`, hence `D_s↑ = (1 − s) ν + s D↑`;
* **the fibre information along the bridge** `L_s = KL(D_s ‖ D_s↑)` satisfies
  `s L₁ − h₂(s) ≤ L_s ≤ s L₁ + h₂(s)` (`fibreInformation_bridge_ge`, `fibreInformation_bridge_le`);
* **the total residual** `R_s = KL(D_s ‖ ν) − 𝓘(M_s)` satisfies
  `(1 − s) H − δ𝓘_s ≤ R₁ − R_s ≤ (1 − s) H + h₂(s) − δ𝓘_s` with `δ𝓘_s = 𝓘(M_D) − 𝓘(M_s)`
  (`invisibleInformation_bridge_modulus`): the endpoint convergence of the invisible information is
  controlled by the information gap of the atlas, with at most a binary-entropy slack.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

section LogBound

variable {X : Type*} [MeasurableSpace X]

/-- The binary entropy `h₂(a, b) = a log(1/a) + b log(1/b)`. -/
noncomputable def binEnt (a b : ℝ≥0) : ℝ := (a : ℝ) * Real.log (1 / a) + (b : ℝ) * Real.log (1 / b)

/-- **A dominated law has bounded information**: if `a P ≤ Q` with `a > 0`, then
`KL(P ‖ Q) ≤ log(1/a)`. -/
theorem klDiv_le_log_of_smul_le (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {a : ℝ≥0} (ha : 0 < a) (hle : a • P ≤ Q) : klDiv P Q ≤ ENNReal.ofReal (Real.log (1 / a)) := by
  have hPQ : P ≪ Q :=
    (Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 ha.ne')).trans
      (Measure.absolutelyContinuous_of_le hle)
  have ha' : (0 : ℝ) < a := ha
  have hbound : ∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal ≤ 1 / a := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hle, Measure.rnDeriv_smul_left' P Q a] with x h1 h2
    rw [h2, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    have h1' : ((a : ℝ≥0∞) * P.rnDeriv Q x).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top h1
      rwa [ENNReal.toReal_one] at this
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at h1'
    rw [le_div_iff₀ ha']
    linarith [mul_comm (a : ℝ) (P.rnDeriv Q x).toReal]
  rw [klDiv_eq_lintegral_klFun_of_ac hPQ]
  have hint := Measure.integrable_toReal_rnDeriv (μ := P) (ν := Q)
  have hpt : ∀ᵐ x ∂Q, klFun (P.rnDeriv Q x).toReal ≤
      (P.rnDeriv Q x).toReal * Real.log (1 / a) + 1 - (P.rnDeriv Q x).toReal := by
    filter_upwards [hbound] with x hx
    have hx0 : 0 ≤ (P.rnDeriv Q x).toReal := ENNReal.toReal_nonneg
    rw [klFun_apply]
    have : (P.rnDeriv Q x).toReal * Real.log (P.rnDeriv Q x).toReal ≤
        (P.rnDeriv Q x).toReal * Real.log (1 / a) := by
      rcases hx0.eq_or_lt with h0 | hpos
      · rw [← h0]
        simp
      · exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hx) hx0
    linarith
  have hI0 : Integrable (fun x ↦ (P.rnDeriv Q x).toReal * Real.log (1 / a)) Q := hint.mul_const _
  have hI1 : Integrable (fun x ↦ (P.rnDeriv Q x).toReal * Real.log (1 / a) + 1) Q :=
    hI0.add (integrable_const _)
  have hint2 : Integrable (fun x ↦ (P.rnDeriv Q x).toReal * Real.log (1 / a) + 1 -
      (P.rnDeriv Q x).toReal) Q := hI1.sub hint
  calc ∫⁻ x, ENNReal.ofReal (klFun (P.rnDeriv Q x).toReal) ∂Q
      ≤ ∫⁻ x, ENNReal.ofReal ((P.rnDeriv Q x).toReal * Real.log (1 / a) + 1 -
          (P.rnDeriv Q x).toReal) ∂Q := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt] with x hx
        exact ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal (∫ x, ((P.rnDeriv Q x).toReal * Real.log (1 / a) + 1 -
          (P.rnDeriv Q x).toReal) ∂Q) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint2]
        filter_upwards [hpt] with x hx
        exact (klFun_nonneg ENNReal.toReal_nonneg).trans hx
    _ = ENNReal.ofReal (Real.log (1 / a)) := by
        congr 1
        rw [integral_sub hI1 hint, integral_add hI0 (integrable_const _), integral_mul_const,
          Measure.integral_toReal_rnDeriv hPQ, probReal_univ, integral_const, probReal_univ]
        simp

end LogBound

section Entropy

variable {X : Type*} [MeasurableSpace X] (ν D : Measure X) [IsProbabilityMeasure ν]
  [IsProbabilityMeasure D] (hD : D ≪ ν) {a b : ℝ≥0} (hab : a + b = 1) (ha : 0 < a) (hb : 0 < b)
include hD hab

omit ha hb in
/-- **Upper entropy modulus along the bridge**: `KL(a ν + b D ‖ ν) ≤ b KL(D ‖ ν)`. -/
theorem klDiv_mixture_self_le :
    klDiv (a • ν + b • D) ν ≤ (b : ℝ≥0∞) * klDiv D ν := by
  have := klDiv_mixture_le ν ν D Measure.AbsolutelyContinuous.rfl hD hab
  rwa [klDiv_self, mul_zero, zero_add] at this

include ha hb in
/-- **Lower entropy modulus along the bridge**:
`b KL(D ‖ ν) ≤ KL(a ν + b D ‖ ν) + h₂(a, b)` for finite `KL(D ‖ ν)`. -/
theorem toReal_klDiv_mixture_ge (hfin : klDiv D ν ≠ ⊤) :
    (b : ℝ) * (klDiv D ν).toReal ≤ (klDiv (a • ν + b • D) ν).toReal + binEnt a b := by
  have hQP := isProbabilityMeasure_mixture ν D hab
  have hcomp := klDiv_mixture_compensation ν ν D Measure.AbsolutelyContinuous.rfl hD hab ha.ne'
    hb.ne'
  rw [klDiv_self, mul_zero, zero_add] at hcomp
  have hab' : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have ha1 : (a : ℝ) ≤ 1 := by linarith [NNReal.coe_nonneg b]
  have hb1 : (b : ℝ) ≤ 1 := by linarith [NNReal.coe_nonneg a]
  have h1 : klDiv ν (a • ν + b • D) ≤ ENNReal.ofReal (Real.log (1 / a)) :=
    klDiv_le_log_of_smul_le ν _ ha (Measure.le_add_right le_rfl)
  have h2 : klDiv D (a • ν + b • D) ≤ ENNReal.ofReal (Real.log (1 / b)) :=
    klDiv_le_log_of_smul_le D _ hb (Measure.le_add_left le_rfl)
  have hQfin : klDiv (a • ν + b • D) ν ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
      (klDiv_mixture_self_le ν D hD hab)
  have hfin1 : klDiv ν (a • ν + b • D) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hfin2 : klDiv D (a • ν + b • D) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
  have h1' : (klDiv ν (a • ν + b • D)).toReal ≤ Real.log (1 / a) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (Real.log_nonneg (one_le_one_div ha' ha1))] at this
  have h2' : (klDiv D (a • ν + b • D)).toReal ≤ Real.log (1 / b) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal (Real.log_nonneg (one_le_one_div hb' hb1))] at this
  have hreal := congrArg ENNReal.toReal hcomp
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_add (ENNReal.add_ne_top.2
    ⟨hQfin, ENNReal.mul_ne_top ENNReal.coe_ne_top hfin1⟩) (ENNReal.mul_ne_top ENNReal.coe_ne_top
    hfin2), ENNReal.toReal_add hQfin (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin1),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
  unfold binEnt
  nlinarith [mul_le_mul_of_nonneg_left h1' ha'.le, mul_le_mul_of_nonneg_left h2' hb'.le]

end Entropy

section AffineLift

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure X)
  [IsProbabilityMeasure ν] (S : X → Y) (hS : Measurable S)
include hS

/-- **The lift is affine**: `(a D₀ + b D₁)↑ = a D₀↑ + b D₁↑`. -/
theorem statisticLift_mixture (D₀ D₁ : Measure X) [IsProbabilityMeasure D₀]
    [IsProbabilityMeasure D₁] (a b : ℝ≥0) :
    statisticLift ν (a • D₀ + b • D₁) S = a • statisticLift ν D₀ S + b • statisticLift ν D₁ S := by
  have hm₀ := measurable_liftDensity ν D₀ S hS
  have hm₁ := measurable_liftDensity ν D₁ S hS
  have hmap : (a • D₀ + b • D₁).map S = a • D₀.map S + b • D₁.map S := by
    rw [Measure.map_add _ _ hS, Measure.map_smul, Measure.map_smul]
  have hrn : (a • D₀.map S + b • D₁.map S).rnDeriv (ν.map S) =ᵐ[ν.map S]
      fun y ↦ (a : ℝ≥0∞) * (D₀.map S).rnDeriv (ν.map S) y +
        (b : ℝ≥0∞) * (D₁.map S).rnDeriv (ν.map S) y := by
    filter_upwards [Measure.rnDeriv_add' (a • D₀.map S) (b • D₁.map S) (ν.map S),
      Measure.rnDeriv_smul_left' (D₀.map S) (ν.map S) a,
      Measure.rnDeriv_smul_left' (D₁.map S) (ν.map S) b] with y hy1 hy2 hy3
    rw [hy1, Pi.add_apply, hy2, hy3]
    rfl
  have hae : (fun x ↦ (a • D₀ + b • D₁).map S |>.rnDeriv (ν.map S) (S x)) =ᵐ[ν]
      fun x ↦ (a : ℝ≥0∞) * (D₀.map S).rnDeriv (ν.map S) (S x) +
        (b : ℝ≥0∞) * (D₁.map S).rnDeriv (ν.map S) (S x) := by
    rw [hmap]
    exact ae_of_ae_map hS.aemeasurable hrn
  unfold statisticLift
  have e : (fun x ↦ (a : ℝ≥0∞) * (D₀.map S).rnDeriv (ν.map S) (S x) +
      (b : ℝ≥0∞) * (D₁.map S).rnDeriv (ν.map S) (S x)) =
      ((a : ℝ≥0∞) • fun x ↦ (D₀.map S).rnDeriv (ν.map S) (S x)) +
        (b : ℝ≥0∞) • fun x ↦ (D₁.map S).rnDeriv (ν.map S) (S x) := rfl
  rw [withDensity_congr_ae hae, e, withDensity_add_left (hm₀.const_smul _),
    withDensity_smul' _ _ ENNReal.coe_ne_top, withDensity_smul' _ _ ENNReal.coe_ne_top]
  rfl

/-- The featureless law is its own lift. -/
theorem statisticLift_self : statisticLift ν ν S = ν := by
  unfold statisticLift
  have hae : (fun x ↦ (ν.map S).rnDeriv (ν.map S) (S x)) =ᵐ[ν] fun _ ↦ 1 :=
    ae_of_ae_map hS.aemeasurable (Measure.rnDeriv_self (ν.map S))
  rw [withDensity_congr_ae hae]
  exact withDensity_one

/-- **The lift of the bridge**: `(a ν + b D)↑ = a ν + b D↑`. -/
theorem statisticLift_bridge (D : Measure X) [IsProbabilityMeasure D] (a b : ℝ≥0) :
    statisticLift ν (a • ν + b • D) S = a • ν + b • statisticLift ν D S := by
  rw [statisticLift_mixture ν S hS ν D a b, statisticLift_self ν S hS]

end AffineLift

section Fibre

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : X → Y) (hS : Measurable S) (hD : D ≪ ν)
  {a b : ℝ≥0} (hab : a + b = 1) (ha : 0 < a) (hb : 0 < b) (hfin : klDiv D ν ≠ ⊤)
include hS hD hab ha hb hfin

omit ha hb in
/-- The fibre information along the bridge is the entropy of the bridge minus the entropy of the
lifted bridge. -/
theorem toReal_fibreInformation_bridge_eq :
    (klDiv (a • ν + b • D) (statisticLift ν (a • ν + b • D) S)).toReal =
      (klDiv (a • ν + b • D) ν).toReal - (klDiv (a • ν + b • statisticLift ν D S) ν).toReal := by
  have hQP := isProbabilityMeasure_mixture ν D hab
  have hQν : a • ν + b • D ≪ ν :=
    mixture_absolutelyContinuous ν Measure.AbsolutelyContinuous.rfl hD a b
  have hQfin : klDiv (a • ν + b • D) ν ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
      (klDiv_mixture_self_le ν D hD hab)
  have hbase := klDiv_eq_klDiv_statisticLift_add_map ν (a • ν + b • D) S hS hQν hQfin
  have hlift := klDiv_statisticLift_eq_map ν (a • ν + b • D) S hS hQν
  rw [statisticLift_bridge ν S hS D a b] at hbase hlift
  have hmapfin : klDiv ((a • ν + b • D).map S) (ν.map S) ≠ ⊤ :=
    ne_top_of_le_ne_top hQfin (klDiv_map_le (μ := a • ν + b • D) (ν := ν) hS)
  have hLfin : klDiv (a • ν + b • D) (a • ν + b • statisticLift ν D S) ≠ ⊤ := by
    intro h
    rw [h, top_add] at hbase
    exact hQfin hbase
  rw [statisticLift_bridge ν S hS D a b, hbase, hlift, ENNReal.toReal_add hLfin hmapfin]
  ring

/-- **Fibre information along the bridge, upper modulus**: `L_s ≤ b L₁ + h₂(a, b)`. -/
theorem fibreInformation_bridge_le :
    (klDiv (a • ν + b • D) (statisticLift ν (a • ν + b • D) S)).toReal ≤
      (b : ℝ) * (klDiv D (statisticLift ν D S)).toReal + binEnt a b := by
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  have hLν := statisticLift_absolutelyContinuous ν D S
  have hbase := klDiv_eq_klDiv_statisticLift_add_map ν D S hS hD hfin
  have hlift := klDiv_statisticLift_eq_map ν D S hS hD
  have hmapfin : klDiv (D.map S) (ν.map S) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (klDiv_map_le (μ := D) (ν := ν) hS)
  have hLfin : klDiv D (statisticLift ν D S) ≠ ⊤ := by
    intro h
    rw [h, top_add] at hbase
    exact hfin hbase
  have hKfin : klDiv (statisticLift ν D S) ν ≠ ⊤ := by rw [hlift]; exact hmapfin
  have hL1 : (klDiv D (statisticLift ν D S)).toReal =
      (klDiv D ν).toReal - (klDiv (statisticLift ν D S) ν).toReal := by
    rw [hbase, hlift, ENNReal.toReal_add hLfin hmapfin]
    ring
  have hQfin : klDiv (a • ν + b • D) ν ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
      (klDiv_mixture_self_le ν D hD hab)
  have hup : (klDiv (a • ν + b • D) ν).toReal ≤ (b : ℝ) * (klDiv D ν).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
      (klDiv_mixture_self_le ν D hD hab)
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  have hlow := toReal_klDiv_mixture_ge ν (statisticLift ν D S) hLν hab ha hb hKfin
  rw [toReal_fibreInformation_bridge_eq ν D S hS hD hab hfin, hL1]
  linarith

/-- **Fibre information along the bridge, lower modulus**: `b L₁ − h₂(a, b) ≤ L_s`. -/
theorem fibreInformation_bridge_ge :
    (b : ℝ) * (klDiv D (statisticLift ν D S)).toReal - binEnt a b ≤
      (klDiv (a • ν + b • D) (statisticLift ν (a • ν + b • D) S)).toReal := by
  have hPL := isProbabilityMeasure_statisticLift ν D S hS hD
  have hLν := statisticLift_absolutelyContinuous ν D S
  have hbase := klDiv_eq_klDiv_statisticLift_add_map ν D S hS hD hfin
  have hlift := klDiv_statisticLift_eq_map ν D S hS hD
  have hmapfin : klDiv (D.map S) (ν.map S) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (klDiv_map_le (μ := D) (ν := ν) hS)
  have hLfin : klDiv D (statisticLift ν D S) ≠ ⊤ := by
    intro h
    rw [h, top_add] at hbase
    exact hfin hbase
  have hKfin : klDiv (statisticLift ν D S) ν ≠ ⊤ := by rw [hlift]; exact hmapfin
  have hL1 : (klDiv D (statisticLift ν D S)).toReal =
      (klDiv D ν).toReal - (klDiv (statisticLift ν D S) ν).toReal := by
    rw [hbase, hlift, ENNReal.toReal_add hLfin hmapfin]
    ring
  have hlow := toReal_klDiv_mixture_ge ν D hD hab ha hb hfin
  have hup : (klDiv (a • ν + b • statisticLift ν D S) ν).toReal ≤
      (b : ℝ) * (klDiv (statisticLift ν D S) ν).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hKfin)
      (klDiv_mixture_self_le ν (statisticLift ν D S) hLν hab)
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  rw [toReal_fibreInformation_bridge_eq ν D S hS hD hab hfin, hL1]
  linarith

end Fibre

section Residual

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : J → X → ℝ) (hD : D ≪ ν)
  {a b : ℝ≥0} (hab : a + b = 1) (ha : 0 < a) (hb : 0 < b) (hfin : klDiv D ν ≠ ⊤)
include hD hab ha hb hfin

/-- **The modulus of the invisible information along the bridge**: with
`R_s = KL(D_s ‖ ν) − 𝓘(M_s)` and `δ𝓘 = 𝓘(M_D) − 𝓘(M_s)`,
`a H − δ𝓘 ≤ R₁ − R_s ≤ a H + h₂(a, b) − δ𝓘`. -/
theorem invisibleInformation_bridge_modulus :
    (a : ℝ) * (klDiv D ν).toReal -
        ((genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal -
          (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal) ≤
      ((klDiv D ν).toReal - (genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal) -
        ((klDiv (a • ν + b • D) ν).toReal -
          (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal) ∧
    ((klDiv D ν).toReal - (genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal) -
        ((klDiv (a • ν + b • D) ν).toReal -
          (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal) ≤
      (a : ℝ) * (klDiv D ν).toReal + binEnt a b -
        ((genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal -
          (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal) := by
  have hab' : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have hup : (klDiv (a • ν + b • D) ν).toReal ≤ (b : ℝ) * (klDiv D ν).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
      (klDiv_mixture_self_le ν D hD hab)
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  have hlow := toReal_klDiv_mixture_ge ν D hD hab ha hb hfin
  have hAH : (a : ℝ) * (klDiv D ν).toReal = (klDiv D ν).toReal - (b : ℝ) * (klDiv D ν).toReal := by
    rw [show (a : ℝ) = 1 - b by linarith]
    ring
  constructor <;> linarith

end Residual

end Laplace.Multi
