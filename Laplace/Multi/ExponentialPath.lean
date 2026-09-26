/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ConditionalVariational
import Laplace.Multi.ThermalTransport
import Laplace.Multi.CubicResponse

/-!
# The exponential path and the four-path comparison

Between the featureless posterior `ν` and a data law `D = dν` with bounded positive density there
are two canonical paths in the full simplex: the mixture bridge `D_s = (1−s)ν + sD` and the
exponential path `E_s = d^s ν / ∫ d^s dν = ν.tilted (s log d)`. They have the same endpoints but
different response schedules, and the same Fisher energy:

`∫₀¹ k_d(s) ds = ∫₀¹ Var_{E_s}(log d) ds = KL(D‖ν) + KL(ν‖D)`

(`integral_mixSpeed_eq_integral_var_expPath`). The exponential-path energy is the integral of
`d/ds E_{E_s} log d = Var_{E_s} log d`, evaluated between `E_ν log d` and `E_D log d`, whose
difference is the symmetrised divergence. The same pair of identities holds between `ν` and the
statistic lift
`D↑ = aν`, and the conditional Fisher loss `k_a ≤ k_d` gives the contraction of the symmetrised
divergence under conditioning, `KL(D↑‖ν) + KL(ν‖D↑) ≤ KL(D‖ν) + KL(ν‖D)`. Every path's Fisher
length is bounded by the square root of its energy
(`sq_setIntegral_sqrt_le_setIntegral_Ioo`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Length

/-- **Length is bounded by energy** on the unit interval: `(∫₀¹ √g)² ≤ ∫₀¹ g` for `g ≥ 0`
there. -/
theorem sq_setIntegral_sqrt_le_setIntegral_Ioo {g : ℝ → ℝ} (hint : IntegrableOn g (Ioo (0 : ℝ) 1))
    (hg0 : ∀ s ∈ Ioo (0 : ℝ) 1, 0 ≤ g s) :
    (∫ s in Ioo (0 : ℝ) 1, Real.sqrt (g s)) ^ 2 ≤ ∫ s in Ioo (0 : ℝ) 1, g s := by
  have hae : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ g s :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hg0)
  have hmeas : AEStronglyMeasurable (fun s ↦ Real.sqrt (g s)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hint.aestronglyMeasurable
  have hf : MemLp (fun s ↦ Real.sqrt (g s)) (ENNReal.ofReal 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq hmeas]
    refine hint.congr ?_
    filter_upwards [hae] with s hs
    rw [Real.sq_sqrt hs]
  have hg : MemLp (fun _ : ℝ ↦ (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    memLp_const 1
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun s ↦ Real.sqrt_nonneg _) (Eventually.of_forall fun _ ↦ zero_le_one)
    hf hg
  simp only [mul_one, Real.rpow_two, one_pow] at hH
  have hone : ∫ _s in Ioo (0 : ℝ) 1, (1 : ℝ) = 1 := by
    rw [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal zero_le_one, one_smul]
  have hsq : ∫ s in Ioo (0 : ℝ) 1, Real.sqrt (g s) ^ 2 = ∫ s in Ioo (0 : ℝ) 1, g s := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with s hs
    rw [Real.sq_sqrt hs]
  rw [hsq, hone, Real.one_rpow, mul_one] at hH
  have hE0 : 0 ≤ ∫ s in Ioo (0 : ℝ) 1, g s := integral_nonneg_of_ae hae
  have hL0 : 0 ≤ ∫ s in Ioo (0 : ℝ) 1, Real.sqrt (g s) :=
    integral_nonneg fun s ↦ Real.sqrt_nonneg _
  calc (∫ s in Ioo (0 : ℝ) 1, Real.sqrt (g s)) ^ 2
      ≤ ((∫ s in Ioo (0 : ℝ) 1, g s) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left₀ hL0 hH 2
    _ = ∫ s in Ioo (0 : ℝ) 1, g s := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE0]
        norm_num

end Length

section ExpPath

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The exponential path `E_s = ν.tilted (s f)` from `ν` to `ν.tilted f`. -/
noncomputable def expPath (f : X → ℝ) (s : ℝ) : Measure X := ν.tilted fun x ↦ s * f x

omit [Nonempty X] in
theorem expPath_zero (f : X → ℝ) : expPath ν f 0 = ν := tilted_zero_mul ν f

omit [Nonempty X] [IsProbabilityMeasure ν] in
theorem expPath_one (f : X → ℝ) : expPath ν f 1 = ν.tilted f := by
  unfold expPath
  simp only [one_mul]

/-- **Equal energies along the exponential path**:
`∫₀¹ Var_{E_s} f ds = KL(ν.tilted f ‖ ν) + KL(ν ‖ ν.tilted f)`. -/
theorem integral_var_expPath_eq_symm_klDiv {f : X → ℝ} (hf : Bdd f) :
    ∫ s in (0 : ℝ)..1, lawCov (expPath ν f s) f f =
      (klDiv (ν.tilted f) ν).toReal + (klDiv ν (ν.tilted f)).toReal := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ ∫ x, f x ∂expPath ν f s)
      (lawCov (expPath ν f s) f f) s := fun s _ ↦ by
    have h := hasDerivAt_integral_tilted ν hf hf s
    unfold expPath lawCov
    exact h
  have hint : IntervalIntegrable (fun s ↦ lawCov (expPath ν f s) f f) volume 0 1 :=
    ContinuousOn.intervalIntegrable fun s _ ↦
      (hasDerivAt_var_tilted ν hf s).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, expPath_one, expPath_zero]
  have hself : klDiv ν ν ≠ ⊤ := by
    rw [klDiv_self]
    exact ENNReal.zero_ne_top
  have hllr : Integrable (llr ν ν) ν := (klDiv_ne_top_iff.1 hself).2
  have hDV := integral_sub_log_le_toReal_klDiv ν ν (Measure.AbsolutelyContinuous.refl ν) hllr hf
  rw [klDiv_self, ENNReal.toReal_zero] at hDV
  rw [klDiv_tilted_eq ν hf, ENNReal.toReal_ofReal (integral_sub_log_nonneg ν hf),
    klDiv_tilted_right_eq ν ν (Measure.AbsolutelyContinuous.refl ν) hself hf, klDiv_self,
    ENNReal.toReal_zero, zero_sub, ENNReal.toReal_ofReal (by linarith)]
  ring

end ExpPath

section FullSimplex

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]
  {d : X → ℝ} (hd : Measurable d) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ d x) (hC : ∀ x, d x ≤ C)
  (hnorm : ∫ x, d x ∂ν = 1)
include hd hc0 hc hC hnorm

omit [Nonempty X] hnorm in
theorem bdd_log_of_bounds : Bdd fun x ↦ Real.log (d x) :=
  ⟨hd.log, _, fun x ↦ abs_log_le_of_mem hc0 (hc x) (hC x)⟩

omit [Nonempty X] [IsProbabilityMeasure ν] hd hC in
theorem expPath_log_one : expPath ν (fun x ↦ Real.log (d x)) 1 = densLaw ν d := by
  rw [expPath_one, densLaw_eq_tilted_log ν (fun x ↦ lt_of_lt_of_le hc0 (hc x)) hnorm]

/-- **Equal energies of the mixture and exponential paths from `ν` to `D`**:
`∫₀¹ k_d = ∫₀¹ Var_{E_s}(log d) = KL(D‖ν) + KL(ν‖D)`. -/
theorem integral_mixSpeed_eq_integral_var_expPath :
    ∫ s in (0 : ℝ)..1, mixSpeed ν d s =
      ∫ s in (0 : ℝ)..1, lawCov (expPath ν (fun x ↦ Real.log (d x)) s)
        (fun x ↦ Real.log (d x)) (fun x ↦ Real.log (d x)) := by
  rw [integral_mixSpeed_eq_symm_klDiv ν hd hc0 hc hC,
    integral_var_expPath_eq_symm_klDiv ν (bdd_log_of_bounds hd hc0 hc hC),
    ← densLaw_eq_tilted_log ν (fun x ↦ lt_of_lt_of_le hc0 (hc x)) hnorm]

omit [Nonempty X] [IsProbabilityMeasure ν] hd hC hnorm in
theorem mixSpeed_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ mixSpeed ν d s := by
  unfold mixSpeed
  refine integral_nonneg fun x ↦ ?_
  unfold klKernel
  exact div_nonneg (sq_nonneg _) (klKernel_denom_pos (lt_of_lt_of_le hc0 (hc x)) hs0 hs1).le

omit [Nonempty X] hnorm in
theorem integrableOn_mixSpeed_Ioo : IntegrableOn (mixSpeed ν d) (Ioo (0 : ℝ) 1) := by
  refine Integrable.of_bound (measurable_mixSpeed ν hd).aestronglyMeasurable
    ((C + 1) ^ 2 / min 1 c) ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun w hw ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_mixSpeed_le ν hc0 hc hC hw.1.le hw.2.le

omit [Nonempty X] hnorm in
/-- **Length versus energy for the mixture bridge**: `(∫₀¹ √k_d)² ≤ KL(D‖ν) + KL(ν‖D)`. -/
theorem sq_integral_sqrt_mixSpeed_le_symm_klDiv :
    (∫ s in Ioo (0 : ℝ) 1, Real.sqrt (mixSpeed ν d s)) ^ 2 ≤
      (klDiv (densLaw ν d) ν).toReal + (klDiv ν (densLaw ν d)).toReal := by
  rw [← integral_mixSpeed_eq_symm_klDiv ν hd hc0 hc hC, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  exact sq_setIntegral_sqrt_le_setIntegral_Ioo (integrableOn_mixSpeed_Ioo ν hd hc0 hc hC) fun s hs ↦
    mixSpeed_nonneg ν hc0 hc hs.1.le hs.2.le

end FullSimplex

section Lift

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {d : X → ℝ} (hd : Measurable d) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ d x) (hC : ∀ x, d x ≤ C)
  (hnorm : ∫ x, d x ∂ν = 1) {a : X → ℝ} (ham : Measurable[statSigma S] a) (hac : ∀ x, c ≤ a x)
  (haC : ∀ x, a x ≤ C) (ha : a =ᵐ[ν] ν[d | statSigma S])
include hS hd hc0 hc hC hnorm ham hac haC ha

omit hd hc hC in
/-- **Equal energies of the mixture and exponential paths from `ν` to the lift `D↑`.** -/
theorem integral_mixSpeed_condDens_eq_integral_var_expPath :
    ∫ s in (0 : ℝ)..1, mixSpeed ν a s =
      ∫ s in (0 : ℝ)..1, lawCov (expPath ν (fun x ↦ Real.log (a x)) s)
        (fun x ↦ Real.log (a x)) (fun x ↦ Real.log (a x)) :=
  integral_mixSpeed_eq_integral_var_expPath ν (ham.mono (statSigma_le hS) le_rfl) hc0 hac haC
    (integral_condDens hS ν hnorm ha)

omit [Nonempty X] in
/-- **Conditioning contracts the symmetrised divergence**:
`KL(D↑‖ν) + KL(ν‖D↑) ≤ KL(D‖ν) + KL(ν‖D)`, from the pointwise Fisher loss `k_a ≤ k_d`. -/
theorem symm_klDiv_statisticLift_le :
    (klDiv (statisticLift ν (densLaw ν d) (statPoint S)) ν).toReal +
        (klDiv ν (statisticLift ν (densLaw ν d) (statPoint S))).toReal ≤
      (klDiv (densLaw ν d) ν).toReal + (klDiv ν (densLaw ν d)).toReal := by
  have ham' : Measurable a := ham.mono (statSigma_le hS) le_rfl
  rw [statisticLift_densLaw_eq_condDens hS ν hd hc0 hc hC hnorm ha,
    ← integral_mixSpeed_eq_symm_klDiv ν hd hc0 hc hC,
    ← integral_mixSpeed_eq_symm_klDiv ν ham' hc0 hac haC]
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun s hs ↦
    mixSpeed_condDens_le hS ν hd hc0 hc hC ham hac haC ha hs.1 hs.2
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (measurable_mixSpeed ν ham').aestronglyMeasurable
      ((C + 1) ^ 2 / min 1 c) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun w hw ↦ by
      rw [Real.norm_eq_abs]; exact abs_mixSpeed_le ν hc0 hac haC hw.1.le hw.2
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (measurable_mixSpeed ν hd).aestronglyMeasurable
      ((C + 1) ^ 2 / min 1 c) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun w hw ↦ by
      rw [Real.norm_eq_abs]; exact abs_mixSpeed_le ν hc0 hc hC hw.1.le hw.2

end Lift

end Laplace.Multi
