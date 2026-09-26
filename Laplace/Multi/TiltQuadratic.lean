/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RegressionProjection
import Laplace.Multi.ThermalTransport
import Laplace.Multi.CubicResponse

/-!
# The information along a bounded tilt is quadratic to leading order

For a bounded `f` and the tilts `ν_t = ν.tilted (t f)`,

  `KL(ν_t ‖ ν) / t² → Var_ν f / 2`  as `t → 0`         (`tendsto_klDiv_tilted_div_sq`),

so `KL(ν_t ‖ ν) = (t²/2) Var_ν f + o(t²)` (`klDiv_tilted_isLittleO_sq`), and `Var_ν f` is the
squared `L²(ν)`-norm of the centred score `f − E_ν f` (`norm_sq_toLp_sub_mean`). The proof is
L'Hôpital on
`d/dt KL(ν_t ‖ ν) = t Var_{ν_t} f` with the variance continuous in `t`. This is the first of the
four quadratic expansions that identify the nonlinear information split with the three-way
Pythagoras of `NestedProjections`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- **The information along a bounded tilt is quadratic at leading order**:
`KL(ν_t ‖ ν) / t² → Var_ν f / 2`. -/
theorem tendsto_klDiv_tilted_div_sq {f : X → ℝ} (hf : Bdd f) :
    Tendsto (fun t ↦ (klDiv (ν.tilted (fun x ↦ t * f x)) ν).toReal / t ^ 2) (𝓝[≠] 0)
      (𝓝 (lawCov ν f f / 2)) := by
  have hK : ∀ t : ℝ, HasDerivAt (fun s ↦ (klDiv (ν.tilted (fun x ↦ s * f x)) ν).toReal)
      (t * lawCov (ν.tilted (fun x ↦ t * f x)) f f) t := fun t ↦
    hasDerivAt_klDiv_tilted_toReal ν hf t
  have hV : ContinuousAt (fun t ↦ lawCov (ν.tilted (fun x ↦ t * f x)) f f) 0 :=
    (hasDerivAt_var_tilted ν hf 0).continuousAt
  have hK0 : (klDiv (ν.tilted (fun x ↦ (0 : ℝ) * f x)) ν).toReal = 0 := by
    rw [tilted_zero_mul, klDiv_self, ENNReal.toReal_zero]
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := fun t ↦ t * lawCov (ν.tilted (fun x ↦ t * f x)) f f)
    (g' := fun t ↦ 2 * t) (Eventually.of_forall hK)
    (Eventually.of_forall fun t ↦ by simpa using hasDerivAt_pow 2 t) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero two_ne_zero ht
  · have := (hK 0).continuousAt.tendsto
    rw [hK0] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have : Tendsto (fun t : ℝ ↦ t ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto 0
    rw [zero_pow two_ne_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have h : Tendsto (fun t ↦ lawCov (ν.tilted (fun x ↦ t * f x)) f f / 2) (𝓝[≠] 0)
        (𝓝 (lawCov (ν.tilted (fun x ↦ (0 : ℝ) * f x)) f f / 2)) :=
      (hV.tendsto.div_const 2).mono_left nhdsWithin_le_nhds
    rw [tilted_zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    field_simp

/-- `KL(ν_t ‖ ν) = (t²/2) Var_ν f + o(t²)`. -/
theorem klDiv_tilted_isLittleO_sq {f : X → ℝ} (hf : Bdd f) :
    (fun t ↦ (klDiv (ν.tilted (fun x ↦ t * f x)) ν).toReal - t ^ 2 / 2 * lawCov ν f f)
      =o[𝓝[≠] 0] fun t ↦ t ^ 2 := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h := (tendsto_klDiv_tilted_div_sq ν hf).sub (tendsto_const_nhds (x := lawCov ν f f / 2))
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    rw [sub_div]
    congr 1
    field_simp
  · filter_upwards [self_mem_nhdsWithin] with t ht h
    exact absurd h (pow_ne_zero 2 ht)

omit [Nonempty X] in
/-- The variance is the squared `L²` norm of the centred observable. -/
theorem norm_sq_toLp_sub_mean {f : X → ℝ} (hf : Bdd f) :
    ‖(memLp_two_bdd ν hf).toLp f - (∫ x, f x ∂ν) • oneLp ν‖ ^ 2 = lawCov ν f f := by
  rw [← real_inner_self_eq_norm_sq]
  unfold oneLp
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, inner_toLp_toLp,
    inner_toLp_toLp, inner_toLp_toLp, inner_toLp_toLp]
  simp only [lawCov, mul_one, one_mul, integral_const, probReal_univ, smul_eq_mul]
  ring

end Laplace.Multi
