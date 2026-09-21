/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.FourGon

/-!
# The 4-gon is stationary for every reweighting

Proposition 11.1 (i) of the working note *Patterning flow*: at the 4-gon with a dead unit,
every per-feature loss `ℓ_i` has vanishing gradient, so `L_h = ∑ h_i ℓ_i` is stationary for
every `h` and the checkpoint-frozen gradient-response force `(Bω)(W*) = ∑ ω_i ∇ℓ_i(W*)` is zero.

The gradient is taken in the Gateaux sense: for every direction `V`, the derivative of
`s ↦ ℓ_i(W* + sV)` at `s = 0` is zero. The only analytic input is that `z ↦ [z]_+²` is `C¹`
with derivative `2[z]_+` (`hasDerivAt_relu_sq`), which vanishes at `z = 0`; no convention for
`ReLU'(0)` is needed, exactly as the note says.
-/

namespace Laplace.Patterning

open Finset Filter Topology Asymptotics

/-- `[z]_+²` is differentiable everywhere with derivative `2[z]_+`. -/
theorem hasDerivAt_relu_sq (z : ℝ) : HasDerivAt (fun z => relu z ^ 2) (2 * relu z) z := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have h : (fun z => relu z ^ 2) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hz] with y hy
      rw [relu_of_nonpos (le_of_lt hy)]
      ring
    rw [relu_of_nonpos hz.le, mul_zero]
    exact (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq h
  · subst hz
    rw [relu_zero, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    have h : (fun h : ℝ => relu (0 + h) ^ 2 - relu 0 ^ 2 - h • (0 : ℝ)) = fun h => relu h ^ 2 := by
      funext h
      simp
    rw [h]
    refine IsBigO.trans_isLittleO ?_ (isLittleO_pow_id (n := 2) one_lt_two)
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have := relu_sq_add_relu_neg_sq h
    nlinarith [sq_nonneg (relu (-h))]
  · have h : (fun z => relu z ^ 2) =ᶠ[𝓝 z] fun y => y ^ 2 := by
      filter_upwards [Ioi_mem_nhds hz] with y hy
      rw [relu_of_nonneg (le_of_lt hy)]
    rw [relu_of_nonneg hz.le]
    refine ((hasDerivAt_pow 2 z).congr_of_eventuallyEq h).congr_deriv ?_
    simp

/-! ### Directional derivatives of the per-feature loss along `W + sV` -/

lemma hasDerivAt_coord_path (W V : Fin 5 → Fin 2 → ℝ) (j : Fin 5) (a : Fin 2) :
    HasDerivAt (fun s : ℝ => (W + s • V) j a) (V j a) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (V j a)).const_add (W j a)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp
  · simp

lemma hasDerivAt_sqNorm_path (W V : Fin 5 → Fin 2 → ℝ) (i : Fin 5) :
    HasDerivAt (fun s : ℝ => sqNorm ((W + s • V) i)) (2 * dot2 (W i) (V i)) 0 := by
  have h := ((hasDerivAt_coord_path W V i 0).pow 2).add ((hasDerivAt_coord_path W V i 1).pow 2)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [sqNorm]
  · simp [dot2]
    ring

lemma hasDerivAt_dot2_path (W V : Fin 5 → Fin 2 → ℝ) (j i : Fin 5) :
    HasDerivAt (fun s : ℝ => dot2 ((W + s • V) j) ((W + s • V) i))
      (dot2 (V j) (W i) + dot2 (W j) (V i)) 0 := by
  have h := ((hasDerivAt_coord_path W V j 0).mul (hasDerivAt_coord_path W V i 0)).add
    ((hasDerivAt_coord_path W V j 1).mul (hasDerivAt_coord_path W V i 1))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [dot2]
  · simp [dot2]
    ring

lemma hasDerivAt_relu_sq_dot2_path (W V : Fin 5 → Fin 2 → ℝ) (j i : Fin 5) :
    HasDerivAt (fun s : ℝ => relu (dot2 ((W + s • V) j) ((W + s • V) i)) ^ 2)
      (2 * relu (dot2 (W j) (W i)) * (dot2 (V j) (W i) + dot2 (W j) (V i))) 0 := by
  have h := (hasDerivAt_relu_sq (dot2 ((W + (0 : ℝ) • V) j) ((W + (0 : ℝ) • V) i))).comp 0
    (hasDerivAt_dot2_path W V j i)
  refine h.congr_deriv ?_
  simp

/-- **The Gateaux derivative of `ℓ_i`** at `W` in direction `V`. -/
theorem hasDerivAt_featureLoss_path (W V : Fin 5 → Fin 2 → ℝ) (i : Fin 5) :
    HasDerivAt (fun s : ℝ => featureLoss (W + s • V) i)
      ((1 / 3) * (2 * (1 - sqNorm (W i)) * (-(2 * dot2 (W i) (V i)))
        + ∑ j, if j = i then 0
            else 2 * relu (dot2 (W j) (W i)) * (dot2 (V j) (W i) + dot2 (W j) (V i)))) 0 := by
  unfold featureLoss
  refine HasDerivAt.const_mul _ (HasDerivAt.add ?_ ?_)
  · have h := ((hasDerivAt_sqNorm_path W V i).const_sub 1).pow 2
    refine h.congr_deriv ?_
    simp
  · refine HasDerivAt.fun_sum fun j _ => ?_
    by_cases hji : j = i
    · simp only [hji, if_true]
      exact hasDerivAt_const _ _
    · simp only [hji, if_false]
      exact hasDerivAt_relu_sq_dot2_path W V j i

/-- **Proposition 11.1 (i).** Every per-feature gradient vanishes at the 4-gon: for every
direction `V` and every feature `i`, `d/ds ℓ_i(W* + sV)|₀ = 0`. -/
theorem fourGon_featureLoss_stationary (V : Fin 5 → Fin 2 → ℝ) (i : Fin 5) :
    HasDerivAt (fun s : ℝ => featureLoss (fourGon 0 0 + s • V) i) 0 0 := by
  refine (hasDerivAt_featureLoss_path (fourGon 0 0) V i).congr_deriv ?_
  fin_cases i <;> simp [fourGon, sqNorm, dot2, Fin.sum_univ_five, relu_neg_one]

/-- The weighted loss `L_h` is stationary at the 4-gon for every reweighting `h`, so the
checkpoint-frozen force `∑ ω_i ∇ℓ_i(W*)` vanishes for every `ω`. -/
theorem fourGon_weightedLoss_stationary (h : Fin 5 → ℝ) (V : Fin 5 → Fin 2 → ℝ) :
    HasDerivAt (fun s : ℝ => weightedLoss h (fourGon 0 0 + s • V)) 0 0 := by
  unfold weightedLoss
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (fourGon_featureLoss_stationary V i).const_mul (h i)
  simpa using this

end Laplace.Patterning
