/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherSpeedForm
import Laplace.Multi.FlatC1Paths

/-!
# Flat `C¹` paths in the direction space and their Fisher length

A `FisherPath S ν x y` is a globally `C¹` path in the direction space `W = dirSpan ν 1 S` from `x`
to `y` with continuous velocity vanishing at both endpoints. Its Fisher length is
`∫₀¹ F(γ_t, γ'_t) dt` with `F = fisherNorm`. This module provides the three constructions the
intrinsic distance needs: flattening of an arbitrary `C¹` path (length-preserving, by the
smoothstep change of variables), so that segments are admissible; reversal (length-preserving);
and concatenation (length-additive).
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Path

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ) (ν : Measure X)

/-- A flat `C¹` path in the direction space from `x` to `y`. -/
structure FisherPath (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) where
  /-- The path. -/
  toFun : ℝ → dirSpan ν (fun _ ↦ (1 : ℝ)) S
  /-- Its velocity. -/
  vel : ℝ → dirSpan ν (fun _ ↦ (1 : ℝ)) S
  hasDerivAt : ∀ t, HasDerivAt toFun (vel t) t
  continuous_vel : Continuous vel
  source : toFun 0 = x
  target : toFun 1 = y
  vel_zero : vel 0 = 0
  vel_one : vel 1 = 0

variable {S ν}

namespace FisherPath

variable {x y z : dirSpan ν (fun _ ↦ (1 : ℝ)) S}

/-- The Fisher length `∫₀¹ F(γ_t, γ'_t) dt`. -/
noncomputable def length (p : FisherPath S ν x y) : ℝ :=
  ∫ t in (0 : ℝ)..1, fisherNorm S ν (p.toFun t : J → ℝ) (p.vel t : J → ℝ)

set_option linter.unusedFintypeInType false in
theorem continuous_toFun (p : FisherPath S ν x y) : Continuous p.toFun :=
  continuous_iff_continuousAt.2 fun t ↦ (p.hasDerivAt t).continuousAt

/-- The constant path. -/
def const (x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : FisherPath S ν x x where
  toFun _ := x
  vel _ := 0
  hasDerivAt t := hasDerivAt_const t x
  continuous_vel := continuous_const
  source := rfl
  target := rfl
  vel_zero := rfl
  vel_one := rfl

/-- The flattening of a `C¹` path. -/
noncomputable def flat {γ γ' : ℝ → dirSpan ν (fun _ ↦ (1 : ℝ)) S}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') (h0 : γ 0 = x) (h1 : γ 1 = y) :
    FisherPath S ν x y where
  toFun t := γ (smoothStep t)
  vel t := smoothStepDeriv t • γ' (smoothStep t)
  hasDerivAt t := hasDerivAt_comp_smoothStep hγ t
  continuous_vel := continuous_smoothStepDeriv_smul hγ'
  source := by rw [smoothStep_zero, h0]
  target := by rw [smoothStep_one, h1]
  vel_zero := by simp [smoothStepDeriv_zero]
  vel_one := by simp [smoothStepDeriv_one]

/-- The reversed path. -/
noncomputable def rev (p : FisherPath S ν x y) : FisherPath S ν y x where
  toFun t := p.toFun (1 - t)
  vel t := -p.vel (1 - t)
  hasDerivAt t := hasDerivAt_rev p.hasDerivAt t
  continuous_vel := (p.continuous_vel.comp (continuous_const.sub continuous_id)).neg
  source := by simp [p.target]
  target := by simp [p.source]
  vel_zero := by simp [p.vel_one]
  vel_one := by simp [p.vel_zero]

/-- The concatenation of two paths. -/
noncomputable def cat (p : FisherPath S ν x y) (q : FisherPath S ν y z) : FisherPath S ν x z where
  toFun := catPath p.toFun q.toFun
  vel := catVel p.vel q.vel
  hasDerivAt := hasDerivAt_catPath p.hasDerivAt q.hasDerivAt (by rw [p.target, q.source])
    p.vel_one q.vel_zero
  continuous_vel := continuous_catVel p.continuous_vel q.continuous_vel p.vel_one q.vel_zero
  source := by rw [catPath_zero, p.source]
  target := by rw [catPath_one, q.target]
  vel_zero := by rw [catVel_zero, p.vel_zero, smul_zero]
  vel_one := by rw [catVel_one, q.vel_one, smul_zero]

/-- The flattened segment from `x` to `y`. -/
noncomputable def segment (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : FisherPath S ν x y :=
  flat (γ := fun t ↦ x + t • (y - x)) (γ' := fun _ ↦ y - x)
    (fun t ↦ by simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x)
    continuous_const (by simp) (by simp)

end FisherPath

end Path

section Length

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

namespace FisherPath

variable {x y z : dirSpan ν (fun _ ↦ (1 : ℝ)) S}

theorem continuous_speed (p : FisherPath S ν x y) :
    Continuous fun t ↦ fisherNorm S ν (p.toFun t : J → ℝ) (p.vel t : J → ℝ) :=
  continuous_fisherNorm_comp hS ν (continuous_subtype_val.comp p.continuous_toFun)
    (continuous_subtype_val.comp p.continuous_vel)

omit [Nonempty X] [IsProbabilityMeasure ν] hS in
theorem length_nonneg (p : FisherPath S ν x y) : 0 ≤ p.length :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ fisherNorm_nonneg S ν _ _

theorem length_const (x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : (const x).length = 0 := by
  simp [length, const, fisherNorm_zero hS ν]

/-- **Flattening preserves the length.** -/
theorem length_flat {γ γ' : ℝ → dirSpan ν (fun _ ↦ (1 : ℝ)) S}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') (h0 : γ 0 = x) (h1 : γ 1 = y) :
    (flat hγ hγ' h0 h1).length =
      ∫ t in (0 : ℝ)..1, fisherNorm S ν (γ t : J → ℝ) (γ' t : J → ℝ) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt
  have hg : Continuous fun t ↦ fisherNorm S ν (γ t : J → ℝ) (γ' t : J → ℝ) :=
    continuous_fisherNorm_comp hS ν (continuous_subtype_val.comp hγc)
      (continuous_subtype_val.comp hγ')
  rw [← integral_comp_smoothStep hg]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [flat, Submodule.coe_smul]
  rw [fisherNorm_smul hS ν, abs_of_nonneg (smoothStepDeriv_nonneg ht.1 ht.2), mul_comm]

/-- **Reversal preserves the length.** -/
theorem length_rev (p : FisherPath S ν x y) : p.rev.length = p.length := by
  simp only [length, rev, Submodule.coe_neg]
  have e : ∀ t, fisherNorm S ν (p.toFun (1 - t) : J → ℝ) (-(p.vel (1 - t) : J → ℝ)) =
      (fun s ↦ fisherNorm S ν (p.toFun s : J → ℝ) (p.vel s : J → ℝ)) (1 - t) := fun t ↦
    fisherNorm_neg hS ν _ _
  simp_rw [e]
  rw [intervalIntegral.integral_comp_sub_left (fun s ↦ fisherNorm S ν (p.toFun s : J → ℝ)
    (p.vel s : J → ℝ)) 1]
  norm_num

/-- **Concatenation adds the lengths.** -/
theorem length_cat (p : FisherPath S ν x y) (q : FisherPath S ν y z) :
    (p.cat q).length = p.length + q.length := by
  set gp : ℝ → ℝ := fun s ↦ fisherNorm S ν (p.toFun s : J → ℝ) (p.vel s : J → ℝ) with hgp
  set gq : ℝ → ℝ := fun s ↦ fisherNorm S ν (q.toFun s : J → ℝ) (q.vel s : J → ℝ) with hgq
  have hc := (p.cat q).continuous_speed hS ν
  have h1 : ∫ t in (0 : ℝ)..1 / 2, fisherNorm S ν ((p.cat q).toFun t : J → ℝ)
      ((p.cat q).vel t : J → ℝ) = p.length := by
    calc ∫ t in (0 : ℝ)..1 / 2, fisherNorm S ν ((p.cat q).toFun t : J → ℝ) ((p.cat q).vel t : J → ℝ)
        = ∫ t in (0 : ℝ)..1 / 2, 2 * gp (2 * t) := by
          refine intervalIntegral.integral_congr fun t ht ↦ ?_
          rw [uIcc_of_le (by norm_num)] at ht
          simp only [cat, catPath_of_le _ _ ht.2, catVel_of_le _ _ ht.2, Submodule.coe_smul, hgp]
          rw [fisherNorm_smul hS ν, abs_two]
      _ = 2 * (2⁻¹ * ∫ t in (2 * 0 : ℝ)..2 * (1 / 2), gp t) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left gp
            two_ne_zero, smul_eq_mul]
      _ = p.length := by
          norm_num [length, hgp]
          ring
  have h2 : ∫ t in (1 / 2 : ℝ)..1, fisherNorm S ν ((p.cat q).toFun t : J → ℝ)
      ((p.cat q).vel t : J → ℝ) = q.length := by
    calc ∫ t in (1 / 2 : ℝ)..1, fisherNorm S ν ((p.cat q).toFun t : J → ℝ) ((p.cat q).vel t : J → ℝ)
        = ∫ t in (1 / 2 : ℝ)..1, 2 * gq (2 * t - 1) := by
          refine intervalIntegral.integral_congr fun t ht ↦ ?_
          rw [uIcc_of_le (by norm_num)] at ht
          rcases eq_or_lt_of_le ht.1 with h | h
          · rw [← h]
            simp only [cat, catPath_of_le _ _ le_rfl, catVel_of_le _ _ le_rfl, Submodule.coe_smul,
              hgq]
            rw [fisherNorm_smul hS ν, abs_two]
            norm_num [p.target, q.source, p.vel_one, q.vel_zero]
          · simp only [cat, catPath_of_lt _ _ h, catVel_of_lt _ _ h, Submodule.coe_smul, hgq]
            rw [fisherNorm_smul hS ν, abs_two]
      _ = 2 * (2⁻¹ * ∫ t in (2 * (1 / 2) - 1 : ℝ)..2 * 1 - 1, gq t) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_sub gq
            two_ne_zero, smul_eq_mul]
      _ = q.length := by
          norm_num [length, hgq]
          ring
  rw [length, ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), h1, h2]

/-- **The segment bound**: `L(segment x y) ≤ K ‖y − x‖` for a global Fisher-norm bound `K`. -/
theorem length_segment_le {K : ℝ} (hK : ∀ θ w : J → ℝ, fisherNorm S ν θ w ≤ K * ‖w‖)
    (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : (segment x y).length ≤ K * ‖y - x‖ := by
  rw [segment, length_flat hS ν]
  calc ∫ t in (0 : ℝ)..1, fisherNorm S ν ((x + t • (y - x) : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
        ((y - x : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ)
      ≤ ∫ _ in (0 : ℝ)..1, K * ‖y - x‖ := by
        refine intervalIntegral.integral_mono_on zero_le_one ?_ (by simp) fun t _ ↦ ?_
        · exact (continuous_fisherNorm_comp hS ν (continuous_subtype_val.comp (by fun_prop))
            continuous_const).intervalIntegrable _ _
        · exact (hK _ _).trans (by rw [Submodule.coe_norm])
    _ = K * ‖y - x‖ := by simp

end FisherPath

end Length

end Laplace.Multi
