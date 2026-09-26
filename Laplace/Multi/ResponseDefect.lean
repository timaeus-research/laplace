/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BasepointCurvature
import Laplace.Multi.ThermalTransport
import Laplace.Multi.EmpiricalProjection
import Laplace.Multi.StraightPathAtlas

/-!
# The response defect along a data path

Move the data law away from the featureless law along the exponential path `ρ_t = ν.tilted(t h)`
with a bounded direction `h`, and follow its response `m_t = E_{ρ_t} S` and the response
projection `q_t = q_{m_t}`.  The **response defect** `ℰ(t) = D(ρ_t ‖ q_t)` is the information in
the data law that the response family does not represent, and the Pythagorean identity splits

  `D(ρ_t ‖ ν) = I(m_t) + ℰ(t)`   (`klDiv_tilted_eq_genRate_add_responseDefect`)

into the information carried by the response and the irreducible defect.  The defect starts at
zero with zero velocity, evolves by

  `ℰ'(t) = t Var_{ρ_t}(h) + ⟨θ(m_t), Cov_{ρ_t}(S, h)⟩`   (`hasDerivAt_responseDefect`),

and its curvature at the featureless law is the **residual variance** of the data score after
regression on the observables,

  `ℰ''(0) = Var_ν(h) − Var_ν(regressor) = Var_ν(h − regressor)`
  (`hasDerivAt_deriv_responseDefect_zero`, `deriv_deriv_responseDefect_zero_eq_residual`):

to second order the defect is `½ t² Var_ν(unexplained score)`, the part of the data movement that
the observables cannot see.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Defect

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

omit [Nonempty X] [Nonempty J] hS hh in
variable (S h) in
/-- The response defect `ℰ(t) = D(ρ_t ‖ ν) − I(E_{ρ_t} S)` along the data path
`ρ_t = ν.tilted(t h)`. -/
noncomputable def responseDefect (t : ℝ) : ℝ :=
  (klDiv (ν.tilted fun x ↦ t * h x) ν).toReal -
    (genRate ν S fun i ↦ ∫ x, S i x ∂ν.tilted fun x ↦ t * h x).toReal

omit [Nonempty X] [Nonempty J] hS in
theorem isProbabilityMeasure_dataPath (t : ℝ) :
    IsProbabilityMeasure (ν.tilted fun x ↦ t * h x) :=
  isProbabilityMeasure_tilted (integrable_exp_of_bdd ν (Bdd.const_mul t hh))

omit [Nonempty X] [Nonempty J] hS in
theorem klDiv_dataPath_ne_top (t : ℝ) : klDiv (ν.tilted fun x ↦ t * h x) ν ≠ ⊤ := by
  rw [klDiv_tilted_eq ν (Bdd.const_mul t hh)]
  exact ENNReal.ofReal_ne_top

theorem genRate_dataPath_ne_top (t : ℝ) :
    genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted fun x ↦ t * h x) ≠ ⊤ :=
  genRate_ne_top_of_mem_intrinsicInterior hS ν (mean_tilted_mem_intrinsicInterior hS ν
    (Bdd.const_mul t hh))

/-- **The response defect is the information of the data law relative to its response
projection**: `ℰ(t) = D(ρ_t ‖ q_{m_t})`. -/
theorem responseDefect_eq_klDiv (t : ℝ) :
    responseDefect S ν h t = (klDiv (ν.tilted fun x ↦ t * h x)
      (responseProjection hS ν fun i ↦ ∫ x, S i x ∂ν.tilted fun x ↦ t * h x)).toReal := by
  have hP := isProbabilityMeasure_dataPath ν hh t
  have hfin := genRate_dataPath_ne_top hS ν hh t
  have hpyth := (responseProjection_spec hS ν hfin).2.2.2 _ hP rfl
  have hle : genRate ν S (fun i ↦ ∫ x, S i x ∂ν.tilted fun x ↦ t * h x) ≤
      klDiv (ν.tilted fun x ↦ t * h x) ν := by
    rw [hpyth]
    exact le_add_self
  rw [responseDefect, ← ENNReal.toReal_sub_of_le hle (klDiv_dataPath_ne_top ν hh t)]
  congr 1
  exact (ENNReal.eq_sub_of_add_eq hfin hpyth.symm).symm

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hh in
/-- **The Pythagorean decomposition of the data information**: `D(ρ_t ‖ ν) = I(m_t) + ℰ(t)`. -/
theorem klDiv_tilted_eq_genRate_add_responseDefect (t : ℝ) :
    (klDiv (ν.tilted fun x ↦ t * h x) ν).toReal =
      (genRate ν S fun i ↦ ∫ x, S i x ∂ν.tilted fun x ↦ t * h x).toReal +
        responseDefect S ν h t := by
  rw [responseDefect]
  ring

theorem responseDefect_nonneg (t : ℝ) : 0 ≤ responseDefect S ν h t := by
  rw [responseDefect_eq_klDiv hS ν hh t]
  exact ENNReal.toReal_nonneg

omit [Nonempty X] [Nonempty J] hh in
theorem responseDefect_zero : responseDefect S ν h 0 = 0 := by
  have h1 := genRate_atlasPath_zero hS ν (M := 0)
  rw [atlasPath_zero, meanMap_zero_eq_mean ν] at h1
  rw [responseDefect, tilted_zero_mul, klDiv_self, h1]
  simp

/-- **The evolution of the defect**: `ℰ'(t) = t Var_{ρ_t}(h) + ⟨θ(m_t), Cov_{ρ_t}(S, h)⟩`. -/
theorem hasDerivAt_responseDefect (t₀ : ℝ) :
    HasDerivAt (responseDefect S ν h)
      (t₀ * lawCov (ν.tilted fun x ↦ t₀ * h x) h h +
        dotJ (dataTheta hS ν hh t₀ : J → ℝ) (dataCov S ν h t₀)) t₀ := by
  have h1 := hasDerivAt_klDiv_tilted_toReal ν hh t₀
  have h2 := hasDerivAt_genRate_dataPath hS ν hh t₀
  refine (h1.sub h2).congr_deriv ?_
  rw [lawCov]
  ring

/-- The defect starts with zero velocity. -/
theorem hasDerivAt_responseDefect_zero : HasDerivAt (responseDefect S ν h) 0 0 := by
  have := hasDerivAt_responseDefect hS ν hh 0
  rwa [dataTheta_zero, Submodule.coe_zero, dotJ_zero_left, zero_mul, zero_add] at this

omit [Fintype J] [Nonempty J] hS in
/-- The variance of the data direction along the data path is differentiable. -/
theorem exists_hasDerivAt_lawCov_dataPath (t₀ : ℝ) :
    ∃ V' : ℝ, HasDerivAt (fun t ↦ lawCov (ν.tilted fun x ↦ t * h x) h h) V' t₀ :=
  ⟨_, (hasDerivAt_integral_tilted ν hh (hh.mul hh) t₀).sub
    ((hasDerivAt_integral_tilted ν hh hh t₀).mul (hasDerivAt_integral_tilted ν hh hh t₀))⟩

/-- **The curvature of the defect at the featureless law is the residual variance**:
`ℰ''(0) = Var_ν(h) − Var_ν(regressor)`. -/
theorem hasDerivAt_deriv_responseDefect_zero :
    HasDerivAt (deriv (responseDefect S ν h))
      (lawCov ν h h - lawCov ν (regressor hS ν hh) (regressor hS ν hh)) 0 := by
  have e : deriv (responseDefect S ν h) = fun t ↦
      t * lawCov (ν.tilted fun x ↦ t * h x) h h +
        dotJ (dataTheta hS ν hh t : J → ℝ) (dataCov S ν h t) :=
    funext fun t ↦ (hasDerivAt_responseDefect hS ν hh t).deriv
  rw [e]
  obtain ⟨V', hV⟩ := exists_hasDerivAt_lawCov_dataPath ν hh 0
  have hprod : HasDerivAt (fun t ↦ t * lawCov (ν.tilted fun x ↦ t * h x) h h)
      (1 * lawCov (ν.tilted fun x ↦ (0 : ℝ) * h x) h h + 0 * V') 0 :=
    (hasDerivAt_id 0).mul hV
  have hrate : HasDerivAt (fun t ↦ dotJ (dataTheta hS ν hh t : J → ℝ) (dataCov S ν h t))
      (-lawCov ν (regressor hS ν hh) (regressor hS ν hh)) 0 := by
    have := (hasDerivAt_rateVel_zero hS ν hh).neg
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
    simp
  refine (hprod.add hrate).congr_deriv ?_
  rw [tilted_zero_mul]
  ring

/-- **The curvature of the defect is the variance of the unexplained score**:
`ℰ''(0) = Var_ν(h − regressor)`. -/
theorem deriv_deriv_responseDefect_zero_eq_residual :
    deriv (deriv (responseDefect S ν h)) 0 =
      lawCov ν (fun x ↦ h x - regressor hS ν hh x) (fun x ↦ h x - regressor hS ν hh x) := by
  rw [(hasDerivAt_deriv_responseDefect_zero hS ν hh).deriv, residual_variance hS ν hh]

theorem deriv_deriv_responseDefect_zero_nonneg :
    0 ≤ deriv (deriv (responseDefect S ν h)) 0 := by
  rw [deriv_deriv_responseDefect_zero_eq_residual hS ν hh]
  exact lawCov_self_nonneg ν (hh.sub (bdd_regressor hS ν hh))

/-- **The defect is at most the data information**: `ℰ''(0) ≤ Var_ν(h) = (D(ρ_t‖ν))''(0)`. -/
theorem deriv_deriv_responseDefect_zero_le :
    deriv (deriv (responseDefect S ν h)) 0 ≤ lawCov ν h h := by
  rw [(hasDerivAt_deriv_responseDefect_zero hS ν hh).deriv]
  linarith [lawCov_self_nonneg ν (bdd_regressor hS ν hh)]

end Defect

end Laplace.Multi
