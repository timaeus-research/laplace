/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.InverseStability
import Laplace.Multi.ObservableCurvature
import Laplace.Multi.EmpiricalProjection
import Laplace.Multi.ConditioningChainRule

/-!
# The Fisher energy of the exponential path and the symmetrised divergence

For a natural coordinate `θ` with response `m(θ)` and featureless response `m₀ = m(0)`:

* `KL(P_θ ‖ ν) = −⟨θ, m(θ)⟩ − Λ(−θ)`                      (`klDiv_familyMeasure_featureless`)
* `KL(ν ‖ P_θ) = ⟨θ, m₀⟩ + Λ(−θ)`                          (`klDiv_featureless_familyMeasure`)
* `KL(P_θ ‖ ν) + KL(ν ‖ P_θ) = −⟨θ, m(θ) − m₀⟩`            (`toReal_klDiv_familyMeasure_symm`)
* `∫₀¹ Var_{P_{sθ}}⟨θ,S⟩ ds = −⟨θ, m(θ) − m₀⟩`              (`integral_var_familyMeasure_segment`)

so the Fisher energy of the straight path in natural coordinates from the featureless posterior to
`P_θ` is the symmetrised divergence between its endpoints, and equals the pairing of the natural
displacement `−θ` with the response displacement `m(θ) − m₀`
(`integral_var_familyMeasure_segment_eq_symm_klDiv`). The two orientations of the divergence are
the two Bregman halves of one pairing.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] in
/-- The mean of the family member `P_θ` is the mean map. -/
theorem mean_familyMeasure_one_zero (θ : J → ℝ) :
    (fun i ↦ ∫ x, S i x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) =
      meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := by
  funext i
  rw [integral_familyMeasure_one_zero hS ν θ (S i)]
  rfl

omit [Nonempty X] hS [IsProbabilityMeasure ν] in
/-- The cumulant of `−θ` as the logarithm of the tilt normaliser. -/
theorem log_integral_exp_neg_dirLoss (θ : J → ℝ) :
    Real.log (∫ x, Real.exp (-1 * dirLoss S θ x) ∂ν) = featCgf ν S (-θ) := by
  unfold featCgf
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [dirLoss_neg (S := S)]
  ring_nf

/-- **The divergence of a family member from the featureless posterior**:
`KL(P_θ ‖ ν) = −⟨θ, m(θ)⟩ − Λ(−θ)`. -/
theorem klDiv_familyMeasure_featureless (θ : J → ℝ) :
    klDiv (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) ν =
      ENNReal.ofReal (-dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) -
        featCgf ν S (-θ)) := by
  have hbdd : Bdd (fun x ↦ -1 * dirLoss S θ x) := Bdd.const_mul (-1) (bdd_dirLoss hS _)
  have : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) θ
  have hmean : ∫ x, -1 * dirLoss S θ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ =
      -dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) := by
    rw [MeasureTheory.integral_const_mul, ← dotJ_integral_eq _ hS _,
      mean_familyMeasure_one_zero hS ν]
    ring
  rw [familyMeasure_one_zero_eq_tilted hS ν θ, klDiv_tilted_eq ν hbdd,
    ← familyMeasure_one_zero_eq_tilted hS ν θ, hmean, log_integral_exp_neg_dirLoss ν]

/-- **The divergence of the featureless posterior from a family member**:
`KL(ν ‖ P_θ) = ⟨θ, m₀⟩ + Λ(−θ)`. -/
theorem klDiv_featureless_familyMeasure (θ : J → ℝ) :
    klDiv ν (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) =
      ENNReal.ofReal (dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) +
        featCgf ν S (-θ)) := by
  have hbdd : Bdd (fun x ↦ -1 * dirLoss S θ x) := Bdd.const_mul (-1) (bdd_dirLoss hS _)
  have hmean : ∫ x, -1 * dirLoss S θ x ∂ν =
      -dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
    rw [MeasureTheory.integral_const_mul, ← dotJ_integral_eq ν hS _, meanMap_zero_eq_mean ν]
    ring
  have h0 : klDiv ν ν ≠ ⊤ := by
    rw [klDiv_self]
    exact ENNReal.zero_ne_top
  rw [familyMeasure_one_zero_eq_tilted hS ν θ,
    klDiv_tilted_right_eq ν ν Measure.AbsolutelyContinuous.rfl h0 hbdd, klDiv_self,
    ENNReal.toReal_zero, hmean, log_integral_exp_neg_dirLoss ν]
  congr 1
  ring

/-- Both real expressions are nonnegative (Fenchel at `m(θ)` and at `m₀`). -/
theorem nonneg_klDiv_familyMeasure_featureless (θ : J → ℝ) :
    0 ≤ -dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) - featCgf ν S (-θ) := by
  obtain ⟨-, h⟩ := featCgf_eq_dotJ_sub_genRate_meanMap hS ν (-θ)
  rw [neg_neg, dotJ_neg_left] at h
  have := ENNReal.toReal_nonneg (a := genRate ν S (meanMap ν (fun _ ↦ (1 : ℝ))
    (fun _ ↦ (0 : ℝ)) S 1 θ))
  linarith

omit [Nonempty X] in
theorem nonneg_klDiv_featureless_familyMeasure (θ : J → ℝ) :
    0 ≤ dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) + featCgf ν S (-θ) := by
  have h0 : genRate ν S (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) = 0 := by
    rw [meanMap_zero_eq_mean ν]
    exact genRate_mean_eq_zero ν hS
  have hF := dotJ_sub_genRate_le_featCgf ν (h0 ▸ ENNReal.zero_ne_top) (-θ)
  rw [h0, ENNReal.toReal_zero, sub_zero, dotJ_neg_left] at hF
  linarith

/-- **The symmetrised divergence is the pairing of the displacements**:
`KL(P_θ ‖ ν) + KL(ν ‖ P_θ) = −⟨θ, m(θ) − m₀⟩`. -/
theorem toReal_klDiv_familyMeasure_symm (θ : J → ℝ) :
    (klDiv (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) ν).toReal +
      (klDiv ν (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)).toReal =
      -dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ -
        meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  rw [klDiv_familyMeasure_featureless hS ν, klDiv_featureless_familyMeasure hS ν,
    ENNReal.toReal_ofReal (nonneg_klDiv_familyMeasure_featureless hS ν θ),
    ENNReal.toReal_ofReal (nonneg_klDiv_featureless_familyMeasure hS ν θ),
    (isLinearMap_dotJ θ).map_sub (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
      (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)]
  ring

/-- **The Fisher energy of the exponential path** `s ↦ P_{sθ}`, `s ∈ [0,1]`:
`∫₀¹ Var_{P_{sθ}}⟨θ,S⟩ ds = −⟨θ, m(θ) − m₀⟩`. -/
theorem integral_var_familyMeasure_segment (θ : J → ℝ) :
    ∫ s in (0 : ℝ)..1, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (s • θ))
        (dirLoss S θ) (dirLoss S θ) =
      -dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ -
        meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  have hd : ∀ t : ℝ, HasDerivAt
      (fun t ↦ dotJ θ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (t • θ)))
      (-lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (t • θ))
        (dirLoss S θ) (dirLoss S θ)) t := by
    intro t
    have h := hasDerivAt_dotJ_meanMap_segment hS ν 0 θ t
    simpa only [sub_zero, zero_add] using h
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ t • θ) θ t := fun t ↦ by
    simpa using (hasDerivAt_id' (x := t)).smul_const θ
  have hcont : Continuous fun t : ℝ ↦
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (t • θ))
        (dirLoss S θ) (dirLoss S θ) :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_lawCov_familyMeasure_path hS ν (hline t)
      (bdd_dirLoss hS θ) (bdd_dirLoss hS θ)).continuousAt
  have hint := hcont.neg.intervalIntegrable (μ := volume) (0 : ℝ) 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hint
  rw [intervalIntegral.integral_neg, one_smul, zero_smul] at h
  rw [(isLinearMap_dotJ θ).map_sub (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
    (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)]
  linarith

/-- **Energy equals symmetrised divergence**: the Fisher energy of the exponential path from the
featureless posterior to `P_θ` is `KL(P_θ ‖ ν) + KL(ν ‖ P_θ)`. -/
theorem integral_var_familyMeasure_segment_eq_symm_klDiv (θ : J → ℝ) :
    ∫ s in (0 : ℝ)..1, lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (s • θ))
        (dirLoss S θ) (dirLoss S θ) =
      (klDiv (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) ν).toReal +
        (klDiv ν (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)).toReal := by
  rw [integral_var_familyMeasure_segment hS ν, toReal_klDiv_familyMeasure_symm hS ν]

end Laplace.Multi
