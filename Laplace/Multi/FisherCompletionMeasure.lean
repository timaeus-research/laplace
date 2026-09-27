/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherCompletionLaws

/-!
# The law of a completion point as a measure

`completionLaw x = ν.withDensity (Ψ̄(x)²)`: a probability measure absolutely continuous with respect
to the base measure, with mean `meanExt x`, and equal to `P_θ` at interior points.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The law of a completion point.** -/
noncomputable def completionLaw (x : FisherCompletion hS ν) : Measure X :=
  ν.withDensity fun y ↦ ENNReal.ofReal (rootDensExt hS ν x y * rootDensExt hS ν x y)

theorem completionLaw_absolutelyContinuous (x : FisherCompletion hS ν) :
    completionLaw hS ν x ≪ ν :=
  withDensity_absolutelyContinuous _ _

theorem integrable_rootDensExt_mul_self (x : FisherCompletion hS ν) :
    Integrable (fun y ↦ rootDensExt hS ν x y * rootDensExt hS ν x y) ν :=
  (Lp.memLp _).integrable_mul (Lp.memLp _)

theorem aemeasurable_rootDensExt_mul_self (x : FisherCompletion hS ν) :
    AEMeasurable (fun y ↦ rootDensExt hS ν x y * rootDensExt hS ν x y) ν :=
  (Lp.aestronglyMeasurable _).aemeasurable.mul (Lp.aestronglyMeasurable _).aemeasurable

/-- Integrals against the law of a completion point. -/
theorem integral_completionLaw (x : FisherCompletion hS ν) (f : X → ℝ) :
    ∫ y, f y ∂completionLaw hS ν x =
      ∫ y, (rootDensExt hS ν x y * rootDensExt hS ν x y) * f y ∂ν := by
  rw [completionLaw, integral_withDensity_eq_integral_toReal_smul₀
    (aemeasurable_rootDensExt_mul_self hS ν x).ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (mul_self_nonneg _), smul_eq_mul]

theorem completionLaw_univ (x : FisherCompletion hS ν) : completionLaw hS ν x univ = 1 := by
  rw [completionLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_rootDensExt_mul_self hS ν x)
      (ae_of_all _ fun y ↦ mul_self_nonneg _), integral_rootDensExt_sq hS ν, ENNReal.ofReal_one]

instance (x : FisherCompletion hS ν) : IsProbabilityMeasure (completionLaw hS ν x) :=
  ⟨completionLaw_univ hS ν x⟩

/-- **The law of a completion point has the extended mean.** -/
theorem integral_completionLaw_eq_meanExt (x : FisherCompletion hS ν) (i : J) :
    ∫ y, S i y ∂completionLaw hS ν x = meanExt hS ν x i := by
  rw [integral_completionLaw hS ν, meanExt_eq_integral_rootDensExt hS ν]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ by ring)

/-- **At interior points the law is the family member.** -/
theorem completionLaw_coe (p : FisherPoint hS ν) :
    completionLaw hS ν (p : FisherCompletion hS ν) = Pfam (p.param : J → ℝ) := by
  rw [completionLaw, familyMeasure_eq_withDensity_famDens, rootDensExt_coe]
  refine withDensity_congr_ae ?_
  filter_upwards [(memLp_rootDens hS ν (p.param : J → ℝ)).coeFn_toLp] with y hy
  rw [rootDensLp, hy, ← sq, rootDens_sq hS ν]

end Law

end Laplace.Multi
