/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ShellMassClassification
import Laplace.Multi.SusceptibilityFisherBound

/-!
# Fisher accessibility of a face along a natural ray: the exact classification

Combining the variance sandwich (`RayVarianceSandwich`) with the shell-mass classification
(`ShellMassClassification`), the natural ray `θ − tu` towards an exposed face has finite Fisher
length — `∫^∞ √Var_{p_t}⟨u,S⟩ dt < ∞` — **iff** the dyadic shell masses
`a_k = ∫_{R/2^{k+1} < β − ⟨u,S⟩ ≤ R/2^k} e^{−⟨θ,S⟩} dν` of the boundary layer satisfy `Σ_k √a_k < ∞`
(`lintegral_sqrt_raySpeedSq_lt_top_iff`).  The tail and the whole ray have the same finiteness
(`lintegral_sqrt_raySpeedSq_Ioi_lt_top_iff`), since the Fisher speed is bounded.

This separates the topological completion (always present: every face is a total-variation and
Hellinger limit of the ray) from the metric completion: for a layer `H(r) ∼ c (log 1/r)^{−β}` the
shell masses are `a_k ≍ k^{−β−1}`, so the face is at finite Fisher distance along the ray iff
`β > 1`; Astra's example `β = 1` is reached in total variation but not in Fisher length.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Ray

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (θ u : J → ℝ) (β : ℝ)
include hS

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- Under the a.e. slack bound, the off-face set is a.e. the set of positive slack. -/
theorem faceFibre_compl_ae_eq_slackPos (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) :
    ({x | 0 < β - dirLoss S u x} : Set X) =ᵐ[ν] {x | dirLoss S u x = β}ᶜ := by
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [hβ] with x hx
  constructor
  · intro h heq
    have h' : 0 < β - dirLoss S u x := h
    have heq' : dirLoss S u x = β := heq
    linarith
  · intro h
    have h' : ¬ dirLoss S u x = β := h
    exact sub_pos.2 (lt_of_le_of_ne hx h')

omit [Nonempty X] [Nonempty J] in
/-- The Lebesgue second moment of the shell module is the second slack moment. -/
theorem secondMomentE_eq_ofReal_slackMoment (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (t : ℝ) :
    secondMomentE ν (famWeight S θ) (fun x ↦ β - dirLoss S u x) t =
      ENNReal.ofReal (slackMoment S ν θ u β 2 t) := by
  unfold secondMomentE slackMoment
  rw [Measure.restrict_congr_set (faceFibre_compl_ae_eq_slackPos ν u β hβ),
    ofReal_integral_eq_lintegral_ofReal (integrable_slack_pow_mul hS ν θ u β 2 t).integrableOn
      (Eventually.of_forall fun x ↦ mul_nonneg (sq_nonneg _)
        (mul_nonneg (famWeight_pos θ x).le (Real.exp_pos _).le))]
  rfl

omit [Nonempty X] [Nonempty J] in
theorem ofReal_sqrt_slackMoment_eq (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (t : ℝ) :
    ENNReal.ofReal (√(slackMoment S ν θ u β 2 t)) =
      secondMomentE ν (famWeight S θ) (fun x ↦ β - dirLoss S u x) t ^ (1 / 2 : ℝ) := by
  rw [secondMomentE_eq_ofReal_slackMoment hS ν θ u β hβ t,
    ENNReal.ofReal_rpow_of_nonneg (slackMoment_nonneg ν θ u β hβ 2 t) (by norm_num),
    Real.sqrt_eq_rpow]

omit [Nonempty X] [Nonempty J] in
/-- **Upper comparison**: `∫₀^∞ √Var ≤ (1/√A) ∫₀^∞ √C₂`. -/
theorem lintegral_sqrt_raySpeedSq_le (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν θ u t)) ≤
      ENNReal.ofReal (1 / √(faceMass S ν θ u β)) *
        ∫⁻ t in Ioi (0 : ℝ),
          secondMomentE ν (famWeight S θ) (fun x ↦ β - dirLoss S u x) t ^ (1 / 2 : ℝ) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun t ht ↦ ?_))
  rw [← ofReal_sqrt_slackMoment_eq hS ν θ u β hβ t, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (sqrt_raySpeedSq_comparable hS ν θ u β hβ hp (le_of_lt ht)).2
  rw [div_eq_mul_one_div, mul_comm] at h
  exact h

omit [Nonempty X] [Nonempty J] in
/-- **Lower comparison**: `(√A/(A + B₀)) ∫₀^∞ √C₂ ≤ ∫₀^∞ √Var`. -/
theorem le_lintegral_sqrt_raySpeedSq (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    ENNReal.ofReal (√(faceMass S ν θ u β) / (faceMass S ν θ u β + offFaceMass S ν θ u β 0)) *
        ∫⁻ t in Ioi (0 : ℝ),
          secondMomentE ν (famWeight S θ) (fun x ↦ β - dirLoss S u x) t ^ (1 / 2 : ℝ) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν θ u t)) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hB0 := offFaceMass_nonneg hS ν θ u β 0
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun t ht ↦ ?_))
  rw [← ofReal_sqrt_slackMoment_eq hS ν θ u β hβ t,
    ← ENNReal.ofReal_mul (div_nonneg (Real.sqrt_nonneg _) (by linarith))]
  exact ENNReal.ofReal_le_ofReal (sqrt_raySpeedSq_comparable hS ν θ u β hβ hp (le_of_lt ht)).1

omit [Nonempty J] in
/-- The Fisher speed of the ray is bounded by the bound of the statistic. -/
theorem sqrt_raySpeedSq_le {K : ℝ} (hK : ∀ x, |dirLoss S u x| ≤ K) (t : ℝ) :
    √(raySpeedSq S ν θ u t) ≤ K := by
  have hP : IsProbabilityMeasure
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u)) := by
    rw [familyMeasure_eq_withDensity_famDens]
    exact isProbabilityMeasure_withDensity_ofReal ν (famDens_nonneg hS ν _)
      (integrable_famDens hS ν _) (integral_famDens hS ν _)
  exact sqrt_lawCov_self_le _ (bdd_dirLoss hS u) hK

omit [Nonempty J] in
/-- **The tail and the whole ray have the same Fisher-length finiteness.** -/
theorem lintegral_sqrt_raySpeedSq_Ioi_lt_top_iff {T : ℝ} (hT : 0 < T) :
    (∫⁻ t in Ioi T, ENNReal.ofReal (√(raySpeedSq S ν θ u t))) < ⊤ ↔
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν θ u t))) < ⊤ := by
  obtain ⟨-, K, hK⟩ := bdd_dirLoss hS u
  have hsplit : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν θ u t)) =
      (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (√(raySpeedSq S ν θ u t))) +
        ∫⁻ t in Ioi T, ENNReal.ofReal (√(raySpeedSq S ν θ u t)) := by
    rw [← lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same, Ioc_union_Ioi_eq_Ioi hT.le]
  have hfin : (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (√(raySpeedSq S ν θ u t))) < ⊤ := by
    calc ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (√(raySpeedSq S ν θ u t))
        ≤ ∫⁻ _ in Ioc (0 : ℝ) T, ENNReal.ofReal K :=
          lintegral_mono fun t ↦ ENNReal.ofReal_le_ofReal (sqrt_raySpeedSq_le hS ν θ u hK t)
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [hsplit]
  constructor
  · intro h
    exact ENNReal.add_lt_top.2 ⟨hfin, h⟩
  · intro h
    exact (ENNReal.add_lt_top.1 h).2

omit [Nonempty X] [Nonempty J] in
/-- **The exact classification of Fisher accessibility along a natural ray**: the ray has finite
Fisher length iff the dyadic shell masses of the boundary layer have summable square roots. -/
theorem lintegral_sqrt_raySpeedSq_lt_top_iff (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {R : ℝ} (hR : 0 < R)
    (hgR : ∀ x, β - dirLoss S u x ≤ R) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(raySpeedSq S ν θ u t))) < ⊤ ↔
      (∑' k, shellMass ν (famWeight S θ) (fun x ↦ β - dirLoss S u x) R k ^ (1 / 2 : ℝ)) < ⊤ := by
  have hw : Measurable (famWeight S θ) := Real.measurable_exp.comp (bdd_dirLoss hS θ).1.neg
  have hw0 : ∀ x, 0 ≤ famWeight S θ x := fun x ↦ (famWeight_pos θ x).le
  have hg : Measurable fun x ↦ β - dirLoss S u x := (bdd_dirLoss hS u).1.const_sub β
  rw [← lintegral_sqrt_secondMomentE_lt_top_iff ν hw hw0 hg hR hgR]
  have hA := faceMass_pos hS ν θ u β hp
  have hB0 := offFaceMass_nonneg hS ν θ u β 0
  constructor
  · intro h
    have hc : 0 < √(faceMass S ν θ u β) / (faceMass S ν θ u β + offFaceMass S ν θ u β 0) := by
      positivity
    have key := le_lintegral_sqrt_raySpeedSq hS ν θ u β hβ hp
    have e : ∫⁻ t in Ioi (0 : ℝ),
        secondMomentE ν (famWeight S θ) (fun x ↦ β - dirLoss S u x) t ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (1 / (√(faceMass S ν θ u β) /
          (faceMass S ν θ u β + offFaceMass S ν θ u β 0))) *
          (ENNReal.ofReal (√(faceMass S ν θ u β) /
            (faceMass S ν θ u β + offFaceMass S ν θ u β 0)) *
            ∫⁻ t in Ioi (0 : ℝ),
              secondMomentE ν (famWeight S θ) (fun x ↦ β - dirLoss S u x) t ^ (1 / 2 : ℝ)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hc.ne',
        ENNReal.ofReal_one, one_mul]
    rw [e]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt key h)
  · intro h
    exact lt_of_le_of_lt (lintegral_sqrt_raySpeedSq_le hS ν θ u β hβ hp)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)

end Ray

end Laplace.Multi
