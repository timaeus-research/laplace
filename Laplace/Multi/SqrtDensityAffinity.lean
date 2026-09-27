/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasHessian
import Laplace.Multi.ReconstructionDerivative
import Laplace.Multi.FisherSpeedForm
import Laplace.Multi.DataRayBlocks
import Laplace.Multi.BoundaryBlowup

/-!
# Square-root densities and the affinity identity

`rootDens S ν θ = √(dP_θ/dν) = e^{−⟨θ,S⟩/2}/√Z(θ)`: bounded, measurable, of unit `L²(ν)` norm. The
exact **affinity identity** `∫ q_θ q_η dν = Z((θ+η)/2)/√(Z(θ)Z(η))` reduces all Hellinger
computations of the exponential family to the partition function. Also the centred second moment
`∫ q_θ² (⟨v,S⟩ − E_θ⟨v,S⟩)² dν = Var_{P_θ}⟨v,S⟩` (the Fisher form) and a Cauchy–Schwarz
inequality for integrals of bounded functions.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Defs

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ) (ν : Measure X)

/-- The square-root density `q_θ = √(dP_θ/dν)`. -/
noncomputable def rootDens (θ : J → ℝ) (x : X) : ℝ := √(famDens S ν θ x)

theorem rootDens_nonneg (θ : J → ℝ) (x : X) : 0 ≤ rootDens S ν θ x := Real.sqrt_nonneg _

end Defs

section Basic

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

theorem rootDens_sq (θ : J → ℝ) (x : X) : rootDens S ν θ x ^ 2 = famDens S ν θ x :=
  Real.sq_sqrt (famDens_nonneg hS ν θ x)

theorem rootDens_eq (θ : J → ℝ) (x : X) :
    rootDens S ν θ x = Real.exp (-dirLoss S θ x / 2) / √(famZ S ν θ) := by
  unfold rootDens famDens famWeight
  rw [Real.sqrt_div' _ (famZ_pos hS ν θ).le, ← Real.exp_half]

omit [IsProbabilityMeasure ν] in
theorem measurable_rootDens (θ : J → ℝ) : Measurable (rootDens S ν θ) := by
  unfold rootDens famDens famWeight
  exact ((bdd_dirLoss hS θ).1.neg.exp.div_const _).sqrt

theorem exists_rootDens_le (θ : J → ℝ) : ∃ C : ℝ, ∀ x, rootDens S ν θ x ≤ C := by
  obtain ⟨-, K, hK⟩ := bdd_dirLoss hS θ
  refine ⟨Real.exp (K / 2) / √(famZ S ν θ), fun x ↦ ?_⟩
  rw [rootDens_eq hS ν]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
  have := (abs_le.1 (hK x)).1
  linarith

theorem bdd_rootDens (θ : J → ℝ) : Bdd (rootDens S ν θ) := by
  obtain ⟨C, hC⟩ := exists_rootDens_le hS ν θ
  exact ⟨measurable_rootDens hS ν θ, C, fun x ↦ by
    rw [abs_of_nonneg (rootDens_nonneg S ν θ x)]
    exact hC x⟩

theorem integral_rootDens_sq (θ : J → ℝ) : ∫ x, rootDens S ν θ x ^ 2 ∂ν = 1 := by
  simp_rw [rootDens_sq hS ν]
  exact integral_famDens hS ν θ

/-- The product of two square-root densities is the weight at the midpoint over `√(Z θ Z η)`. -/
theorem rootDens_mul (θ η : J → ℝ) (x : X) :
    rootDens S ν θ x * rootDens S ν η x =
      famWeight S ((1 / 2 : ℝ) • (θ + η)) x / √(famZ S ν θ * famZ S ν η) := by
  rw [rootDens_eq hS ν, rootDens_eq hS ν, Real.sqrt_mul (famZ_pos hS ν θ).le, div_mul_div_comm,
    ← Real.exp_add]
  unfold famWeight
  simp only [dirLoss_smul, dirLoss_add]
  rw [show -dirLoss S θ x / 2 + -dirLoss S η x / 2 =
    -(1 / 2 * (dirLoss S θ x + dirLoss S η x)) by ring]

/-- **The affinity identity** `∫ q_θ q_η dν = Z((θ+η)/2)/√(Z θ Z η)`. -/
theorem integral_rootDens_mul (θ η : J → ℝ) :
    ∫ x, rootDens S ν θ x * rootDens S ν η x ∂ν =
      famZ S ν ((1 / 2 : ℝ) • (θ + η)) / √(famZ S ν θ * famZ S ν η) := by
  simp_rw [rootDens_mul hS ν]
  rw [integral_div]
  rfl

/-- `E_{P_θ}⟨v,S⟩ = ⟨v, m(θ)⟩` in density form. -/
theorem integral_famDens_mul_dirLoss [Nonempty X] (θ v : J → ℝ) :
    ∫ x, famDens S ν θ x * dirLoss S v x ∂ν = dotJ v (famMean S ν θ) := by
  have := isProbabilityMeasure_family hS ν θ
  rw [← integral_famDens_mul hS ν θ, integral_dirLoss_eq_dotJ v _ hS, famMean_eq_meanMap hS ν,
    ← mean_familyMeasure_one_zero hS ν θ]

/-- `∫ e^{−⟨θ,S⟩} ⟨v,S⟩ dν = Z(θ) ⟨v, m(θ)⟩`. -/
theorem integral_famWeight_mul_dirLoss [Nonempty X] (θ v : J → ℝ) :
    ∫ x, famWeight S θ x * dirLoss S v x ∂ν = famZ S ν θ * dotJ v (famMean S ν θ) := by
  rw [← integral_famDens_mul_dirLoss hS ν, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [famDens]
  have hZ := (famZ_pos hS ν θ).ne'
  field_simp

/-- **The centred second moment of the square-root density is the Fisher form.** -/
theorem integral_rootDens_mul_centred_sq [Nonempty X] (θ v : J → ℝ) :
    ∫ x, (rootDens S ν θ x * (dirLoss S v x - dotJ v (famMean S ν θ))) ^ 2 ∂ν =
      fisherVar S ν θ v := by
  have hP := isProbabilityMeasure_family hS ν θ
  have e : ∀ x, (rootDens S ν θ x * (dirLoss S v x - dotJ v (famMean S ν θ))) ^ 2 =
      famDens S ν θ x * ((dirLoss S v x - dotJ v (famMean S ν θ)) *
        (dirLoss S v x - dotJ v (famMean S ν θ))) := fun x ↦ by
    rw [mul_pow, rootDens_sq hS ν]
    ring
  simp_rw [e]
  rw [← integral_famDens_mul hS ν θ, fisherVar,
    lawCov_eq_integral_centred _ (bdd_dirLoss hS v) (bdd_dirLoss hS v),
    integral_dirLoss_eq_dotJ v _ hS, famMean_eq_meanMap hS ν, ← mean_familyMeasure_one_zero hS ν θ]

end Basic

section CauchySchwarz

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- **Cauchy–Schwarz for integrals of bounded functions.** -/
theorem sq_integral_mul_le {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x * f x ∂ν) * ∫ x, g x * g x ∂ν := by
  have hff := integrable_of_bdd_prob ν (hf.mul hf)
  have hgg := integrable_of_bdd_prob ν (hg.mul hg)
  have hfg := integrable_of_bdd_prob ν (hf.mul hg)
  have key : ∀ l : ℝ, 0 ≤ (∫ x, g x * g x ∂ν) * (l * l) + (-2 * ∫ x, f x * g x ∂ν) * l +
      ∫ x, f x * f x ∂ν := fun l ↦ by
    have h0 : 0 ≤ ∫ x, (f x - l * g x) * (f x - l * g x) ∂ν :=
      integral_nonneg fun x ↦ mul_self_nonneg _
    have h1 : ∀ x, (f x - l * g x) * (f x - l * g x) =
        f x * f x - 2 * l * (f x * g x) + l * l * (g x * g x) := fun x ↦ by ring
    simp_rw [h1] at h0
    have i1 : Integrable (fun x ↦ f x * f x - 2 * l * (f x * g x)) ν :=
      hff.sub (hfg.const_mul _)
    have i2 : Integrable (fun x ↦ l * l * (g x * g x)) ν := hgg.const_mul _
    have i3 : Integrable (fun x ↦ 2 * l * (f x * g x)) ν := hfg.const_mul _
    rw [integral_add i1 i2, integral_sub hff i3, integral_const_mul, integral_const_mul] at h0
    linarith
  have h := discrim_le_zero key
  rw [discrim] at h
  nlinarith [h]

end CauchySchwarz

end Laplace.Multi
