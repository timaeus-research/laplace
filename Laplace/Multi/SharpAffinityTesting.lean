/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseProductAffinity
import Laplace.Multi.ResponseHellingerAtlas

/-!
# Sharp affinity testing bounds

`ResponseProductAffinity` advertises the coarse bound `TV ≤ H`. Cauchy–Schwarz actually gives, for
unit vectors `f, g ∈ L²(μ)` with affinity `A = ⟪f, g⟫`,
`∫ |f² − g²| ≤ ‖f − g‖ ‖f + g‖ = √(2 − 2A) √(2 + 2A) = 2 √(1 − A²)`, hence for every test
`0 ≤ φ ≤ 1`

`∫ φ d(f²μ) − ∫ φ d(g²μ) ≤ √(1 − A²)`   (`integral_rootLaw_sub_le_sqrt`),

and every equal-prior test has error at least `(1 − √(1 − A²))/2` (`testing_error_ge_sqrt`). For
`n` samples of two completion laws the affinity tensorises exactly, `A_n = A^n`, so

`∫ φ dQ_x^{⊗n} − ∫ φ dQ_y^{⊗n} ≤ √(1 − A(x,y)^{2n})`   (`integral_sampleLaw_sub_le_sqrt`),

with `A(x, y) = ∫ Ψ_x Ψ_y = 1 − H(Q_x, Q_y)²/2 ≥ 1 − d̂(x, y)²/8` (`affinityExt_ge`). These are the
exact affinity-based testing bounds; the coarse `√n d̂/2` bound is their linearisation.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Roots

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- `‖f + g‖² = 2 + 2A` for unit vectors. -/
theorem norm_add_sq_eq {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    ‖f + g‖ ^ 2 = 2 + 2 * ∫ y, f y * g y ∂μ := by
  rw [norm_add_sq_real, hf, hg, inner_eq_integral_mul]
  ring

/-- The affinity of unit vectors lies in `[−1, 1]`. -/
theorem abs_integral_mul_le_one {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    |∫ y, f y * g y ∂μ| ≤ 1 := by
  rw [← inner_eq_integral_mul]
  have := abs_real_inner_le_norm f g
  rwa [hf, hg, one_mul] at this

/-- **The sharp total-variation bound**: `∫ |f² − g²| ≤ 2 √(1 − A²)`. -/
theorem integral_abs_mul_self_sub_le_sqrt {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    ∫ y, |f y * f y - g y * g y| ∂μ ≤ 2 * √(1 - (∫ y, f y * g y ∂μ) ^ 2) := by
  calc ∫ y, |f y * f y - g y * g y| ∂μ = ∫ y, |f y - g y| * |f y + g y| ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        beta_reduce
        rw [← abs_mul]
        congr 1
        ring
    _ ≤ ‖f - g‖ * ‖f + g‖ := integral_abs_sub_mul_abs_add_le μ f g
    _ = √(‖f - g‖ ^ 2 * ‖f + g‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ = √(4 * (1 - (∫ y, f y * g y ∂μ) ^ 2)) := by
        rw [norm_sub_sq_eq μ hf hg, norm_add_sq_eq μ hf hg]
        congr 1
        ring
    _ = 2 * √(1 - (∫ y, f y * g y ∂μ) ^ 2) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

/-- A test sees at most half of the total variation. -/
theorem integral_rootLaw_sub_le_half {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) {φ : Ω → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1) :
    ∫ y, φ y ∂rootLaw μ f - ∫ y, φ y ∂rootLaw μ g ≤
      (∫ y, |f y * f y - g y * g y| ∂μ) / 2 := by
  rw [integral_rootLaw, integral_rootLaw]
  have hφb : ∀ y, ‖φ y‖ ≤ 1 := fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 y)]
    exact hφ1 y
  have hff := integrable_mul_self μ f
  have hgg := integrable_mul_self μ g
  have h1 : Integrable (fun y ↦ (f y * f y) * φ y) μ :=
    (hff.bdd_mul hφm.aestronglyMeasurable (Eventually.of_forall hφb)).congr
      (Eventually.of_forall fun y ↦ mul_comm _ _)
  have h2 : Integrable (fun y ↦ (g y * g y) * φ y) μ :=
    (hgg.bdd_mul hφm.aestronglyMeasurable (Eventually.of_forall hφb)).congr
      (Eventually.of_forall fun y ↦ mul_comm _ _)
  have h12 : Integrable (fun y ↦ (f y * f y) * φ y - (g y * g y) * φ y) μ := h1.sub h2
  have hd : Integrable (fun y ↦ f y * f y - g y * g y) μ := hff.sub hgg
  have hD : Integrable
      (fun y ↦ (|f y * f y - g y * g y| + (f y * f y - g y * g y)) / 2) μ :=
    (hd.abs.add hd).div_const 2
  have key : ∀ y, (f y * f y) * φ y - (g y * g y) * φ y ≤
      (|f y * f y - g y * g y| + (f y * f y - g y * g y)) / 2 := by
    intro y
    have h0 := hφ0 y
    have h1 := hφ1 y
    rcases le_or_gt 0 (f y * f y - g y * g y) with h | h
    · rw [abs_of_nonneg h]
      nlinarith
    · rw [abs_of_neg h]
      nlinarith
  have hfg : ∫ y, (f y * f y - g y * g y) ∂μ = 0 := by
    rw [integral_sub hff hgg, integral_mul_self_eq_one μ hf, integral_mul_self_eq_one μ hg,
      sub_self]
  calc (∫ y, (f y * f y) * φ y ∂μ) - ∫ y, (g y * g y) * φ y ∂μ =
        ∫ y, ((f y * f y) * φ y - (g y * g y) * φ y) ∂μ := (integral_sub h1 h2).symm
    _ ≤ ∫ y, (|f y * f y - g y * g y| + (f y * f y - g y * g y)) / 2 ∂μ :=
        integral_mono h12 hD key
    _ = ((∫ y, |f y * f y - g y * g y| ∂μ) + ∫ y, (f y * f y - g y * g y) ∂μ) / 2 := by
        rw [integral_div, integral_add hd.abs hd]
    _ = (∫ y, |f y * f y - g y * g y| ∂μ) / 2 := by rw [hfg, add_zero]

/-- **The sharp testing bound**: `∫ φ d(f²μ) − ∫ φ d(g²μ) ≤ √(1 − A²)`. -/
theorem integral_rootLaw_sub_le_sqrt {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) {φ : Ω → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1) :
    ∫ y, φ y ∂rootLaw μ f - ∫ y, φ y ∂rootLaw μ g ≤ √(1 - (∫ y, f y * g y ∂μ) ^ 2) := by
  refine (integral_rootLaw_sub_le_half μ hf hg hφm hφ0 hφ1).trans ?_
  have := integral_abs_mul_self_sub_le_sqrt μ hf hg
  linarith

/-- **Every equal-prior test has error at least `(1 − √(1 − A²))/2`.** -/
theorem testing_error_ge_sqrt {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) {φ : Ω → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1) :
    (1 - √(1 - (∫ y, f y * g y ∂μ) ^ 2)) / 2 ≤
      ((∫ y, φ y ∂rootLaw μ f) + ∫ y, (1 - φ y) ∂rootLaw μ g) / 2 := by
  have := isProbabilityMeasure_rootLaw μ hg
  have hφb : ∀ y, ‖φ y‖ ≤ 1 := fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 y)]
    exact hφ1 y
  have hint : Integrable φ (rootLaw μ g) :=
    Integrable.of_bound hφm.aestronglyMeasurable 1 (Eventually.of_forall hφb)
  rw [integral_sub (integrable_const 1) hint, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  have h := integral_rootLaw_sub_le_sqrt μ hg hf hφm hφ0 hφ1
  have e : (fun y ↦ g y * f y) = fun y ↦ f y * g y := funext fun y ↦ mul_comm _ _
  rw [e] at h
  linarith

end Roots

section Completion

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The affinity of two completion laws**: `A(x, y) = ∫ Ψ_x Ψ_y dν`. -/
noncomputable def affinityExt (x y : FisherCompletion hS ν) : ℝ :=
  ∫ z, rootDensExt hS ν x z * rootDensExt hS ν y z ∂ν

/-- `A(x, y) = 1 − H(Q_x, Q_y)²/2`. -/
theorem affinityExt_eq (x y : FisherCompletion hS ν) :
    affinityExt hS ν x y = 1 - hellingerExt hS ν x y ^ 2 / 2 := by
  have := norm_sub_sq_eq ν (norm_rootDensExt hS ν x) (norm_rootDensExt hS ν y)
  rw [hellingerExt, dist_eq_norm, affinityExt]
  linarith

/-- **The affinity is at least `1 − d̂²/8`.** -/
theorem affinityExt_ge (x y : FisherCompletion hS ν) :
    1 - dist x y ^ 2 / 8 ≤ affinityExt hS ν x y := by
  rw [affinityExt_eq]
  have h := hellingerExt_le hS ν x y
  have h0 : 0 ≤ hellingerExt hS ν x y := dist_nonneg
  have : hellingerExt hS ν x y ^ 2 ≤ (dist x y / 2) ^ 2 := pow_le_pow_left₀ h0 h 2
  have e : (dist x y / 2) ^ 2 = dist x y ^ 2 / 4 := by ring
  linarith

/-- **The sharp `n`-sample testing bound**: `∫ φ dQ_x^{⊗n} − ∫ φ dQ_y^{⊗n} ≤ √(1 − A(x,y)^{2n})`. -/
theorem integral_sampleLaw_sub_le_sqrt (n : ℕ) (x y : FisherCompletion hS ν)
    {φ : (Fin n → X) → ℝ} (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (∫ z, φ z ∂sampleLaw hS ν n x) - ∫ z, φ z ∂sampleLaw hS ν n y ≤
      √(1 - (affinityExt hS ν x y ^ n) ^ 2) := by
  rw [sampleLaw_eq_rootLaw, sampleLaw_eq_rootLaw]
  have h := integral_rootLaw_sub_le_sqrt _ (norm_prodRoot ν n (norm_rootDensExt hS ν x))
    (norm_prodRoot ν n (norm_rootDensExt hS ν y)) hφm hφ0 hφ1
  have e : ∫ z, prodRoot ν n (rootDensExt hS ν x) z * prodRoot ν n (rootDensExt hS ν y) z
      ∂(Measure.pi fun _ : Fin n ↦ ν) = affinityExt hS ν x y ^ n := by
    rw [← inner_eq_integral_mul, inner_prodRoot]
    rfl
  rwa [e] at h

/-- **Every test on `n` samples has error at least `(1 − √(1 − A(x,y)^{2n}))/2`.** -/
theorem testing_error_sampleLaw_ge_sqrt (n : ℕ) (x y : FisherCompletion hS ν)
    {φ : (Fin n → X) → ℝ} (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(1 - (affinityExt hS ν x y ^ n) ^ 2)) / 2 ≤
      ((∫ z, φ z ∂sampleLaw hS ν n x) + ∫ z, (1 - φ z) ∂sampleLaw hS ν n y) / 2 := by
  have hφb : ∀ z, ‖φ z‖ ≤ 1 := fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 z)]
    exact hφ1 z
  have hint : Integrable φ (sampleLaw hS ν n y) :=
    Integrable.of_bound hφm.aestronglyMeasurable 1 (Eventually.of_forall hφb)
  rw [integral_sub (integrable_const 1) hint, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  have h := integral_sampleLaw_sub_le_sqrt hS ν n y x hφm hφ0 hφ1
  have e : affinityExt hS ν y x = affinityExt hS ν x y := by
    unfold affinityExt
    exact integral_congr_ae (Eventually.of_forall fun z ↦ mul_comm _ _)
  rw [e] at h
  linarith

end Completion

end Laplace.Multi
