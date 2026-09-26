/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherAccessibility

/-!
# The Hellinger comparison

For nonnegative densities `p, q` the squared Hellinger distance `d_H² = ∫ (√p − √q)²` satisfies
`d_H² ≤ ‖p − q‖₁ ≤ √(2(∫p + ∫q)) d_H` (`hellingerSq_le_integral_abs_sub`,
`integral_abs_sub_le_sqrt_mul_sqrt_hellingerSq`), so for probability densities `‖p − q‖₁ ≤ 2 d_H`.
Hence the `L¹` and Hellinger topologies coincide on the completed family: along the charged polytope
`M ↦ dq_M/dν` is Hellinger-continuous (`tendsto_hellingerSq_projDens`), and Hellinger convergence of
projections is `L¹` convergence (`tendsto_projL1_of_tendsto_hellingerSq`). The completed family is
therefore the (ambient) Hellinger closure of the interior exponential family.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Pointwise

theorem abs_sub_eq_abs_sqrt_sub_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| = |√a - √b| * (√a + √b) := by
  have h : (√a - √b) * (√a + √b) = √a * √a - √b * √b := by ring
  rw [Real.mul_self_sqrt ha, Real.mul_self_sqrt hb] at h
  rw [← h, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]

/-- `(√a − √b)² ≤ |a − b|` for `a, b ≥ 0`. -/
theorem sq_sqrt_sub_sqrt_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (√a - √b) ^ 2 ≤ |a - b| := by
  rw [abs_sub_eq_abs_sqrt_sub_mul ha hb, ← sq_abs, sq]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |√a - √b| ≤ |√a| + |√b| := abs_sub _ _
    _ = √a + √b := by rw [abs_of_nonneg (Real.sqrt_nonneg a), abs_of_nonneg (Real.sqrt_nonneg b)]

/-- `(√a + √b)² ≤ 2(a + b)` for `a, b ≥ 0`. -/
theorem sq_sqrt_add_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (√a + √b) ^ 2 ≤ 2 * (a + b) := by
  nlinarith [sq_nonneg (√a - √b), Real.sq_sqrt ha, Real.sq_sqrt hb]

theorem sq_sqrt_sub_sqrt_le_two_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (√a - √b) ^ 2 ≤ 2 * (a + b) := by
  nlinarith [sq_nonneg (√a + √b), Real.sq_sqrt ha, Real.sq_sqrt hb]

end Pointwise

section Hellinger

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- The squared Hellinger distance `∫ (√p − √q)² dν`. -/
noncomputable def hellingerSq (p q : X → ℝ) : ℝ := ∫ x, (√(p x) - √(q x)) ^ 2 ∂ν

variable {ν} {p q : X → ℝ} (hp : Measurable p) (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x)
  (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p ν) (hqi : Integrable q ν)
include hp hq hp0 hq0 hpi hqi

omit hp hq hp0 hq0 hpi hqi in
theorem hellingerSq_nonneg : 0 ≤ hellingerSq ν p q := integral_nonneg fun _ ↦ sq_nonneg _

omit hp hq in
/-- **`d_H² ≤ ‖p − q‖₁`.** -/
theorem hellingerSq_le_integral_abs_sub : hellingerSq ν p q ≤ ∫ x, |p x - q x| ∂ν :=
  integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _) (hpi.sub hqi).abs
    (Eventually.of_forall fun x ↦ sq_sqrt_sub_sqrt_le_abs_sub (hp0 x) (hq0 x))

/-- **`‖p − q‖₁ ≤ √(2(∫p + ∫q)) · d_H`** (Cauchy–Schwarz on `|p − q| = |√p − √q|(√p + √q)`). -/
theorem integral_abs_sub_le_sqrt_mul_sqrt_hellingerSq :
    ∫ x, |p x - q x| ∂ν ≤
      √(2 * ((∫ x, p x ∂ν) + ∫ x, q x ∂ν)) * √(hellingerSq ν p q) := by
  have hf_meas : Measurable fun x ↦ |√(p x) - √(q x)| :=
    ((Real.continuous_sqrt.measurable.comp hp).sub (Real.continuous_sqrt.measurable.comp hq)).abs
  have hg_meas : Measurable fun x ↦ √(p x) + √(q x) :=
    (Real.continuous_sqrt.measurable.comp hp).add (Real.continuous_sqrt.measurable.comp hq)
  have hint2 : Integrable (fun x ↦ 2 * (p x + q x)) ν := (hpi.add hqi).const_mul 2
  have hf2 : Integrable (fun x ↦ |√(p x) - √(q x)| ^ 2) ν := by
    refine hint2.mono' (hf_meas.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_abs, sq_abs]
    exact sq_sqrt_sub_sqrt_le_two_mul (hp0 x) (hq0 x)
  have hg2 : Integrable (fun x ↦ (√(p x) + √(q x)) ^ 2) ν := by
    refine hint2.mono' (hg_meas.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_sqrt_add_sqrt_le (hp0 x) (hq0 x)
  have hf : MemLp (fun x ↦ |√(p x) - √(q x)|) (ENNReal.ofReal 2) ν := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hf_meas.aestronglyMeasurable).2 hf2
  have hg : MemLp (fun x ↦ √(p x) + √(q x)) (ENNReal.ofReal 2) ν := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hg_meas.aestronglyMeasurable).2 hg2
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x ↦ abs_nonneg _)
    (Eventually.of_forall fun x ↦ add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hf hg
  have hL : ∫ x, |√(p x) - √(q x)| * (√(p x) + √(q x)) ∂ν = ∫ x, |p x - q x| ∂ν :=
    integral_congr_ae (Eventually.of_forall fun x ↦
      (abs_sub_eq_abs_sqrt_sub_mul (hp0 x) (hq0 x)).symm)
  rw [hL] at hCS
  refine hCS.trans ?_
  have e1 : (∫ x, |√(p x) - √(q x)| ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) = √(hellingerSq ν p q) := by
    rw [Real.sqrt_eq_rpow, hellingerSq]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [Real.rpow_two, sq_abs])
  have e2 : (∫ x, (√(p x) + √(q x)) ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) ≤
      √(2 * ((∫ x, p x ∂ν) + ∫ x, q x ∂ν)) := by
    rw [Real.sqrt_eq_rpow]
    refine Real.rpow_le_rpow (integral_nonneg fun x ↦ Real.rpow_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _) ?_ (by norm_num)
    calc ∫ x, (√(p x) + √(q x)) ^ (2 : ℝ) ∂ν = ∫ x, (√(p x) + √(q x)) ^ 2 ∂ν :=
          integral_congr_ae (Eventually.of_forall fun x ↦ by
            beta_reduce
            rw [Real.rpow_two])
      _ ≤ ∫ x, 2 * (p x + q x) ∂ν :=
          integral_mono hg2 hint2 fun x ↦ sq_sqrt_add_sqrt_le (hp0 x) (hq0 x)
      _ = 2 * ((∫ x, p x ∂ν) + ∫ x, q x ∂ν) := by rw [integral_const_mul, integral_add hpi hqi]
  rw [e1]
  calc √(hellingerSq ν p q) * (∫ x, (√(p x) + √(q x)) ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) ≤
        √(hellingerSq ν p q) * √(2 * ((∫ x, p x ∂ν) + ∫ x, q x ∂ν)) :=
        mul_le_mul_of_nonneg_left e2 (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

/-- **`‖p − q‖₁ ≤ 2 d_H` for probability densities.** -/
theorem integral_abs_sub_le_two_sqrt_hellingerSq (h1 : ∫ x, p x ∂ν = 1) (h2 : ∫ x, q x ∂ν = 1) :
    ∫ x, |p x - q x| ∂ν ≤ 2 * √(hellingerSq ν p q) := by
  have h := integral_abs_sub_le_sqrt_mul_sqrt_hellingerSq hp hq hp0 hq0 hpi hqi
  rw [h1, h2, show (2 : ℝ) * (1 + 1) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  exact h

end Hellinger

section Family

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **Hellinger is dominated by `L¹` on the completed family.** -/
theorem hellingerSq_projDens_le_norm (M M' : J → ℝ) :
    hellingerSq ν (projDens hS ν M) (projDens hS ν M') ≤ ‖projL1 hS ν M - projL1 hS ν M'‖ := by
  rw [norm_projL1_sub]
  exact hellingerSq_le_integral_abs_sub (projDens_nonneg hS ν M) (projDens_nonneg hS ν M')
    (integrable_projDens hS ν M) (integrable_projDens hS ν M')

/-- **`L¹` is dominated by Hellinger on the completed family.** -/
theorem norm_projL1_sub_le_two_sqrt_hellingerSq {M M' : J → ℝ} (hM : genRate ν S M ≠ ⊤)
    (hM' : genRate ν S M' ≠ ⊤) :
    ‖projL1 hS ν M - projL1 hS ν M'‖ ≤
      2 * √(hellingerSq ν (projDens hS ν M) (projDens hS ν M')) := by
  rw [norm_projL1_sub]
  exact integral_abs_sub_le_two_sqrt_hellingerSq (measurable_projDens hS ν M)
    (measurable_projDens hS ν M') (projDens_nonneg hS ν M) (projDens_nonneg hS ν M')
    (integrable_projDens hS ν M) (integrable_projDens hS ν M')
    (integral_eq_one_of_isProbabilityMeasure_withDensity ν (projDens_nonneg hS ν M)
      (integrable_projDens hS ν M) (isProbabilityMeasure_withDensity_projDens hS ν hM))
    (integral_eq_one_of_isProbabilityMeasure_withDensity ν (projDens_nonneg hS ν M')
      (integrable_projDens hS ν M') (isProbabilityMeasure_withDensity_projDens hS ν hM'))

variable (V : Finset (J → ℝ)) [Nonempty V] (hV : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hV

/-- **The completed family is Hellinger-continuous on the charged polytope.** -/
theorem tendsto_hellingerSq_projDens {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {m : ℕ → J → ℝ} (hm : ∀ n, m n ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hlim : Tendsto m atTop (𝓝 M)) :
    Tendsto (fun n ↦ hellingerSq ν (projDens hS ν (m n)) (projDens hS ν M)) atTop (𝓝 0) := by
  have h := tendsto_projL1_of_tendsto hS ν V hV hM hm hlim
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  exact squeeze_zero (fun n ↦ hellingerSq_nonneg) (fun n ↦ hellingerSq_projDens_le_norm hS ν _ _) h

omit [Nonempty V] in
/-- **Hellinger convergence of projections is `L¹` convergence.** -/
theorem tendsto_projL1_of_tendsto_hellingerSq {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {m : ℕ → J → ℝ} (hm : ∀ n, m n ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hH : Tendsto (fun n ↦ hellingerSq ν (projDens hS ν (m n)) (projDens hS ν M)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ projL1 hS ν (m n)) atTop (𝓝 (projL1 hS ν M)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n ↦ 2 * √(hellingerSq ν (projDens hS ν (m n)) (projDens hS ν M)))
      atTop (𝓝 0) := by
    have := (hH.sqrt).const_mul 2
    simpa using this
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hlim
  exact norm_projL1_sub_le_two_sqrt_hellingerSq hS ν
    (genRate_ne_top_of_mem_convexHull_vertices hS ν V hV (hm n))
    (genRate_ne_top_of_mem_convexHull_vertices hS ν V hV hM)

end Family

end Laplace.Multi
