/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SamplingResolution
import Laplace.Multi.EmpiricalMoments

/-!
# Sampling resolution: wall-crossing probabilities and exact boundary hits

Two honest statements about the sampling noise of the structural coordinate `M̂_n = (1/n) ∑ S(X_i)`
of `n` i.i.d. samples from a data law `D`.

* **Decision walls.** For an affine wall `⟨a, m⟩ = b` with the truth on the side
  `⟨a, M_D⟩ − b = δ > 0`, Chebyshev's inequality in the direction `a` bounds the probability that
  the empirical coordinate lands on the wrong side by `Var_D⟨a,S⟩ / (n δ²)`
  (`measureReal_dotJ_sampleResponse_le_le`): the relevant margin is the wall distance in the data
  variance of the wall direction.
* **Boundary faces.** For an exposed face `⟨u, ·⟩ = β` of the moment polytope (`⟨u, S⟩ ≤ β` on the
  data), the empirical coordinate lies on the face **iff every observation does**
  (`dotJ_sampleResponse_eq_iff`), so under i.i.d. sampling the probability of landing on the face is
  exactly `P_D(⟨u,S⟩ = β)^n` (`measureReal_dotJ_sampleResponse_eq`): a finite structural coordinate
  fails to exist with an exact combinatorial probability, exponentially small unless the data law
  charges the face fully.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Wall

variable {X : Type*} {J : Type*} {Ω : Type*} [MeasurableSpace X] [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hS hXm hid hlaw

omit [IsProbabilityMeasure P] [IsProbabilityMeasure D] hid hlaw in
theorem measurable_dotJ_sampleResponse (n : ℕ) (a : J → ℝ) :
    Measurable fun ω ↦ dotJ a (sampleResponse S Xs n ω) := by
  have h := measurable_sampleResponse hS Xs hXm n
  exact Finset.measurable_sum _ fun j _ ↦ measurable_const.mul ((measurable_pi_apply j).comp h)

/-- **The wall-crossing probability**: if the truth lies at distance `δ = ⟨a, M_D⟩ − b > 0` from the
affine wall `⟨a, m⟩ = b`, the empirical coordinate lands on the wrong side with probability at most
`Var_D⟨a,S⟩ / (n δ²)`. -/
theorem measureReal_dotJ_sampleResponse_le_le (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (a : J → ℝ) {b : ℝ} (hb : b < dotJ a (fun j ↦ ∫ x, S j x ∂D)) :
    P.real {ω | dotJ a (sampleResponse S Xs n ω) ≤ b} ≤
      lawCov D (dirLoss S a) (dirLoss S a) / (n * (dotJ a (fun j ↦ ∫ x, S j x ∂D) - b) ^ 2) := by
  set m : J → ℝ := fun j ↦ ∫ x, S j x ∂D with hm
  set δ := dotJ a m - b with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  -- the centred direction as a random variable
  set Y : Ω → ℝ := fun ω ↦ dotJ a (fun j ↦ sampleResponse S Xs n ω j - m j) ^ 2 with hY
  have hYm : Measurable Y := by
    have h := measurable_sampleResponse hS Xs hXm n
    refine (Finset.measurable_sum _ fun j _ ↦ measurable_const.mul
      (((measurable_pi_apply j).comp h).sub measurable_const)).pow_const 2
  have hYint : Integrable Y P := by
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ ω, |Y ω| ≤ B := by
      choose K hK using fun j ↦ (hS j).2
      refine ⟨(∑ j, |a j| * (2 * K j)) ^ 2, fun ω ↦ ?_⟩
      rw [hY, abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact abs_sampleResponse_sub_le D Xs hn j (hK j) ω
    exact Integrable.of_bound hYm.aestronglyMeasurable B (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs]; exact hB ω)
  have hEY : ∫ ω, Y ω ∂P = lawCov D (dirLoss S a) (dirLoss S a) / n :=
    integral_sq_dotJ_sampleResponse_sub hS P D Xs hXm hid hlaw hind hn a
  -- the wrong side is contained in the Chebyshev event
  have hsub : {ω | dotJ a (sampleResponse S Xs n ω) ≤ b} ⊆ {ω | δ ^ 2 ≤ Y ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have e : dotJ a (fun j ↦ sampleResponse S Xs n ω j - m j) =
        dotJ a (sampleResponse S Xs n ω) - dotJ a m := (isLinearMap_dotJ a).map_sub _ _
    rw [hY]
    simp only
    rw [e]
    have : dotJ a (sampleResponse S Xs n ω) - dotJ a m ≤ -δ := by rw [hδ]; linarith
    nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := Y)
    (ae_of_all _ fun ω ↦ sq_nonneg _) hYint (δ ^ 2)
  rw [hEY] at hmarkov
  have hmono : P.real {ω | dotJ a (sampleResponse S Xs n ω) ≤ b} ≤ P.real {ω | δ ^ 2 ≤ Y ω} :=
    measureReal_mono hsub
  have hδ2 : 0 < δ ^ 2 := by positivity
  calc P.real {ω | dotJ a (sampleResponse S Xs n ω) ≤ b}
      ≤ P.real {ω | δ ^ 2 ≤ Y ω} := hmono
    _ ≤ (lawCov D (dirLoss S a) (dirLoss S a) / n) / δ ^ 2 := by
        rw [le_div_iff₀ hδ2, mul_comm]
        exact hmarkov
    _ = lawCov D (dirLoss S a) (dirLoss S a) / (n * δ ^ 2) := by rw [div_div]

end Wall

section Face

variable {X : Type*} {J : Type*} {Ω : Type*} [MeasurableSpace X] [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hS hXm hid hlaw

omit [MeasurableSpace X] hS [MeasurableSpace Ω] [IsProbabilityMeasure P] [IsProbabilityMeasure D]
  hXm hid hlaw in
/-- The empirical coordinate in a direction is the average of the sample coordinates. -/
theorem dotJ_sampleResponse (u : J → ℝ) (n : ℕ) (ω : Ω) :
    dotJ u (sampleResponse S Xs n ω) =
      (∑ i ∈ Finset.range n, dotJ u (fun j ↦ S j (Xs i ω))) / n := by
  simp only [dotJ, sampleResponse, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  rw [Finset.sum_comm]

omit [MeasurableSpace X] hS [MeasurableSpace Ω] [IsProbabilityMeasure P] [IsProbabilityMeasure D]
  hXm hid hlaw in
/-- **The empirical coordinate lies on an exposed face iff every observation does**: for a
supporting direction `⟨u, S⟩ ≤ β`, `⟨u, M̂_n⟩ = β ↔ ∀ i < n, ⟨u, S(X_i)⟩ = β`. -/
theorem dotJ_sampleResponse_eq_iff (u : J → ℝ) {β : ℝ} (hβ : ∀ x, dotJ u (fun j ↦ S j x) ≤ β)
    {n : ℕ} (hn : 0 < n) (ω : Ω) :
    dotJ u (sampleResponse S Xs n ω) = β ↔
      ∀ i ∈ Finset.range n, dotJ u (fun j ↦ S j (Xs i ω)) = β := by
  rw [dotJ_sampleResponse, div_eq_iff (by exact_mod_cast hn.ne')]
  have e : β * n = ∑ _i ∈ Finset.range n, β := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  rw [e]
  exact Finset.sum_eq_sum_iff_of_le fun i _ ↦ hβ _

omit [IsProbabilityMeasure D] hXm hid hlaw in
theorem measurableSet_dotJ_statistic_eq (u : J → ℝ) (β : ℝ) :
    MeasurableSet {x | dotJ u (fun j ↦ S j x) = β} :=
  measurableSet_eq_fun (Finset.measurable_sum _ fun j _ ↦ measurable_const.mul (hS j).1)
    measurable_const

omit [IsProbabilityMeasure P] [IsProbabilityMeasure D] in
/-- **The exact face-hit probability**: under i.i.d. sampling the empirical coordinate lands on the
exposed face `⟨u, ·⟩ = β` with probability `P_D(⟨u,S⟩ = β)^n`. -/
theorem measure_dotJ_sampleResponse_eq (hind : iIndepFun Xs P) (u : J → ℝ) {β : ℝ}
    (hβ : ∀ x, dotJ u (fun j ↦ S j x) ≤ β) {n : ℕ} (hn : 0 < n) :
    P {ω | dotJ u (sampleResponse S Xs n ω) = β} = D {x | dotJ u (fun j ↦ S j x) = β} ^ n := by
  set A : Set X := {x | dotJ u (fun j ↦ S j x) = β} with hA
  have hAm : MeasurableSet A := measurableSet_dotJ_statistic_eq hS u β
  have e : {ω | dotJ u (sampleResponse S Xs n ω) = β} =
      ⋂ i ∈ Finset.range n, Xs i ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, hA]
    exact dotJ_sampleResponse_eq_iff Xs u hβ hn ω
  rw [e, hind.measure_inter_preimage_eq_mul (Finset.range n) fun _ _ ↦ hAm]
  have hi : ∀ i, P (Xs i ⁻¹' A) = D A := fun i ↦ by
    rw [← map_Xs_eq P D Xs hid hlaw i, Measure.map_apply (hXm i) hAm]
  simp only [hi, Finset.prod_const, Finset.card_range]

omit [IsProbabilityMeasure P] [IsProbabilityMeasure D] in
/-- The exact face-hit probability in real form. -/
theorem measureReal_dotJ_sampleResponse_eq (hind : iIndepFun Xs P) (u : J → ℝ) {β : ℝ}
    (hβ : ∀ x, dotJ u (fun j ↦ S j x) ≤ β) {n : ℕ} (hn : 0 < n) :
    P.real {ω | dotJ u (sampleResponse S Xs n ω) = β} =
      D.real {x | dotJ u (fun j ↦ S j x) = β} ^ n := by
  rw [measureReal_def, measureReal_def, measure_dotJ_sampleResponse_eq hS P D Xs hXm hid hlaw hind
    u hβ hn, ENNReal.toReal_pow]

omit [IsProbabilityMeasure P] [IsProbabilityMeasure D] in
/-- If the data law does not charge the face fully, the face-hit probability decays exponentially
in the sample size. -/
theorem measureReal_dotJ_sampleResponse_eq_lt_one (hind : iIndepFun Xs P) (u : J → ℝ) {β : ℝ}
    (hβ : ∀ x, dotJ u (fun j ↦ S j x) ≤ β) (hlt : D.real {x | dotJ u (fun j ↦ S j x) = β} < 1)
    {n : ℕ} (hn : 0 < n) :
    P.real {ω | dotJ u (sampleResponse S Xs n ω) = β} < 1 := by
  rw [measureReal_dotJ_sampleResponse_eq hS P D Xs hXm hid hlaw hind u hβ hn]
  exact pow_lt_one₀ measureReal_nonneg hlt hn.ne'

end Face

end Laplace.Multi
