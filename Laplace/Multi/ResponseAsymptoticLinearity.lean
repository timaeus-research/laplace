/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFaceCarried
import Laplace.Multi.ResponseStratifiedTransport
import Laplace.Multi.ResponseObservableIIDExpansion
import Laplace.Multi.ResponseEmpiricalRisk
import Laplace.Multi.IIDFourthMoment

/-!
# Face-adaptive asymptotic linearity of the plug-in estimator

Let `D` be any data law on the finite configuration, `m_D` its mean, `A = supp q*(m_D)` the atoms
of the minimal face of `m_D`, and `u_F = u_F^{A}(m_D)` the tangential response field of a bounded
observable `F` at `m_D`. The **face influence function** of `F` is
`ψ_F(x) = ⟨u_F, S(x) − m_D⟩` (`faceInfluence`).

* **The quadratic remainder on the face polytope** (`exists_face_quadratic_remainder`): for every
  mean `N` of the face polytope `conv S(A)`,
  `|E_{R_N}F − E_{R_{m_D}}F − ⟨u_F, N − m_D⟩| ≤ C ‖N − m_D‖²`,
  from the cubic expansion of the interior calculus of the face law `ν_A` near `m_D` and the global
  Lipschitz bound far from it.
* **Asymptotic linearity** (`empiricalObs_sub_eq_sum_faceInfluence_add`,
  `integral_sq_linearityRemainder_le`): since the samples lie in `A` almost surely, the plug-in
  estimator `Ψ̂_F = E_{R_{M̂_n}}F` of `n` i.i.d. samples satisfies
  `Ψ̂_F − Ψ_F(D) = (1/n) ∑ᵢ ψ_F(Xᵢ) + ℛ_n`, `E_D ℛ_n² ≤ 3 C² |J|⁴ (2B)⁴ / n²`.
* **First-order unbiasedness and the sharp risk** (`abs_integral_empiricalObs_sub_le`,
  `abs_integral_sq_empiricalObs_sub_sub_le`): `|E_D Ψ̂_F − Ψ_F(D)| ≤ C |J|² (2B)² / n` and
  `|E_D (Ψ̂_F − Ψ_F(D))² − Var_D(ψ_F)/n| ≤ (Var_D ψ_F + 2 C₄) / n^{3/2}`.

The theorem holds at **every** data law, boundary means included: the estimator only explores the
face on which the data mean is relatively interior, and its statistics are those of the interior
problem of the face law. No central limit theorem enters; the constants depend on the face.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Remainder

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x}) (D : Measure X) [IsProbabilityMeasure D]
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hS hν
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] in
theorem dotJ_finset_sum {ι : Type*} (e : J → ℝ) (s : Finset ι) (g : ι → J → ℝ) :
    dotJ e (∑ i ∈ s, g i) = ∑ i ∈ s, dotJ e (g i) := by
  simp only [dotJ, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hS hν
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] in
theorem dotJ_sub_right (e a b : J → ℝ) : dotJ e (a - b) = dotJ e a - dotJ e b := by
  simp only [dotJ, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- **The quadratic remainder on the face polytope**: for every mean `N` of the face polytope of
`m_D`, `|E_{R_N}F − E_{R_{m_D}}F − ⟨u_F, N − m_D⟩| ≤ C ‖N − m_D‖²`. -/
theorem exists_face_quadratic_remainder {F : X → ℝ} (hF : Bdd F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2 := by
  have hM : mD ∈ hull := dataLawMean_mem_polytope hS ν hν D
  have hνA : IsProbabilityMeasure (faceMeasure ν (supportSet hS ν mD)) :=
    isProbabilityMeasure_faceMeasure ν (measure_supportSet_ne_zero hS ν hν hM)
  have hrel : mD ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν (supportSet hS ν mD)) (fun _ ↦ (1 : ℝ)) S) := by
    rw [intrinsicInterior_momentBody_faceMeasure hS ν hν]
    exact mem_intrinsicInterior_carriedResponses_supportSet hS ν hν hM
  set θ₀ := responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos (faceMeasure ν (supportSet hS ν mD))) hS mD with hθ₀
  have hmean : meanMap (faceMeasure ν (supportSet hS ν mD)) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ))
      S 1 (θ₀ : J → ℝ) = mD :=
    meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos (faceMeasure ν (supportSet hS ν mD))) hS hrel
  obtain ⟨δ, hδ, hball, K, hK, hcub⟩ :=
    exists_obsChart_cubic_remainder hS (faceMeasure ν (supportSet hS ν mD)) hF θ₀
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_responseObs hS ν hν hF
  set CH := ‖obsHessCLM hS (faceMeasure ν (supportSet hS ν mD)) hF θ₀‖ with hCH
  set u := tangentField hS ν F mD with hu
  have hu_eq : u = (regressionDir hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ : J → ℝ) := by
    rw [hu, tangentField, faceField_eq]
  refine ⟨max (CH / 2 + K * δ) ((L + ∑ j, |u j|) / δ), le_max_of_le_left (by positivity),
    fun N hN ↦ ?_⟩
  have hNh : N ∈ hull := carriedResponses_subset_hull (S := S) _ hN
  have hz : N - mD ∈ dirSpan (faceMeasure ν (supportSet hS ν mD)) (fun _ ↦ (1 : ℝ)) S := by
    rw [dirSpan_faceMeasure_eq_vectorSpan_image hS ν hν, ← vectorSpan_carriedResponses S]
    simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hN
      (mem_carriedResponses_supportSet hS ν hν hM)
  -- the base-`ν` responses on the face are the face-law responses
  have hfN := responseProjection_faceMeasure_of_mem_carriedResponses hS ν hν hM hN
  have hfM := responseProjection_faceMeasure_of_mem_carriedResponses hS ν hν hM
    (mem_carriedResponses_supportSet hS ν hν hM)
  by_cases hsmall : ‖N - mD‖ ≤ δ
  · -- the cubic expansion of the face law
    have hzΩ := hball ⟨N - mD, hz⟩ hsmall
    have hNΩ : N ∈ intrinsicInterior ℝ
        (momentBody (faceMeasure ν (supportSet hS ν mD)) (fun _ ↦ (1 : ℝ)) S) := by
      have := hzΩ
      rw [hmean] at this
      simpa using this
    have e1 : ∫ x, F x ∂responseProjection hS ν N =
        obsChart hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ ⟨N - mD, hz⟩ := by
      rw [← hfN, responseProjection_eq_familyMeasure_responseTheta hS _ hNΩ]
      simp only [obsChart, hmean, add_sub_cancel]
    have e2 : ∫ x, F x ∂responseProjection hS ν mD =
        obsChart hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ 0 := by
      rw [← hfM, responseProjection_eq_familyMeasure_responseTheta hS _ hrel, obsChart_zero]
    have hc := hcub ⟨N - mD, hz⟩ hsmall
    have hH := abs_obsHessForm_le hS (faceMeasure ν (supportSet hS ν mD)) hF θ₀ ⟨N - mD, hz⟩
    rw [← hu_eq] at hc
    rw [e1, e2]
    calc |obsChart hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ ⟨N - mD, hz⟩ -
          obsChart hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ 0 -
          dotJ u (N - mD)|
        ≤ |obsChart hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ ⟨N - mD, hz⟩ -
            obsChart hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ 0 -
            dotJ u (N - mD) -
            (1 / 2 : ℝ) * obsHessForm hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ ⟨N - mD, hz⟩|
          + |(1 / 2 : ℝ) * obsHessForm hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ ⟨N - mD, hz⟩|
          := by
            have := abs_add_le (obsChart hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ ⟨N - mD, hz⟩ -
              obsChart hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ 0 -
              dotJ u (N - mD) -
              (1 / 2 : ℝ) * obsHessForm hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ ⟨N - mD, hz⟩)
              ((1 / 2 : ℝ) * obsHessForm hS (faceMeasure ν (supportSet hS ν mD)) F θ₀ ⟨N - mD, hz⟩)
            rwa [sub_add_cancel] at this
      _ ≤ K * ‖N - mD‖ ^ 3 + (1 / 2 : ℝ) * (CH * ‖N - mD‖ ^ 2) := by
            refine add_le_add hc ?_
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            exact mul_le_mul_of_nonneg_left hH (by norm_num)
      _ ≤ (CH / 2 + K * δ) * ‖N - mD‖ ^ 2 := by
            have h3 : ‖N - mD‖ ^ 3 ≤ δ * ‖N - mD‖ ^ 2 := by
              rw [pow_succ, mul_comm]
              exact mul_le_mul_of_nonneg_right hsmall (by positivity)
            nlinarith [mul_le_mul_of_nonneg_left h3 hK]
      _ ≤ max (CH / 2 + K * δ) ((L + ∑ j, |u j|) / δ) * ‖N - mD‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- far from the mean: the Lipschitz bound
    push Not at hsmall
    have h1 := hL mD hM N hNh
    have h2 := abs_dotJ_le u (N - mD)
    calc |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
          dotJ u (N - mD)|
        ≤ |(∫ x, F x ∂responseProjection hS ν N) - ∫ x, F x ∂responseProjection hS ν mD| +
          |dotJ u (N - mD)| := abs_sub _ _
      _ ≤ L * ‖N - mD‖ + (∑ j, |u j|) * ‖N - mD‖ := add_le_add h1 h2
      _ = (L + ∑ j, |u j|) / δ * (δ * ‖N - mD‖) := by field_simp
      _ ≤ (L + ∑ j, |u j|) / δ * ‖N - mD‖ ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [sq]
            exact mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg _)
      _ ≤ max (CH / 2 + K * δ) ((L + ∑ j, |u j|) / δ) * ‖N - mD‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Remainder

section Sampling

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  (ν : Measure X) [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x}) [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X) [IsProbabilityMeasure D]
  (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : iIndepFun Xs P)
include hS hν hXm hid hlaw hind

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

/-- The empirical displacement `M̂_n − m_D`. -/
local notation "raw" n => (fun ω : Ω ↦ fun j : J ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)

/-- **The face influence function** `ψ_F(x) = ⟨u_F, S(x) − m_D⟩`, with `u_F` the tangential
response field of `F` at the data mean. -/
noncomputable def faceInfluence (F : X → ℝ) (x : X) : ℝ :=
  dotJ (tangentField hS ν F mD) (statPoint S x - mD)

/-- **The linearity remainder** `ℛ_n = Ψ̂_F − Ψ_F(D) − ⟨u_F, M̂_n − m_D⟩`. -/
noncomputable def linearityRemainder (F : X → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  empiricalObs hS ν Xs F n ω - (∫ x, F x ∂responseProjection hS ν mD) -
    dotJ (tangentField hS ν F mD) ((raw n) ω)

omit [IsProbabilityMeasure P] hind in
/-- **The empirical mean lies in the face polytope of the data mean, almost surely.** -/
theorem ae_sampleResponse_mem_carriedResponses {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂P, sampleResponse S Xs n ω ∈ carriedResponses S (supportSet hS ν mD) := by
  have hA : D (supportSet hS ν mD)ᶜ = 0 := measure_compl_supportSet_dataMean hS ν hν D
  have hi : ∀ i, ∀ᵐ ω ∂P, Xs i ω ∈ supportSet hS ν mD := by
    intro i
    have hD : ∀ᵐ y ∂D, y ∈ supportSet hS ν mD := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA] with y hy
      exact Set.notMem_compl_iff.1 hy
    refine ae_of_ae_map (hXm i).aemeasurable ?_
    rw [map_Xs_eq P D Xs hid hlaw i]
    exact hD
  filter_upwards [ae_all_iff.2 hi] with ω hω
  have e : sampleResponse S Xs n ω =
      ∑ i ∈ Finset.range n, (1 / (n : ℝ)) • statPoint S (Xs i ω) := by
    funext j
    simp only [sampleResponse, Finset.sum_apply, Pi.smul_apply, statPoint, smul_eq_mul,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e, carriedResponses_eq_convexHull_image]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ ↦ by positivity) ?_
    fun i _ ↦ subset_convexHull ℝ _ ⟨_, hω i, rfl⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν [MeasurableSpace Ω]
  [IsProbabilityMeasure D] hXm hid hlaw hind in
/-- **The linear term is the empirical average of the face influence function.** -/
theorem dotJ_tangentField_sampleResponse_sub (F : X → ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    dotJ (tangentField hS ν F mD) ((raw n) ω) =
      (∑ i ∈ Finset.range n, faceInfluence hS ν D F (Xs i ω)) / n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  beta_reduce
  have e : (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) =
      ∑ i ∈ Finset.range n, (1 / (n : ℝ)) • (statPoint S (Xs i ω) - mD) := by
    funext j
    simp only [sampleResponse, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, statPoint,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.sum_div]
    field_simp
  rw [e, dotJ_finset_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ ↦ by
    unfold faceInfluence dotJ
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν [MeasurableSpace Ω]
  [IsProbabilityMeasure P] [IsProbabilityMeasure D] hXm hid hlaw hind in
/-- **Asymptotic linearity of the plug-in estimator**:
`Ψ̂_F − Ψ_F(D) = (1/n) ∑ᵢ ψ_F(Xᵢ) + ℛ_n`. -/
theorem empiricalObs_sub_eq_sum_faceInfluence_add (F : X → ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD =
      (∑ i ∈ Finset.range n, faceInfluence hS ν D F (Xs i ω)) / n +
        linearityRemainder hS ν D Xs F n ω := by
  rw [← dotJ_tangentField_sampleResponse_sub hS ν D Xs F hn ω]
  unfold linearityRemainder
  ring

omit [IsProbabilityMeasure P] hind in
/-- The linearity remainder is quadratic in the empirical displacement, almost surely. -/
theorem ae_abs_linearityRemainder_le {F : X → ℝ} {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂P, |linearityRemainder hS ν D Xs F n ω| ≤ C * ‖(raw n) ω‖ ^ 2 := by
  filter_upwards [ae_sampleResponse_mem_carriedResponses hS ν hν P D Xs hXm hid hlaw hn]
    with ω hω
  have := hC _ hω
  unfold linearityRemainder empiricalObs
  beta_reduce
  rw [show (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) = sampleResponse S Xs n ω - mD
    from rfl]
  exact this

variable {B : ℝ} (hB : ∀ j x, |S j x| ≤ B)
include hB

omit [IsProbabilityMeasure D] hid hlaw hind hB in
theorem measurable_linearityRemainder (F : X → ℝ) {n : ℕ} (hn : 0 < n) :
    Measurable (linearityRemainder hS ν D Xs F n) := by
  unfold linearityRemainder
  refine ((measurable_empiricalObs hS ν hν Xs hXm F hn).sub measurable_const).sub ?_
  unfold dotJ
  exact Finset.measurable_sum _ fun j _ ↦ measurable_const.mul
    ((measurable_pi_apply j).comp (measurable_sampleResponse_sub hS D Xs hXm))

/-- **The remainder is `O(1/n)` in mean square**: `E_D ℛ_n² ≤ C² · 3 |J|⁴ (2B)⁴ / n²`. -/
theorem integral_sq_linearityRemainder_le {F : X → ℝ} {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    ∫ ω, linearityRemainder hS ν D Xs F n ω ^ 2 ∂P ≤
      C ^ 2 * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4 / n ^ 2) := by
  have hae := ae_abs_linearityRemainder_le hS ν hν P D Xs hXm hid hlaw hC hn
  have hae2 : ∀ᵐ ω ∂P, linearityRemainder hS ν D Xs F n ω ^ 2 ≤ C ^ 2 * ‖(raw n) ω‖ ^ 4 := by
    filter_upwards [hae] with ω hω
    have h := pow_le_pow_left₀ (abs_nonneg _) hω 2
    rw [sq_abs] at h
    calc linearityRemainder hS ν D Xs F n ω ^ 2 ≤ (C * ‖(raw n) ω‖ ^ 2) ^ 2 := h
      _ = C ^ 2 * ‖(raw n) ω‖ ^ 4 := by ring
  have hg : Integrable (fun ω ↦ C ^ 2 * ‖(raw n) ω‖ ^ 4) P :=
    (integrable_of_bdd_prob P (bdd_norm_sampleResponse_sub_pow hS D Xs hXm hB hn 4)).const_mul _
  have hf : Integrable (fun ω ↦ linearityRemainder hS ν D Xs F n ω ^ 2) P := by
    refine hg.mono'
      (((measurable_linearityRemainder hS ν hν D Xs hXm F hn).pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [hae2] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  calc ∫ ω, linearityRemainder hS ν D Xs F n ω ^ 2 ∂P ≤ ∫ ω, C ^ 2 * ‖(raw n) ω‖ ^ 4 ∂P :=
        integral_mono_ae hf hg hae2
    _ = C ^ 2 * ∫ ω, ‖(raw n) ω‖ ^ 4 ∂P := integral_const_mul _ _
    _ ≤ C ^ 2 * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4 / n ^ 2) :=
        mul_le_mul_of_nonneg_left
          (integral_norm_pow_four_sampleResponse_sub_le hS P D Xs hXm hid hlaw hind hB hn)
          (sq_nonneg C)

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν hind in
/-- The linear term is centred. -/
theorem integral_dotJ_tangentField_sampleResponse_sub (F : X → ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ ω, dotJ (tangentField hS ν F mD) ((raw n) ω) ∂P = 0 := by
  have hint : ∀ j, Integrable (fun ω ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) P := fun j ↦
    Integrable.of_bound ((measurable_pi_apply j).comp
      (measurable_sampleResponse_sub hS D Xs hXm)).aestronglyMeasurable (Fintype.card J * (2 * B))
      (ae_of_all _ fun ω ↦ (norm_le_pi_norm _ j).trans (norm_sampleResponse_sub_le D Xs hB hn ω))
  have hSint : ∀ j, Integrable (fun ω ↦ sampleResponse S Xs n ω j) P := fun j ↦ by
    have := (hint j).add (integrable_const (∫ x, S j x ∂D))
    exact this.congr (Eventually.of_forall fun ω ↦ by simp)
  unfold dotJ
  beta_reduce
  rw [integral_finsetSum _ fun j _ ↦ (hint j).const_mul _]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [integral_const_mul, integral_sub (hSint j) (integrable_const _),
    integral_sampleResponse hS P D Xs hXm hid hlaw hn j, integral_const, probReal_univ, one_smul,
    sub_self, mul_zero]

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν hid hlaw hind in
theorem integrable_dotJ_tangentField_sampleResponse_sub (F : X → ℝ) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ dotJ (tangentField hS ν F mD) ((raw n) ω)) P := by
  have hmeas : Measurable fun ω ↦ dotJ (tangentField hS ν F mD) ((raw n) ω) := by
    unfold dotJ
    exact Finset.measurable_sum _ fun j _ ↦ measurable_const.mul
      ((measurable_pi_apply j).comp (measurable_sampleResponse_sub hS D Xs hXm))
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    ((∑ j, |tangentField hS ν F mD j|) * (Fintype.card J * (2 * B))) (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs]
  exact (abs_dotJ_le _ _).trans (mul_le_mul_of_nonneg_left
    (norm_sampleResponse_sub_le D Xs hB hn ω) (Finset.sum_nonneg fun j _ ↦ abs_nonneg _))

omit hind in
theorem integrable_linearityRemainder {F : X → ℝ} {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    Integrable (linearityRemainder hS ν D Xs F n) P := by
  have hg : Integrable (fun ω ↦ C * ‖(raw n) ω‖ ^ 2) P :=
    (integrable_of_bdd_prob P (bdd_norm_sampleResponse_sub_pow hS D Xs hXm hB hn 2)).const_mul _
  refine hg.mono' (measurable_linearityRemainder hS ν hν D Xs hXm F hn).aestronglyMeasurable ?_
  filter_upwards [ae_abs_linearityRemainder_le hS ν hν P D Xs hXm hid hlaw hC hn] with ω hω
  rwa [Real.norm_eq_abs]

/-- **First-order unbiasedness**: the bias of the plug-in estimator is `O(1/n)`,
`|E_D Ψ̂_F − Ψ_F(D)| ≤ C |J|² (2B)² / n`. -/
theorem abs_integral_empiricalObs_sub_le {F : X → ℝ} (hF : Bdd F) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    |(∫ ω, empiricalObs hS ν Xs F n ω ∂P) - ∫ x, F x ∂responseProjection hS ν mD| ≤
      C * (Fintype.card J ^ 2 * (2 * B) ^ 2 / n) := by
  obtain ⟨K, hK⟩ := hF.2
  have hΨint : Integrable (fun ω ↦ empiricalObs hS ν Xs F n ω) P :=
    integrable_of_bdd_prob P ⟨measurable_empiricalObs hS ν hν Xs hXm F hn, K,
      abs_empiricalObs_le hS ν hν Xs hK hn⟩
  have hLint := integrable_dotJ_tangentField_sampleResponse_sub hS ν P D Xs hXm hB F hn
  have hRint := integrable_linearityRemainder hS ν hν P D Xs hXm hid hlaw hB hC hn
  have hg : Integrable (fun ω ↦ C * ‖(raw n) ω‖ ^ 2) P :=
    (integrable_of_bdd_prob P (bdd_norm_sampleResponse_sub_pow hS D Xs hXm hB hn 2)).const_mul _
  have hae := ae_abs_linearityRemainder_le hS ν hν P D Xs hXm hid hlaw hC hn
  have e : (fun ω ↦ empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) =
      fun ω ↦ dotJ (tangentField hS ν F mD) ((raw n) ω) + linearityRemainder hS ν D Xs F n ω := by
    funext ω
    unfold linearityRemainder
    ring
  have e2 : ∫ ω, (empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) ∂P =
      (∫ ω, empiricalObs hS ν Xs F n ω ∂P) - ∫ x, F x ∂responseProjection hS ν mD := by
    rw [integral_sub hΨint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [← e2, e, integral_add hLint hRint,
    integral_dotJ_tangentField_sampleResponse_sub hS ν P D Xs hXm hid hlaw hB F hn, zero_add]
  calc |∫ ω, linearityRemainder hS ν D Xs F n ω ∂P|
      ≤ ∫ ω, |linearityRemainder hS ν D Xs F n ω| ∂P := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        exact integral_congr_ae (Eventually.of_forall fun ω ↦ Real.norm_eq_abs _)
    _ ≤ ∫ ω, C * ‖(raw n) ω‖ ^ 2 ∂P := integral_mono_ae hRint.abs hg hae
    _ = C * ∫ ω, ‖(raw n) ω‖ ^ 2 ∂P := integral_const_mul _ _
    _ ≤ C * (Fintype.card J ^ 2 * (2 * B) ^ 2 / n) := by
        exact mul_le_mul_of_nonneg_left
          (integral_norm_sq_sampleResponse_sub_le hS P D Xs hXm hid hlaw hind hB hn) hC0

omit hind in
theorem integrable_sq_linearityRemainder {F : X → ℝ} {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ linearityRemainder hS ν D Xs F n ω ^ 2) P := by
  have hg : Integrable (fun ω ↦ C ^ 2 * ‖(raw n) ω‖ ^ 4) P :=
    (integrable_of_bdd_prob P (bdd_norm_sampleResponse_sub_pow hS D Xs hXm hB hn 4)).const_mul _
  refine hg.mono'
    (((measurable_linearityRemainder hS ν hν D Xs hXm F hn).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_abs_linearityRemainder_le hS ν hν P D Xs hXm hid hlaw hC hn] with ω hω
  have h := pow_le_pow_left₀ (abs_nonneg _) hω 2
  rw [sq_abs] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc linearityRemainder hS ν D Xs F n ω ^ 2 ≤ (C * ‖(raw n) ω‖ ^ 2) ^ 2 := h
    _ = C ^ 2 * ‖(raw n) ω‖ ^ 4 := by ring

/-- **The sharp risk of the plug-in estimator**: with `V = Var_D(ψ_F)` and
`C₄ = 3 C² |J|⁴ (2B)⁴`,
`|E_D (Ψ̂_F − Ψ_F(D))² − V/n| ≤ (V + 2 C₄) / n^{3/2}`. -/
theorem abs_integral_sq_empiricalObs_sub_sub_le {F : X → ℝ} (hF : Bdd F) {C : ℝ}
    (hC : ∀ N ∈ carriedResponses S (supportSet hS ν mD),
      |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
        dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2) {n : ℕ} (hn : 0 < n) :
    |(∫ ω, (empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) ^ 2 ∂P) -
        lawCov D (dirLoss S (tangentField hS ν F mD)) (dirLoss S (tangentField hS ν F mD)) / n| ≤
      (lawCov D (dirLoss S (tangentField hS ν F mD)) (dirLoss S (tangentField hS ν F mD)) +
        2 * (C ^ 2 * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4))) / (n * Real.sqrt n) := by
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = lawCov D (dirLoss S (tangentField hS ν F mD))
    (dirLoss S (tangentField hS ν F mD)) := ⟨_, rfl⟩
  obtain ⟨C4, hC4def⟩ : ∃ C4 : ℝ, C4 = C ^ 2 * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Ω → ℝ, L = fun ω ↦ dotJ (tangentField hS ν F mD) ((raw n) ω) :=
    ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Ω → ℝ, R = linearityRemainder hS ν D Xs F n := ⟨_, rfl⟩
  rw [← hVdef, ← hC4def]
  have hC4 : 0 ≤ C4 := by rw [hC4def]; positivity
  -- the integrals of the two pieces
  have hLint : Integrable L P := by
    rw [hLdef]
    exact integrable_dotJ_tangentField_sampleResponse_sub hS ν P D Xs hXm hB F hn
  have hL2int : Integrable (fun ω ↦ L ω ^ 2) P := by
    rw [hLdef]
    have hb : Bdd fun ω ↦ dotJ (tangentField hS ν F mD) ((raw n) ω) := by
      refine ⟨?_, (∑ j, |tangentField hS ν F mD j|) * (Fintype.card J * (2 * B)), fun ω ↦ ?_⟩
      · unfold dotJ
        exact Finset.measurable_sum _ fun j _ ↦ measurable_const.mul
          ((measurable_pi_apply j).comp (measurable_sampleResponse_sub hS D Xs hXm))
      · exact (abs_dotJ_le _ _).trans (mul_le_mul_of_nonneg_left
          (norm_sampleResponse_sub_le D Xs hB hn ω) (Finset.sum_nonneg fun j _ ↦ abs_nonneg _))
    exact (integrable_of_bdd_prob P (hb.mul hb)).congr
      (Eventually.of_forall fun ω ↦ by simp [sq])
  have hR2int : Integrable (fun ω ↦ R ω ^ 2) P := by
    rw [hRdef]
    exact integrable_sq_linearityRemainder hS ν hν P D Xs hXm hid hlaw hB hC hn
  have hL2 : ∫ ω, L ω ^ 2 ∂P = V / n := by
    rw [hLdef, hVdef]
    have := integral_dotJ_sampleResponse_sub_mul hS P D Xs hXm hid hlaw
      (fun i k h ↦ hind.indepFun h) hn (tangentField hS ν F mD) (tangentField hS ν F mD)
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun ω ↦ by simp [sq])
  have hR2 : ∫ ω, R ω ^ 2 ∂P ≤ C4 / n ^ 2 := by
    rw [hRdef, hC4def, mul_div_assoc]
    exact integral_sq_linearityRemainder_le hS ν hν P D Xs hXm hid hlaw hind hB hC hn
  have hR2nn : 0 ≤ ∫ ω, R ω ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg _
  have hV0 : 0 ≤ V := by
    have h : 0 ≤ ∫ ω, L ω ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg (L ω)
    rw [hL2] at h
    have := mul_nonneg h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rwa [div_mul_cancel₀ _ (by positivity : (n : ℝ) ≠ 0)] at this
  -- the estimator error is the sum of the two pieces
  have e : (fun ω ↦ (empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) ^ 2) =
      fun ω ↦ (L ω + R ω) ^ 2 := by
    funext ω
    rw [hLdef, hRdef]
    unfold linearityRemainder
    ring
  rw [e]
  obtain ⟨K, hK⟩ := hF.2
  have hsum_int : Integrable (fun ω ↦ (L ω + R ω) ^ 2) P := by
    rw [← e]
    have hb : Bdd fun ω ↦ empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD :=
      ⟨(measurable_empiricalObs hS ν hν Xs hXm F hn).sub measurable_const, K + K, fun ω ↦
        (abs_sub _ _).trans (add_le_add (abs_empiricalObs_le hS ν hν Xs hK hn ω)
          (by
            rw [integral_responseProjection_eq_sum hS ν hν (dataLawMean_mem_polytope hS ν hν D) F]
            exact abs_sum_mul_le_of_stdSimplex
              (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν (dataLawMean_mem_polytope hS ν hν D))
              hK))⟩
    exact (integrable_of_bdd_prob P (hb.mul hb)).congr (Eventually.of_forall fun ω ↦ by simp [sq])
  -- the square root of `n`
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt n := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hnpos
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    exact (Real.le_sqrt zero_le_one hnpos.le).2
      (by simpa using (Nat.one_le_cast.2 hn : (1 : ℝ) ≤ n))
  have hsn : s * s = n := by rw [hsdef]; exact Real.mul_self_sqrt hnpos.le
  rw [← hsdef]
  -- the two-sided pointwise bound `(L + R)² ≶ (1 ± 1/s) L² ± (1 + s) R²`
  have hup : ∀ ω, (L ω + R ω) ^ 2 ≤ (1 + 1 / s) * L ω ^ 2 + (1 + s) * R ω ^ 2 := by
    intro ω
    have h2 : 2 * (L ω * R ω) ≤ 1 / s * L ω ^ 2 + s * R ω ^ 2 := by
      have hsq := sq_nonneg (L ω - s * R ω)
      rw [one_div, inv_mul_eq_div, div_add' _ _ _ hs0.ne', le_div_iff₀ hs0]
      nlinarith
    nlinarith
  have hlo : ∀ ω, (1 - 1 / s) * L ω ^ 2 - s * R ω ^ 2 ≤ (L ω + R ω) ^ 2 := by
    intro ω
    have h2 : -(2 * (L ω * R ω)) ≤ 1 / s * L ω ^ 2 + s * R ω ^ 2 := by
      have hsq := sq_nonneg (L ω + s * R ω)
      rw [one_div, inv_mul_eq_div, div_add' _ _ _ hs0.ne', le_div_iff₀ hs0]
      nlinarith
    nlinarith
  have hup_int : Integrable (fun ω ↦ (1 + 1 / s) * L ω ^ 2 + (1 + s) * R ω ^ 2) P :=
    (hL2int.const_mul _).add (hR2int.const_mul _)
  have hlo_int : Integrable (fun ω ↦ (1 - 1 / s) * L ω ^ 2 - s * R ω ^ 2) P :=
    (hL2int.const_mul _).sub (hR2int.const_mul _)
  have Iup := integral_mono_ae hsum_int hup_int (ae_of_all _ hup)
  have Ilo := integral_mono_ae hlo_int hsum_int (ae_of_all _ hlo)
  rw [integral_add (hL2int.const_mul _) (hR2int.const_mul _), integral_const_mul,
    integral_const_mul, hL2] at Iup
  rw [integral_sub (hL2int.const_mul _) (hR2int.const_mul _), integral_const_mul,
    integral_const_mul, hL2] at Ilo
  -- arithmetic in `s`
  rw [← hsn] at Iup Ilo hR2 ⊢
  have hkey1 : (1 + 1 / s) * (V / (s * s)) - V / (s * s) = V / (s * s * s) := by
    field_simp
    ring
  have hkey2 : (1 + s) * (C4 / (s * s) ^ 2) ≤ 2 * C4 / (s * s * s) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hC4 (mul_nonneg hs0.le hs0.le), mul_nonneg hC4 hs0.le,
      mul_nonneg (mul_nonneg hC4 hs0.le) (mul_nonneg hs0.le (mul_nonneg hs0.le (sub_nonneg.2 hs1)))]
  have hkey3 : s * (C4 / (s * s) ^ 2) = C4 / (s * s * s) := by
    field_simp
  rw [abs_le]
  constructor
  · -- lower bound
    have h1 : s * ∫ ω, R ω ^ 2 ∂P ≤ C4 / (s * s * s) :=
      hkey3 ▸ mul_le_mul_of_nonneg_left hR2 hs0.le
    have h2 : (1 - 1 / s) * (V / (s * s)) - V / (s * s) = -(V / (s * s * s)) := by
      field_simp
      ring
    have h3 : 0 ≤ C4 / (s * s * s) := by positivity
    rw [add_div]
    nlinarith
  · -- upper bound
    have h1 : (1 + s) * ∫ ω, R ω ^ 2 ∂P ≤ 2 * C4 / (s * s * s) :=
      (mul_le_mul_of_nonneg_left hR2 (by positivity)).trans hkey2
    rw [add_div]
    nlinarith

end Sampling

end Laplace.Multi
