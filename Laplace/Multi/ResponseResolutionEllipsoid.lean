/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseMinimaxTwoPoint

/-!
# The observable resolution ellipsoid

For finitely many bounded observables `F_1, …, F_r` the matrix `V_{ii'} = Σ_D(u_{F_i}, u_{F_{i'}})`
of data covariances of their regression directions (`resolutionMat`) is the leading joint sampling
covariance of the empirical posterior expectations (`ResponseObservableJointCovariance`). It is also
the exact **resolution ellipsoid**: the regression direction is linear in the observable
(`regressionDir_add`, `regressionDir_const_mul`, `regressionDir_sum`), so every scalar contrast
`F_c = Σ_i c_i F_i` has regression direction `Σ_i c_i u_{F_i}` and influence variance
`σ²_{F_c} = cᵀ V c` (`dataBilin_regressionDir_sum`), and the two-point minimax obstruction of
`ResponseMinimaxTwoPoint` applies to every contrast with `cᵀ V c > 0` at the scale
`√(cᵀ V c / n)` (`minimax_two_point_contrast`). Thus `V/n` is not merely an asymptotic covariance:
its ellipsoid `{c : cᵀ V c ≤ 1}` describes exactly which combinations of posterior expectations
`n` samples can resolve, matched above (sampling covariance) and below (Le Cam) by the same
quadratic form, including the singular contrasts, which are those in the kernel of `V`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Linear

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The regression direction. -/
local notation "uF" => regressionDir hS ν

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- A finite linear combination of bounded observables is bounded. -/
theorem bdd_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ) {F : ι → X → ℝ}
    (hF : ∀ i, Bdd (F i)) : Bdd fun x ↦ ∑ i ∈ s, c i * F i x := by
  choose hm M hM using hF
  refine ⟨Finset.measurable_sum _ fun i _ ↦ (hm i).const_mul _, ∑ i ∈ s, |c i| * M i,
    fun x ↦ ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM i x) (abs_nonneg _)

omit [Nonempty J] in
/-- The covariance functional is additive in the observable. -/
theorem covFunctional_add {F H : X → ℝ} (hF : Bdd F) (hH : Bdd H) (θ : 𝕍) :
    covFunctional ν (fun x ↦ F x + H x) θ = covFunctional ν F θ + covFunctional ν H θ := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  ext v
  rw [LinearMap.add_apply, covFunctional_apply hS ν (hF.add hH), covFunctional_apply hS ν hF,
    covFunctional_apply hS ν hH]
  exact lawCov_add_left_eq _ hF hH (bdd_dirLoss hS _)

omit [Nonempty J] in
/-- The covariance functional is homogeneous in the observable. -/
theorem covFunctional_const_mul (c : ℝ) {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) :
    covFunctional ν (fun x ↦ c * F x) θ = c • covFunctional ν F θ := by
  ext v
  rw [LinearMap.smul_apply, covFunctional_apply hS ν (hF.const_mul c), covFunctional_apply hS ν hF,
    smul_eq_mul, lawCov_const_mul_left_eq]

omit [Nonempty J] in
/-- The covariance functional of the zero observable vanishes. -/
theorem covFunctional_zero (θ : 𝕍) : covFunctional ν (fun _ ↦ (0 : ℝ)) θ = 0 := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  ext v
  rw [covFunctional_apply hS ν (Bdd.const 0), LinearMap.zero_apply, lawCov_const_left_eq_zero]

/-- **The regression direction is additive in the observable.** -/
theorem regressionDir_add {F H : X → ℝ} (hF : Bdd F) (hH : Bdd H) (θ : 𝕍) :
    uF (fun x ↦ F x + H x) θ = uF F θ + uF H θ := by
  unfold regressionDir
  rw [covFunctional_add hS ν hF hH, map_add]

/-- **The regression direction is homogeneous in the observable.** -/
theorem regressionDir_const_mul (c : ℝ) {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) :
    uF (fun x ↦ c * F x) θ = c • uF F θ := by
  unfold regressionDir
  rw [covFunctional_const_mul hS ν c hF, map_smul]

theorem regressionDir_zero (θ : 𝕍) : uF (fun _ ↦ (0 : ℝ)) θ = 0 := by
  unfold regressionDir
  rw [covFunctional_zero hS ν, map_zero]

/-- **Linearity of the regression direction**: `u_{Σ c_i F_i} = Σ c_i u_{F_i}`. -/
theorem regressionDir_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) {F : ι → X → ℝ}
    (hF : ∀ i, Bdd (F i)) (θ : 𝕍) :
    uF (fun x ↦ ∑ i ∈ s, c i * F i x) θ = ∑ i ∈ s, c i • uF (F i) θ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact regressionDir_zero hS ν θ
  | insert a s ha ih =>
    have e : (fun x ↦ ∑ i ∈ insert a s, c i * F i x) =
        fun x ↦ c a * F a x + ∑ i ∈ s, c i * F i x := by
      funext x
      rw [Finset.sum_insert ha]
    rw [e, regressionDir_add hS ν ((hF a).const_mul _) (bdd_sum_mul s c hF),
      regressionDir_const_mul hS ν _ (hF a), ih, Finset.sum_insert ha]

end Linear

section Ellipsoid

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

/-- The regression direction of `F` at the response of `D`. -/
local notation "uF" F => regressionDir hS ν F (θr mD)

/-- **The resolution matrix** `V_{ii'} = Σ_D(u_{F_i}, u_{F_{i'}})` of finitely many observables. -/
noncomputable def resolutionMat {ι : Type*} (F : ι → X → ℝ) (i i' : ι) : ℝ :=
  dataBilin hS ν D (uF (F i)) (uF (F i'))

/-- **The influence variance of a contrast is its resolution form**:
`σ²_{F_c} = Σ_D(u_{F_c}, u_{F_c}) = cᵀ V c`. -/
theorem dataBilin_regressionDir_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) {F : ι → X → ℝ}
    (hF : ∀ i, Bdd (F i)) :
    dataBilin hS ν D (uF fun x ↦ ∑ i, c i * F i x) (uF fun x ↦ ∑ i, c i * F i x) =
      ∑ i, ∑ i', c i * c i' * resolutionMat hS ν D F i i' := by
  rw [regressionDir_sum hS ν Finset.univ c hF]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    resolutionMat]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ ↦ ?_
  rw [dataBilin_comm hS ν D (regressionDir hS ν (F i') _) (regressionDir hS ν (F i) _)]
  ring

variable (hDν : D ≪ ν) (hνD : ν ≪ D)
include hDν hνD

/-- **THE RESOLUTION ELLIPSOID**: every scalar contrast `F_c = Σ_i c_i F_i` of finitely many
posterior expectations with `cᵀ V c > 0` carries the two-point minimax obstruction at the scale
`√(cᵀ V c / n)`: along the alternatives tilted by the influence function of `F_c` at scale
`a/√n`, `√n L_n → (a cᵀVc/2)(1 − √(a² cᵀVc/2))` and every integrable estimator has two-point risk
at least `L_n` for `n` large. -/
theorem minimax_two_point_contrast {ι : Type*} [Fintype ι] {F : ι → X → ℝ} (hF : ∀ i, Bdd (F i))
    (c : ι → ℝ) (hpos : 0 < ∑ i, ∑ i', c i * c i' * resolutionMat hS ν D F i i') {a : ℝ}
    (ha : 0 < a) :
    ∃ L : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ Real.sqrt n * L n) atTop
        (𝓝 (a * (∑ i, ∑ i', c i * c i' * resolutionMat hS ν D F i i') / 2 *
          (1 - √(a ^ 2 * (∑ i, ∑ i', c i * c i' * resolutionMat hS ν D F i i') / 2)))) ∧
      ∀ᶠ n : ℕ in atTop, ∀ T : (Fin n → X) → ℝ, Measurable T →
        Integrable T (Measure.pi fun _ : Fin n ↦ D) →
        Integrable T (Measure.pi fun _ : Fin n ↦
          D.tilted fun x ↦ (a / Real.sqrt n) * dataInfluence hS ν D (fun x ↦ ∑ i, c i * F i x) x) →
        L n ≤ max (∫ z, |T z - dataObs hS ν (fun x ↦ ∑ i, c i * F i x) D|
            ∂(Measure.pi fun _ : Fin n ↦ D))
          (∫ z, |T z - dataObs hS ν (fun x ↦ ∑ i, c i * F i x) (D.tilted fun x ↦ (a / Real.sqrt n) *
            dataInfluence hS ν D (fun x ↦ ∑ i, c i * F i x) x)| ∂(Measure.pi fun _ : Fin n ↦
              D.tilted fun x ↦ (a / Real.sqrt n) *
                dataInfluence hS ν D (fun x ↦ ∑ i, c i * F i x) x)) := by
  have hbdd : Bdd fun x ↦ ∑ i, c i * F i x := bdd_sum_mul Finset.univ c hF
  have h := minimax_two_point_tilted hS ν D hDν hνD hbdd
    (by rwa [dataBilin_regressionDir_sum hS ν D c hF]) ha
  rwa [dataBilin_regressionDir_sum hS ν D c hF] at h

end Ellipsoid

end Laplace.Multi
