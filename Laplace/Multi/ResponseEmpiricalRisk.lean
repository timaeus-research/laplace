/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseGlobalLipschitz
import Laplace.Multi.ResponseFacewiseRegression
import Laplace.Multi.SamplingResolution
import Laplace.Multi.EmpiricalMoments
import Laplace.Multi.ReconstructionBias

/-!
# The uniform, unlocalised risk of the empirical posterior expectation

On a finite configuration the natural estimator of a posterior expectation from `n` i.i.d. samples
is the plug-in `Ψ̂_F = E_{R_{M̂_n}} F`, the posterior expectation at the empirical mean — defined
for every sample, boundary empirical means included, because the empirical mean always lies in the
closed polytope (`sampleResponse_mem_convexHull`) and the response of every observable is Lipschitz
there (`ResponseGlobalLipschitz`). Its risk is controlled uniformly over all data laws on the
configuration, without localisation and without any chart:

`E_D (Ψ̂_F − Ψ_F(D))² ≤ L_F² tr Cov_D(S) / n`,   `E_D |Ψ̂_F − Ψ_F(D)| ≤ L_F √(tr Cov_D(S) / n)`

(`integral_sq_empiricalObs_sub_le`, `integral_abs_empiricalObs_sub_le`), with `tr Cov_D(S) =
Σ_j Var_D(S_j)` the exact second moment of the empirical displacement
(`integral_sum_sq_sampleResponse_sub`). The same second moment gives the **margin chamber theorem**
(`measureReal_sampleResponse_notMem_le`): if the chamber assigned to `D` contains the Euclidean
`r`-ball about `m_D`, the probability of assigning the wrong chamber from `n` samples is at most
`tr Cov_D(S) / (n r²)`. It is the distance of the mean to the chamber boundary, not the chamber's
width, that controls the resolution.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Risk

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  (ν : Measure X) [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x}) [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X) [IsProbabilityMeasure D]
  (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
include hS hν hXm hid hlaw hind

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J]
  [Nonempty J] hS hν [IsProbabilityMeasure ν] [MeasurableSpace Ω] [IsProbabilityMeasure P]
  [IsProbabilityMeasure D] hXm hid hlaw hind in
/-- The empirical mean is a convex combination of feature vectors, hence lies in the polytope. -/
theorem sampleResponse_mem_convexHull {n : ℕ} (hn : 0 < n) (ω : Ω) :
    sampleResponse S Xs n ω ∈ hull := by
  have e : sampleResponse S Xs n ω =
      ∑ i ∈ Finset.range n, (1 / (n : ℝ)) • statPoint S (Xs i ω) := by
    funext j
    simp only [sampleResponse, Finset.sum_apply, Pi.smul_apply, statPoint, smul_eq_mul,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ ↦ by positivity) ?_
    fun i _ ↦ subset_convexHull ℝ _ (mem_range_self _)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

variable (S) in
/-- **The trace of the data covariance of the features**: `tr Cov_D(S) = Σ_j Var_D(S_j)`. -/
noncomputable def traceCov : ℝ := ∑ j, lawCov D (S j) (S j)

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hν
  [IsProbabilityMeasure ν] in
/-- **The exact second moment of the empirical displacement**:
`E_D Σ_j (M̂_j − m_j)² = tr Cov_D(S) / n`. -/
theorem integral_sum_sq_sampleResponse_sub {n : ℕ} (hn : 0 < n) :
    ∫ ω, ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 ∂P = traceCov S D / n := by
  classical
  have hint : ∀ j, Integrable (fun ω ↦ (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2) P :=
    fun j ↦ by
      have := integrable_sampleResponse_sub_mul hS P D Xs hXm hn j j
      simpa only [sq] using this
  rw [integral_finsetSum _ fun j _ ↦ hint j, traceCov, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h := integral_sq_dotJ_sampleResponse_sub hS P D Xs hXm hid hlaw hind hn (Pi.single j 1)
  have e1 : ∀ ω, dotJ (Pi.single j 1 : J → ℝ)
      (fun i ↦ sampleResponse S Xs n ω i - ∫ x, S i x ∂D) =
      sampleResponse S Xs n ω j - ∫ x, S j x ∂D := fun ω ↦ by
    simp [dotJ, Pi.single_apply]
  have e2 : dirLoss S (Pi.single j 1 : J → ℝ) = S j := by
    funext x
    simp [dirLoss, Pi.single_apply]
  simp only [e1, e2] at h
  exact h

/-- **The plug-in estimator of a posterior expectation**: `Ψ̂_F = E_{R_{M̂_n}} F`, the posterior
expectation at the empirical mean. -/
noncomputable def empiricalObs (F : X → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ x, F x ∂responseProjection hS ν (sampleResponse S Xs n ω)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] hXm hid hlaw hind in
/-- The plug-in estimator is Lipschitz in the empirical mean. -/
theorem abs_empiricalObs_sub_le {F : X → ℝ} (hF : Bdd F) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S, ∑ j, |(regressionDir hS ν F θ : J → ℝ) j| ≤ L)
    {n : ℕ} (hn : 0 < n) (ω : Ω) :
    |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| ≤
      L * ‖sampleResponse S Xs n ω - mD‖ :=
  abs_responseObs_sub_le hS ν hν hF hL0 hL (dataLawMean_mem_polytope hS ν hν D)
    (sampleResponse_mem_convexHull Xs hn ω)

/-- **THE UNIFORM SECOND-MOMENT RISK BOUND**:
`E_D (Ψ̂_F − Ψ_F(D))² ≤ L_F² tr Cov_D(S) / n`. -/
theorem integral_sq_empiricalObs_sub_le {F : X → ℝ} (hF : Bdd F) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S, ∑ j, |(regressionDir hS ν F θ : J → ℝ) j| ≤ L)
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, (empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) ^ 2 ∂P ≤
      L ^ 2 * (traceCov S D / n) := by
  have hint : ∀ j, Integrable (fun ω ↦ (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2) P :=
    fun j ↦ by
      have := integrable_sampleResponse_sub_mul hS P D Xs hXm hn j j
      simpa only [sq] using this
  have hg : Integrable (fun ω ↦ L ^ 2 * ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2) P :=
    (integrable_finsetSum _ fun j _ ↦ hint j).const_mul _
  calc ∫ ω, (empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) ^ 2 ∂P
      ≤ ∫ ω, L ^ 2 * ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _) hg
          (ae_of_all _ fun ω ↦ ?_)
        have h1 := abs_empiricalObs_sub_le hS ν hν D Xs hF hL0 hL hn ω
        have h2 := norm_sq_le_sum_sq (sampleResponse S Xs n ω - mD)
        simp only [Pi.sub_apply] at h2
        calc (empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) ^ 2
            = |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| ^ 2 := by
              rw [sq_abs]
          _ ≤ (L * ‖sampleResponse S Xs n ω - mD‖) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = L ^ 2 * ‖sampleResponse S Xs n ω - mD‖ ^ 2 := by ring
          _ ≤ L ^ 2 * ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2 :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = L ^ 2 * (traceCov S D / n) := by
        rw [integral_const_mul, integral_sum_sq_sampleResponse_sub hS P D Xs hXm hid hlaw hind hn]

omit hid hlaw hind [IsProbabilityMeasure P] [IsProbabilityMeasure D] in
/-- The plug-in estimator is a measurable function of the sample. -/
theorem measurable_empiricalObs (F : X → ℝ) {n : ℕ} (hn : 0 < n) :
    Measurable (empiricalObs hS ν Xs F n) := by
  have hcont : Continuous (Set.domRestrict hull (qStarVec hS ν)) :=
    continuousOn_iff_continuous_domRestrict.1 (continuousOn_qStarVec hS ν hν)
  have hm : Measurable fun ω ↦ (⟨sampleResponse S Xs n ω,
      sampleResponse_mem_convexHull Xs hn ω⟩ : hull) :=
    (measurable_sampleResponse hS Xs hXm n).subtype_mk
  have e : empiricalObs hS ν Xs F n = fun ω ↦ ∑ x, (Set.domRestrict hull (qStarVec hS ν)
      ⟨sampleResponse S Xs n ω, sampleResponse_mem_convexHull Xs hn ω⟩) x * F x := by
    funext ω
    exact integral_responseProjection_eq_sum hS ν hν (sampleResponse_mem_convexHull Xs hn ω) F
  rw [e]
  exact Finset.measurable_sum _ fun x _ ↦
    ((measurable_pi_apply x).comp (hcont.measurable.comp hm)).mul_const _

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [IsProbabilityMeasure D] hXm hid hlaw hind in
/-- The plug-in estimator is bounded by the bound of the observable. -/
theorem abs_empiricalObs_le {F : X → ℝ} {K : ℝ} (hK : ∀ x, |F x| ≤ K) {n : ℕ} (hn : 0 < n)
    (ω : Ω) : |empiricalObs hS ν Xs F n ω| ≤ K := by
  unfold empiricalObs
  rw [integral_responseProjection_eq_sum hS ν hν (sampleResponse_mem_convexHull Xs hn ω) F]
  exact abs_sum_mul_le_of_stdSimplex
    (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν (sampleResponse_mem_convexHull Xs hn ω)) hK

/-- **THE UNIFORM RISK BOUND**: `E_D |Ψ̂_F − Ψ_F(D)| ≤ L_F √(tr Cov_D(S) / n)`, uniformly over all
data laws on the configuration and with no localisation. -/
theorem integral_abs_empiricalObs_sub_le {F : X → ℝ} (hF : Bdd F) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S, ∑ j, |(regressionDir hS ν F θ : J → ℝ) j| ≤ L)
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| ∂P ≤
      L * √(traceCov S D / n) := by
  obtain ⟨-, K, hK⟩ := id hF
  -- the centred estimator is bounded and measurable
  have hb : Bdd fun ω ↦ |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| := by
    refine ⟨((measurable_empiricalObs hS ν hν Xs hXm F hn).sub measurable_const).abs, 2 * K,
      fun ω ↦ ?_⟩
    rw [abs_abs]
    have h1 := abs_empiricalObs_le hS ν hν Xs hK hn ω
    have h2 : |∫ x, F x ∂responseProjection hS ν mD| ≤ K := by
      rw [integral_responseProjection_eq_sum hS ν hν (dataLawMean_mem_polytope hS ν hν D) F]
      exact abs_sum_mul_le_of_stdSimplex
        (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν (dataLawMean_mem_polytope hS ν hν D)) hK
    calc _ ≤ |empiricalObs hS ν Xs F n ω| + |∫ x, F x ∂responseProjection hS ν mD| := abs_sub _ _
      _ ≤ K + K := add_le_add h1 h2
      _ = 2 * K := by ring
  -- `(E|Z|)² ≤ E Z²` is the nonnegativity of the variance of `|Z|`
  have hvar := lawCov_self_nonneg P hb
  unfold lawCov at hvar
  have hsq : ∫ ω, |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| *
      |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| ∂P =
      ∫ ω, (empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD) ^ 2 ∂P := by
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    beta_reduce
    rw [← sq, sq_abs]
  rw [hsq] at hvar
  have hrisk := integral_sq_empiricalObs_sub_le hS ν hν P D Xs hXm hid hlaw hind hF hL0 hL hn
  have hnn : 0 ≤ ∫ ω, |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| ∂P :=
    integral_nonneg fun ω ↦ abs_nonneg _
  calc ∫ ω, |empiricalObs hS ν Xs F n ω - ∫ x, F x ∂responseProjection hS ν mD| ∂P
      ≤ √(L ^ 2 * (traceCov S D / n)) := by
        refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
        nlinarith
    _ = L * √(traceCov S D / n) := by
        rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL0]

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hν
  [IsProbabilityMeasure ν] in
/-- **Chebyshev for the empirical mean**: `P_D(‖M̂_n − m_D‖ ≥ r) ≤ tr Cov_D(S) / (n r²)`. -/
theorem measureReal_norm_sampleResponse_sub_ge_le {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    P.real {ω | r ≤ ‖sampleResponse S Xs n ω - mD‖} ≤ traceCov S D / n / r ^ 2 := by
  have hint : ∀ j, Integrable (fun ω ↦ (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2) P :=
    fun j ↦ by
      have := integrable_sampleResponse_sub_mul hS P D Xs hXm hn j j
      simpa only [sq] using this
  have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω ↦ ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2)
    (ae_of_all _ fun ω ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
    (integrable_finsetSum _ fun j _ ↦ hint j) (r ^ 2)
  rw [integral_sum_sq_sampleResponse_sub hS P D Xs hXm hid hlaw hind hn] at hcheb
  have hsub : {ω | r ≤ ‖sampleResponse S Xs n ω - mD‖} ⊆
      {ω | r ^ 2 ≤ ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2} := by
    intro ω hω
    have h2 := norm_sq_le_sum_sq (sampleResponse S Xs n ω - mD)
    simp only [Pi.sub_apply] at h2
    exact (pow_le_pow_left₀ hr.le hω 2).trans h2
  rw [le_div_iff₀ (by positivity)]
  calc P.real {ω | r ≤ ‖sampleResponse S Xs n ω - mD‖} * r ^ 2
      ≤ P.real {ω | r ^ 2 ≤ ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2} * r ^ 2 :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) (by positivity)
    _ = r ^ 2 * P.real {ω | r ^ 2 ≤ ∑ j, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ^ 2} := by
        ring
    _ ≤ traceCov S D / n := hcheb

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hν
  [IsProbabilityMeasure ν] in
/-- **THE MARGIN CHAMBER THEOREM**: if the chamber `C` assigned to the data law contains the
Euclidean `r`-ball about `m_D`, then the probability of assigning the empirical mean to another
chamber is at most `tr Cov_D(S) / (n r²)`. The margin `r`, the distance from `m_D` to the boundary
of its chamber, controls the resolution, not the width of the chamber. -/
theorem measureReal_sampleResponse_notMem_chamber_le {C : Set (J → ℝ)} {r : ℝ} (hr : 0 < r)
    (hball : ∀ M', ‖M' - mD‖ < r → M' ∈ C) {n : ℕ} (hn : 0 < n) :
    P.real {ω | sampleResponse S Xs n ω ∉ C} ≤ traceCov S D / n / r ^ 2 := by
  refine le_trans (measureReal_mono ?_)
    (measureReal_norm_sampleResponse_sub_ge_le hS P D Xs hXm hid hlaw hind hn hr)
  intro ω hω
  by_contra hlt
  exact hω (hball _ (not_le.1 hlt))

end Risk

end Laplace.Multi
