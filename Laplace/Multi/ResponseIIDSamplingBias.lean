/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseLocalizedSamplingBias
import Laplace.Multi.IIDFourthMoment
import Laplace.Multi.ResponseObservableHessian

/-!
# The i.i.d. sampling bias of the localised response

The law-level localised bias theorem of `ResponseLocalizedSamplingBias` is instantiated for the
empirical displacement `ξ_n = p(M̂_n − m_D)` of `n` i.i.d. samples from a data law `D ≪ ν` with
features bounded by `B`, projected into the direction space by any retraction `p` (which is the
identity on `W`, so `ξ_n` is the intrinsic displacement almost surely).

* **`integral_curvatureForm_sampleResponse`** — the covariance contraction: the expected curvature
  form of the empirical displacement is the m-connection contracted with the data covariance,
  `E[C(A⁻¹ξ_n, A⁻¹ξ_n)] = (1/n) ∑_{a,b} Cov_D(S_a,S_b) C(A⁻¹p e_a, A⁻¹p e_b)`
  (`curvBilin`, `covContraction`); pairwise independence suffices.
* `integral_norm_pow_three_proj_le` — the third absolute moment of `ξ_n` is
  `≤ √3 |J|³ (2B)³ / n^{3/2}` (mutual independence, from `IIDFourthMoment`).
* **`iid_localizedBias_curvature`** — the headline: for the reset-localised response
  `θ̂_loc = θ₀ + 1_{‖ξ_n‖≤δ}(θr(m₀ + ξ_n) − θ₀)`,

  `‖ E[θ̂_loc − θ₀] + (1/(2n)) ∑_{a,b} Cov_D(S_a,S_b) C(A⁻¹p e_a, A⁻¹p e_b) ‖
      ≤ (‖A⁻¹‖/δ² + K + ½‖A⁻¹‖‖T‖‖A⁻¹‖²/δ) · √3 |J|³ (2B)³ / n^{3/2}`.

  The leading bias of the localised response is exactly `−(1/2n)` times the m-connection
  contracted with the sampling covariance, and the remainder is one order smaller.
* `setIntegral_map_sampleResponse` — the left-hand side is the expectation of the reset-localised
  estimator (the set integral on the law is the integral over the good event).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section IID

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : iIndepFun Xs P)
include hS hXm hid hlaw hDν hind

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain (the sample space is `Ω`). -/
local notation "Ωm" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The raw empirical displacement `M̂_n − m_D`. -/
local notation "raw" n => (fun ω : Ω ↦ fun j : J ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)

omit [DecidableEq J] [IsProbabilityMeasure P] [IsProbabilityMeasure D] hDν hXm hid hlaw hind in
/-- **The curvature bilinear form** `(u, v) ↦ C_{θ₀}(A⁻¹u, A⁻¹v)`. -/
noncomputable def curvBilin (θ₀ : 𝕍) : 𝕍 →ₗ[ℝ] 𝕍 →ₗ[ℝ] 𝕍 :=
  LinearMap.mk₂ ℝ (fun u v ↦ mChristoffel hS ν θ₀ ((CDE θ₀).symm u) ((CDE θ₀).symm v))
    (fun u u' v ↦ by rw [map_add, mChristoffel_add_left hS ν])
    (fun c u v ↦ by rw [map_smul, mChristoffel_smul_left hS ν])
    (fun u v v' ↦ by rw [map_add, mChristoffel_add_right hS ν])
    (fun c u v ↦ by rw [map_smul, mChristoffel_smul_right hS ν])

omit [DecidableEq J] [IsProbabilityMeasure P] [IsProbabilityMeasure D] hDν hXm hid hlaw hind in
theorem curvatureForm_eq_curvBilin (θ₀ z : 𝕍) :
    curvatureForm hS ν θ₀ z = curvBilin hS ν θ₀ z z := rfl

omit [IsProbabilityMeasure P] [IsProbabilityMeasure D] hDν hXm hid hlaw hind in
/-- The curvature form of a projected vector expands over the coordinate basis. -/
theorem curvatureForm_proj_eq_sum (p : (J → ℝ) →ₗ[ℝ] 𝕍) (θ₀ : 𝕍) (y : J → ℝ) :
    curvatureForm hS ν θ₀ (p y) = ∑ a, ∑ b, (y a * y b) •
      curvBilin hS ν θ₀ (p (Pi.single a 1)) (p (Pi.single b 1)) := by
  rw [curvatureForm_eq_curvBilin]
  conv_lhs => rw [pi_eq_sum_univ' y, map_sum]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by rw [mul_comm]

omit [IsProbabilityMeasure P] hDν hXm hid hlaw hind in
/-- **The m-connection contracted with the data covariance**:
`∑_{a,b} Cov_D(S_a,S_b) C_{θ₀}(A⁻¹ p e_a, A⁻¹ p e_b)`. -/
noncomputable def covContraction (p : (J → ℝ) →ₗ[ℝ] 𝕍) (θ₀ : 𝕍) : 𝕍 :=
  ∑ a, ∑ b, (∫ x, (S a x - ∫ y, S a y ∂D) * (S b x - ∫ y, S b y ∂D) ∂D) •
    curvBilin hS ν θ₀ (p (Pi.single a 1)) (p (Pi.single b 1))

variable {n : ℕ} (hn : 0 < n)
include hn

omit hDν hind in
/-- **The covariance contraction**: the expected curvature form of the projected empirical
displacement is `(1/n)` times the m-connection contracted with the data covariance. -/
theorem integral_curvatureForm_sampleResponse (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hind' : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P) (θ₀ : 𝕍) :
    ∫ ω, curvatureForm hS ν θ₀ (p ((raw n) ω)) ∂P = (1 / n : ℝ) • covContraction hS ν D p θ₀ := by
  simp_rw [curvatureForm_proj_eq_sum hS ν p θ₀]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦
    (integrable_sampleResponse_sub_mul hS P D Xs hXm hn a b).smul_const _]
  simp_rw [integral_finsetSum _ fun b _ ↦
    (integrable_sampleResponse_sub_mul hS P D Xs hXm hn _ b).smul_const _, integral_smul_const,
    integral_sampleResponse_sub_mul_sub hS P D Xs hXm hid hlaw hind' hn]
  unfold covContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [smul_smul, div_eq_mul_one_div, mul_comm]

omit [DecidableEq J] [IsProbabilityMeasure P] hind in
/-- Almost surely the projected displacement is the raw displacement. -/
theorem ae_proj_eq_raw (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) :
    ∀ᵐ ω ∂P, ((p ((raw n) ω) : 𝕍) : J → ℝ) = (raw n) ω := by
  filter_upwards [ae_sampleResponse_sub_mem_dirSpan hS ν P D hDν Xs hXm hid hlaw hn] with ω hω
  have := hp ⟨(raw n) ω, hω⟩
  rw [this]

omit [DecidableEq J] [IsProbabilityMeasure P] hind in
theorem ae_norm_proj_eq (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) :
    ∀ᵐ ω ∂P, ‖p ((raw n) ω)‖ = ‖(raw n) ω‖ := by
  filter_upwards [ae_proj_eq_raw hS ν P D hDν Xs hXm hid hlaw hn p hp] with ω hω
  rw [Submodule.coe_norm, hω]

omit [Nonempty X] [Nonempty J] [DecidableEq J] [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
  [IsProbabilityMeasure D] hDν hid hlaw hind hn in
/-- The projected displacement is measurable. -/
theorem measurable_proj_raw (p : (J → ℝ) →ₗ[ℝ] 𝕍) : Measurable fun ω ↦ p ((raw n) ω) :=
  (LinearMap.continuous_of_finiteDimensional p).measurable.comp
    (measurable_sampleResponse_sub hS D Xs hXm)

variable {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B)
include hB0 hB

omit [DecidableEq J] in
/-- **The third absolute moment of the projected displacement** is `O(n^{−3/2})`. -/
theorem integral_norm_pow_three_proj_le (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) :
    ∫ ω, ‖p ((raw n) ω)‖ ^ 3 ∂P ≤ Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 /
      (n * Real.sqrt n) := by
  have e : ∫ ω, ‖p ((raw n) ω)‖ ^ 3 ∂P = ∫ ω, ‖(raw n) ω‖ ^ 3 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_norm_proj_eq hS ν P D hDν Xs hXm hid hlaw hn p hp] with ω hω
    rw [hω]
  rw [e]
  exact integral_norm_pow_three_sampleResponse_sub_le hS P D Xs hXm hid hlaw hind hB0 hB hn

omit [Nonempty X] [Nonempty J] [DecidableEq J] [IsProbabilityMeasure ν] hS [MeasurableSpace Ω] hDν
  hXm hid hlaw hind hB0 in
/-- The projected displacement is bounded. -/
theorem norm_proj_raw_le (p : (J → ℝ) →ₗ[ℝ] 𝕍) (ω : Ω) :
    ‖p ((raw n) ω)‖ ≤ ‖LinearMap.toContinuousLinearMap p‖ * (Fintype.card J * (2 * B)) :=
  calc ‖p ((raw n) ω)‖ = ‖LinearMap.toContinuousLinearMap p ((raw n) ω)‖ := rfl
    _ ≤ ‖LinearMap.toContinuousLinearMap p‖ * ‖(raw n) ω‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖LinearMap.toContinuousLinearMap p‖ * (Fintype.card J * (2 * B)) :=
        mul_le_mul_of_nonneg_left (norm_sampleResponse_sub_le D Xs hB hn ω) (norm_nonneg _)

omit [Nonempty X] [Nonempty J] [DecidableEq J] [IsProbabilityMeasure ν] hDν hid hlaw hind hB0 in
theorem integrable_proj_raw (p : (J → ℝ) →ₗ[ℝ] 𝕍) : Integrable (fun ω ↦ p ((raw n) ω)) P :=
  Integrable.of_bound (measurable_proj_raw hS ν D Xs hXm p).aestronglyMeasurable _
    (ae_of_all _ fun ω ↦ norm_proj_raw_le ν D Xs hn hB p ω)

omit [Nonempty X] [Nonempty J] [DecidableEq J] [IsProbabilityMeasure ν] hDν hid hlaw hind hB0 in
theorem integrable_norm_pow_three_proj_raw (p : (J → ℝ) →ₗ[ℝ] 𝕍) :
    Integrable (fun ω ↦ ‖p ((raw n) ω)‖ ^ 3) P := by
  refine Integrable.of_bound
    ((measurable_proj_raw hS ν D Xs hXm p).norm.pow_const 3).aestronglyMeasurable
    ((‖LinearMap.toContinuousLinearMap p‖ * (Fintype.card J * (2 * B))) ^ 3)
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_proj_raw_le ν D Xs hn hB p ω) 3

omit [Nonempty X] [Nonempty J] [DecidableEq J] [IsProbabilityMeasure ν] hDν hid hlaw hind hB0 in
/-- The raw displacement is integrable. -/
theorem integrable_raw : Integrable (raw n) P :=
  Integrable.of_bound (measurable_sampleResponse_sub hS D Xs hXm).aestronglyMeasurable
    (Fintype.card J * (2 * B)) (ae_of_all _ fun ω ↦ norm_sampleResponse_sub_le D Xs hB hn ω)

omit [Nonempty X] [Nonempty J] [DecidableEq J] [IsProbabilityMeasure ν] hDν hind hB0 in
/-- **The raw displacement is centred.** -/
theorem integral_raw_eq_zero : ∫ ω, (raw n) ω ∂P = 0 := by
  funext j
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J ↦ ℝ) j).integral_comp_comm
    (integrable_raw hS P D Xs hXm hn hB)
  simp only [ContinuousLinearMap.proj_apply] at h
  rw [Pi.zero_apply, ← h]
  have hrawj : Integrable (fun ω ↦ (raw n) ω j) P :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J ↦ ℝ) j).integrable_comp
      (integrable_raw hS P D Xs hXm hn hB)
  have hsr : Integrable (fun ω ↦ sampleResponse S Xs n ω j) P := by
    refine (hrawj.add (integrable_const (∫ x, S j x ∂D))).congr
      (Eventually.of_forall fun ω ↦ ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  change ∫ ω, (sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ∂P = 0
  rw [integral_sub hsr (integrable_const _), integral_sampleResponse hS P D Xs hXm hid hlaw hn j,
    integral_const, probReal_univ, one_smul, sub_self]

omit [Nonempty X] [Nonempty J] [DecidableEq J] [IsProbabilityMeasure ν] hDν hind hB0 in
/-- **The projected displacement is centred.** -/
theorem integral_proj_raw_eq_zero (p : (J → ℝ) →ₗ[ℝ] 𝕍) : ∫ ω, p ((raw n) ω) ∂P = 0 := by
  have h := (LinearMap.toContinuousLinearMap p).integral_comp_comm
    (integrable_raw hS P D Xs hXm hn hB)
  rw [integral_raw_eq_zero hS P D Xs hXm hid hlaw hn hB, map_zero] at h
  exact h

variable {δ : ℝ}

/-- The certified ball `{‖z‖ ≤ δ}`. -/
local notation "cball" => Metric.closedBall (0 : 𝕍) δ

omit [DecidableEq J] [IsProbabilityMeasure P] [IsProbabilityMeasure D] hDν hid hlaw hind hn hB0
  hB in
/-- **The law-level set integral is the expectation of the reset-localised estimator**: the set
integral over the certified ball on the law of `ξ_n` is the integral over the good event
`{‖ξ_n‖ ≤ δ}`. -/
theorem setIntegral_map_proj (p : (J → ℝ) →ₗ[ℝ] 𝕍) (θ₀ : 𝕍)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm) :
    ∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀)
        ∂(P.map fun ω ↦ p ((raw n) ω)) =
      ∫ ω in (fun ω ↦ p ((raw n) ω)) ⁻¹' cball,
        (θr (mean (θ₀ : J → ℝ) + ((p ((raw n) ω) : 𝕍) : J → ℝ)) - θ₀) ∂P := by
  have hs : MeasurableSet cball := Metric.isClosed_closedBall.measurableSet
  have hξm := measurable_proj_raw hS ν D Xs hXm (n := n) p
  have hballdom : cball ⊆ responseBallDomain S ν θ₀ := fun z hz ↦ by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hdom z hz
  have hcont : ContinuousOn (fun z : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀) cball :=
    ((contDiffOn_responseTheta_meanAdd hS ν θ₀).continuousOn.mono hballdom).sub
      continuousOn_const
  have hf : AEStronglyMeasurable (fun z : 𝕍 ↦ θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀)
      ((P.map fun ω ↦ p ((raw n) ω)).restrict cball) := hcont.aestronglyMeasurable hs
  rw [Measure.restrict_map hξm hs] at hf ⊢
  exact integral_map hξm.aemeasurable hf

/-- **THE i.i.d. SAMPLING BIAS OF THE LOCALISED RESPONSE**: for the reset-localised response of
`n` i.i.d. samples,
`‖ E[θ̂_loc − θ₀] + (1/(2n)) ∑_{a,b} Cov_D(S_a,S_b) C(A⁻¹p e_a, A⁻¹p e_b) ‖
  ≤ (‖A⁻¹‖/δ² + K + ½‖A⁻¹‖‖T‖‖A⁻¹‖²/δ) · √3 |J|³ (2B)³ / n^{3/2}`. -/
theorem iid_localizedBias_curvature (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w)
    (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z +
        (1 / 2 : ℝ) • curvatureForm hS ν θ₀ z‖ ≤ K * ‖z‖ ^ 3) :
    ‖(∫ z in cball, (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀)
          ∂(P.map fun ω ↦ p ((raw n) ω))) +
        (1 / 2 : ℝ) • ((1 / n : ℝ) • covContraction hS ν D p θ₀)‖ ≤
      (‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ / δ ^ 2 + K +
        (1 / 2 : ℝ) * (‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ * ‖thirdOp hS ν θ₀‖ *
          ‖((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍)‖ ^ 2) / δ) *
        (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) := by
  have hξm := measurable_proj_raw hS ν D Xs hXm (n := n) p
  have : IsProbabilityMeasure (P.map fun ω ↦ p ((raw n) ω)) :=
    Measure.isProbabilityMeasure_map hξm.aemeasurable
  have hidm : AEStronglyMeasurable (fun z : 𝕍 ↦ z) (P.map fun ω ↦ p ((raw n) ω)) :=
    aestronglyMeasurable_id
  have h3m : AEStronglyMeasurable (fun z : 𝕍 ↦ ‖z‖ ^ 3) (P.map fun ω ↦ p ((raw n) ω)) :=
    (by fun_prop : Continuous fun z : 𝕍 ↦ ‖z‖ ^ 3).aestronglyMeasurable
  have hcm : AEStronglyMeasurable (fun z : 𝕍 ↦ curvatureForm hS ν θ₀ z)
      (P.map fun ω ↦ p ((raw n) ω)) := (continuous_curvatureForm hS ν θ₀).aestronglyMeasurable
  have hcent : ∫ z, z ∂(P.map fun ω ↦ p ((raw n) ω)) = 0 := by
    rw [integral_map hξm.aemeasurable hidm]
    exact integral_proj_raw_eq_zero hS ν P D Xs hXm hid hlaw hn hB p
  have hint : Integrable (fun z : 𝕍 ↦ z) (P.map fun ω ↦ p ((raw n) ω)) :=
    (integrable_map_measure hidm hξm.aemeasurable).2 (integrable_proj_raw hS ν P D Xs hXm hn hB p)
  have h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) (P.map fun ω ↦ p ((raw n) ω)) :=
    (integrable_map_measure h3m hξm.aemeasurable).2
      (integrable_norm_pow_three_proj_raw hS ν P D Xs hXm hn hB p)
  have hM3 : ∫ z, ‖z‖ ^ 3 ∂(P.map fun ω ↦ p ((raw n) ω)) ≤
      Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n) := by
    rw [integral_map hξm.aemeasurable h3m]
    exact integral_norm_pow_three_proj_le hS ν P D hDν Xs hXm hid hlaw hind hn hB0 hB p hp
  have hcurv : ∫ z, curvatureForm hS ν θ₀ z ∂(P.map fun ω ↦ p ((raw n) ω)) =
      (1 / n : ℝ) • covContraction hS ν D p θ₀ := by
    rw [integral_map hξm.aemeasurable hcm]
    exact integral_curvatureForm_sampleResponse hS ν P D Xs hXm hid hlaw hn p
      (fun i k hik ↦ hind.indepFun hik) θ₀
  have h := localizedBias_curvature hS ν (P.map fun ω ↦ p ((raw n) ω)) θ₀ hδ hK hdom hrem hcent
    hint h3
  rw [hcurv] at h
  refine h.trans (mul_le_mul_of_nonneg_left hM3 ?_)
  exact add_nonneg (add_nonneg (by positivity) hK) (by positivity)

end IID

end Laplace.Multi
