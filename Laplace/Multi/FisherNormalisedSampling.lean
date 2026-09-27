/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SamplingResolution
import Laplace.Multi.ResponsePullbackForm
import Mathlib.LinearAlgebra.Trace

/-!
# Fisher-normalised sampling noise: the basis-free trace identity

The sampling error `M̂_n − m` of the structural coordinate is measured in the Fisher metric of the
response chart at `θ`: with `R_θ = ι ∘ (Dm(θ)|_W)⁻¹ ∘ p` for any retraction `p` of `J → ℝ` onto
the direction space `W` (the choice of `p` is invisible on `W`), the **Fisher-normalised sampling
energy** is `q_θ(z) = −⟨R_θ z, z⟩`, which on `W` is `|(Dm(θ)|_W)⁻¹ z|²_{F,θ} = zᵀ C_θ⁻¹ z`
(`samplingEnergy_eq_fisherVar`). Its expectation under `n` samples from any data law `D` is

`E q_θ(M̂_n − m) = tr(R_θ C_D) / n`
(`integral_samplingEnergy`, `integral_samplingEnergy_eq_trace`),

and at a **matched** law `D = P_θ` the operator `ι ∘ (Dm(θ)|_W)⁻¹ ∘ Dm(θ)` is a projection onto
`W`, so the trace is the dimension of the direction space:

`E q_θ(M̂_n − m) = dim W / n`   (`integral_samplingEnergy_family`).

The Fisher-normalised sampling noise is scale-free: it is `√(dim W / n)` at every response, in
every chart, which is the noise floor against which the response speed `|θ'|_F` of the pulled-back
form (`ResponsePullbackForm`) is to be compared.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Operator

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The ambient Jacobian of the mean map. -/
local notation "Dm" => meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit hS [Nonempty X] [Nonempty J] [Fintype J] [IsProbabilityMeasure ν] in
/-- A linear retraction of `J → ℝ` onto the direction space exists. -/
theorem exists_retraction : ∃ p : (J → ℝ) →ₗ[ℝ] 𝕍, ∀ w : 𝕍, p (w : J → ℝ) = w := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (𝕍).subtype (𝕍).ker_subtype
  exact ⟨g, fun w ↦ by simpa using LinearMap.congr_fun hg w⟩

/-- The Fisher-normalising operator `R_θ = ι ∘ (Dm(θ)|_W)⁻¹ ∘ p`. -/
noncomputable def samplingOp (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍) : (J → ℝ) →ₗ[ℝ] (J → ℝ) :=
  (𝕍).subtype ∘ₗ (CDE θ).symm.toLinearEquiv.toLinearMap ∘ₗ p

theorem samplingOp_apply (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (z : J → ℝ) :
    samplingOp hS ν θ p z = ((CDE θ).symm (p z) : J → ℝ) := rfl

/-- The Fisher-normalised sampling energy `q_θ(z) = −⟨R_θ z, z⟩`. -/
noncomputable def samplingEnergy (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (z : J → ℝ) : ℝ :=
  -dotJ (samplingOp hS ν θ p z) z

/-- The chart derivative of `(Dm(θ)|_W)⁻¹ z` is `z`. -/
theorem meanMapDeriv_chartDerivEquiv_symm (θ : 𝕍) (w : 𝕍) :
    Dm θ (((CDE θ).symm w : 𝕍) : J → ℝ) = (w : J → ℝ) := by
  change (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
    hS θ ((CDE θ).symm w) : J → ℝ) = (w : J → ℝ)
  rw [← ContinuousLinearMap.coe_coe (chartDeriv measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS θ), ← coe_chartDerivEquiv,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **On the direction space the sampling energy is the Fisher norm of the normalised error**:
`q_θ(z) = |(Dm(θ)|_W)⁻¹ z|²_{F,θ}` for `z ∈ W`, independently of the retraction. -/
theorem samplingEnergy_eq_fisherVar (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {z : J → ℝ} (hz : z ∈ 𝕍) :
    samplingEnergy hS ν θ p z =
      fisherVar S ν (θ : J → ℝ) (((CDE θ).symm ⟨z, hz⟩ : 𝕍) : J → ℝ) := by
  rw [fisherVar_eq_neg_dotJ hS ν, samplingEnergy, samplingOp_apply, hp ⟨z, hz⟩,
    meanMapDeriv_chartDerivEquiv_symm hS ν θ ⟨z, hz⟩]

/-- The matched normalising operator `N_θ = ι ∘ (Dm(θ)|_W)⁻¹ ∘ Dm(θ)`. -/
noncomputable def matchedOp (θ : 𝕍) : (J → ℝ) →ₗ[ℝ] (J → ℝ) :=
  (𝕍).subtype ∘ₗ (CDE θ).symm.toLinearEquiv.toLinearMap ∘ₗ
    ((Dm θ : (J → ℝ) →L[ℝ] (J → ℝ)) : (J → ℝ) →ₗ[ℝ] (J → ℝ)).codRestrict 𝕍
      (meanMapDeriv_mem_dirSpan measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS θ)

theorem matchedOp_apply (θ : 𝕍) (z : J → ℝ) :
    matchedOp hS ν θ z = ((CDE θ).symm ⟨Dm θ z, meanMapDeriv_mem_dirSpan measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS θ z⟩ : J → ℝ) := rfl

/-- The sampling operator applied to a Jacobian image is the matched operator. -/
theorem samplingOp_meanMapDeriv (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (z : J → ℝ) :
    samplingOp hS ν θ p (Dm θ z) = matchedOp hS ν θ z := by
  rw [samplingOp_apply, matchedOp_apply]
  congr 2
  exact hp ⟨Dm θ z, _⟩

/-- **The matched operator is a projection onto the direction space.** -/
theorem isProj_matchedOp (θ : 𝕍) : LinearMap.IsProj 𝕍 (matchedOp hS ν θ) := by
  refine ⟨fun z ↦ by rw [matchedOp_apply]; exact Subtype.mem _, fun z hz ↦ ?_⟩
  rw [matchedOp_apply]
  have e : (⟨Dm θ z, meanMapDeriv_mem_dirSpan measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS θ z⟩ : 𝕍) = CDE θ ⟨z, hz⟩ := by
    apply Subtype.ext
    rw [← ContinuousLinearEquiv.coe_coe, coe_chartDerivEquiv]
    rfl
  rw [e, ContinuousLinearEquiv.symm_apply_apply]

/-- **The trace of the matched operator is the dimension of the direction space.** -/
theorem trace_matchedOp (θ : 𝕍) :
    LinearMap.trace ℝ (J → ℝ) (matchedOp hS ν θ) = (Module.finrank ℝ 𝕍 : ℝ) :=
  (isProj_matchedOp hS ν θ).trace

end Operator

section Coordinates

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The ambient Jacobian of the mean map. -/
local notation "Dm" => meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- Coordinates of the sampling operator. -/
theorem samplingOp_apply_eq_sum (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (y : J → ℝ) (a : J) :
    samplingOp hS ν θ p y a = ∑ b, y b * samplingOp hS ν θ p (Pi.single b 1) a := by
  conv_lhs => rw [pi_eq_sum_univ' y, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The quadratic form of the sampling operator in coordinates. -/
theorem dotJ_samplingOp_eq (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍) (z : J → ℝ) :
    dotJ (samplingOp hS ν θ p z) z =
      ∑ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a * (z b * z a) := by
  simp only [dotJ, samplingOp_apply_eq_sum hS ν θ p z, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

omit [Nonempty X] [Nonempty J] hS in
/-- The trace of an operator in the coordinate basis. -/
theorem trace_eq_sum_single (f : (J → ℝ) →ₗ[ℝ] (J → ℝ)) :
    LinearMap.trace ℝ (J → ℝ) f = ∑ a, f (Pi.single a 1) a := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ J)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply,
    Pi.basisFun_repr]

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- A coordinate statistic as a directional loss. -/
theorem dirLoss_single_one (b : J) : dirLoss S (Pi.single b 1) = S b := by
  funext x
  simp [dirLoss, Pi.single_apply]

omit [Nonempty J] in
/-- The covariance of the statistics at a family law is minus the Jacobian:
`Cov_θ(S_a, S_b) = −(Dm(θ) e_a)_b`. -/
theorem lawCov_family_eq_neg_meanMapDeriv (θ : J → ℝ) (a b : J) :
    lawCov (Pfam θ) (S a) (S b) = -(Dm θ (Pi.single a 1)) b := by
  have h := dotJ_meanMapDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ (Pi.single b 1) (Pi.single a 1)
  rw [priorCov_eq_lawCov_familyMeasure hS ν, dirLoss_single_one, dirLoss_single_one,
    dotJ_single_left] at h
  rw [h, neg_neg, lawCov_comm]

/-- **The matched trace identity in coordinates**: `∑ (R_θ)_{ab} Cov_θ(S_a,S_b) = −dim W`. -/
theorem sum_samplingOp_lawCov_family (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) :
    ∑ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a * lawCov (Pfam (θ : J → ℝ)) (S a) (S b) =
      -(Module.finrank ℝ 𝕍 : ℝ) := by
  have h1 : ∀ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a *
      lawCov (Pfam (θ : J → ℝ)) (S a) (S b) = -(matchedOp hS ν θ (Pi.single a 1)) a := by
    intro a
    rw [← samplingOp_meanMapDeriv hS ν θ p hp, samplingOp_apply_eq_sum hS ν,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [lawCov_family_eq_neg_meanMapDeriv hS ν]
    ring
  simp only [h1, Finset.sum_neg_distrib]
  rw [← trace_eq_sum_single, trace_matchedOp]

end Coordinates

section Sampling

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
  (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
include hS hXm hid hlaw hind

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The expected Fisher-normalised sampling energy is a trace**:
`E q_θ(M̂_n − m) = −∑ (R_θ)_{ab} Cov_D(S_a, S_b) / n`. -/
theorem integral_samplingEnergy (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍) {n : ℕ} (hn : 0 < n) :
    ∫ ω, samplingEnergy hS ν θ p (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ∂P =
      -(∑ a, ∑ b, samplingOp hS ν θ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n := by
  have hexp : ∀ ω, samplingEnergy hS ν θ p (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) =
      ∑ a, ∑ b, (-samplingOp hS ν θ p (Pi.single b 1) a) *
        ((sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
          (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) := fun ω ↦ by
    rw [samplingEnergy, dotJ_samplingOp_eq, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦
    (integrable_sampleResponse_sub_mul hS P D Xs hXm hn a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ ↦
    (integrable_sampleResponse_sub_mul hS P D Xs hXm hn _ b).const_mul _,
    integral_const_mul, integral_sampleResponse_sub_mul_sub hS P D Xs hXm hid hlaw hind hn]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [lawCov_eq_integral_centred D (hS a) (hS b)]
  ring

/-- **The trace form**: `E q_θ(M̂_n − m) = −tr(R_θ C_D) / n` with `C_D` the covariance matrix of
the statistics under the data law. -/
theorem integral_samplingEnergy_eq_trace (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍) {n : ℕ} (hn : 0 < n) :
    ∫ ω, samplingEnergy hS ν θ p (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ∂P =
      -Matrix.trace (LinearMap.toMatrix (Pi.basisFun ℝ J) (Pi.basisFun ℝ J)
        (samplingOp hS ν θ p) * Matrix.of fun a b ↦ lawCov D (S a) (S b)) / n := by
  rw [integral_samplingEnergy hS ν P D Xs hXm hid hlaw hind θ p hn]
  congr 2
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [lawCov_comm]

omit [DecidableEq J] hlaw in
/-- **The matched trace identity**: with `n` samples from the family law `P_θ` itself, the
expected Fisher-normalised sampling energy of the structural coordinate is `dim W / n`,
independently of `θ` and of the retraction. -/
theorem integral_samplingEnergy_family (θ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (hlaw : P.map (Xs 0) = Pfam (θ : J → ℝ))
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, samplingEnergy hS ν θ p
        (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂(Pfam (θ : J → ℝ))) ∂P =
      (Module.finrank ℝ 𝕍 : ℝ) / n := by
  classical
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  rw [integral_samplingEnergy hS ν P _ Xs hXm hid hlaw hind θ p hn,
    sum_samplingOp_lawCov_family hS ν θ p hp, neg_neg]

end Sampling

end Laplace.Multi
