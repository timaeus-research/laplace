/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseObservableTransport
import Laplace.Multi.ResponseIIDSamplingBias
import Laplace.Multi.BoundaryBlowup

/-!
# Sampling geometry of an arbitrary posterior expectation

The structural coordinate is displaced by the truth and by sampling; this module transfers both to
the posterior expectation `E_{P_θ} F` of **any** bounded observable `F`, through one object.

* **The regression direction** `u_F ∈ W` (`regressionDir`): the Fisher–Riesz representative of the
  covariance functional `v ↦ Cov_{P_θ}(F, ⟨v, S⟩)`, so `G_θ(u_F, v) = Cov_{P_θ}(F, ⟨v,S⟩)` for every
  direction `v` (`fisherInner_regressionDir`). The centred feature `⟨u_F, S⟩` is the linear
  regression of `F` on the features: the residual `F − ⟨u_F,S⟩` is uncorrelated with every feature
  direction (`lawCov_regressionResidual_dirLoss`), its variance is `Var F − G_θ(u_F,u_F)`
  (`lawCov_regressionResidual_self`), and the explained variance `G_θ(u_F,u_F) = Cov(F, ⟨u_F,S⟩)`
  is at most `Var F` (`fisherInner_regressionDir_self_le`).
* **The influence of a mean displacement** (`hasDerivAt_lineObservable_zero`): along the response
  line `θ(m(θ₀) + t e)`, `d/dt E_{θ_t} F |_{t=0} = ⟨u_F, e⟩` — the Euclidean pairing of the
  displacement with the regression direction, for every `e ∈ W`.
* **The exact sampling variance** (`integral_dotJ_sampleResponse_sub_mul`): for `n` i.i.d. samples
  from any data law `D`, `E[⟨u, M̂_n − m_D⟩ ⟨w, M̂_n − m_D⟩] = Cov_D(⟨u,S⟩, ⟨w,S⟩)/n`; hence the
  linearised posterior expectations of finitely many observables have sampling covariance matrix
  `Cov_D(⟨u_F,S⟩, ⟨u_G,S⟩)/n`, and at a matched law `D = P_{θ₀}` this is the Fisher Gram matrix
  `G_{θ₀}(u_F, u_G)/n` of the regression directions (`integral_influence_mul_influence_matched`),
  whose diagonal is the explained variance over `n`, at most `Var_{θ₀} F / n`
  (`integral_sq_influence_matched_le`).
* **The observable resolution floor** (`sq_dotJ_regressionDir_le`, `observable_resolution_floor`):
  the signal `⟨u_F, e⟩²` of a truth displacement `e` in the observable `F` is at most
  `G(u_F,u_F) · |A⁻¹e|²_F`, so if the observable resolves the shift above its own sampling noise
  at a matched point then `n |A⁻¹ e|²_F ≥ 1`: **no posterior expectation resolves a truth shift
  better than the structural coordinate itself** — the response resolution floor of
  `ResponseSamplingResolution` transfers to every observable.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Laplace.Multi

section Regression

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The Fisher form as a bilinear form on the direction space. -/
noncomputable def fisherBilin (θ : 𝕍) : LinearMap.BilinForm ℝ 𝕍 :=
  LinearMap.mk₂ ℝ (fisherInner S ν θ) (fisherInner_add_left hS ν θ)
    (fun c u v ↦ by rw [smul_eq_mul]; exact fisherInner_smul_left ν θ c u v)
    (fun u v w ↦ by
      rw [fisherInner_comm hS ν, fisherInner_add_left hS ν, fisherInner_comm hS ν θ v,
        fisherInner_comm hS ν θ w])
    (fun c u v ↦ by
      rw [smul_eq_mul, fisherInner_comm hS ν, fisherInner_smul_left ν, fisherInner_comm hS ν])

omit [Nonempty J] in
theorem fisherBilin_apply (θ u v : 𝕍) : fisherBilin hS ν θ u v = fisherInner S ν θ u v := rfl

/-- The Fisher form is nondegenerate. -/
theorem fisherBilin_nondegenerate (θ : 𝕍) : (fisherBilin hS ν θ).Nondegenerate := by
  have hrefl : (fisherBilin hS ν θ).IsRefl := fun u v h ↦ by
    rw [fisherBilin_apply, fisherInner_comm hS ν] at h
    exact h
  refine hrefl.nondegenerate_iff_separatingLeft.2 fun u hu ↦ ?_
  by_contra h
  have := fisherInner_self_pos hS ν θ h
  rw [← fisherBilin_apply hS ν θ u u, hu u] at this
  exact lt_irrefl _ this

/-- **The Fisher–Riesz map**: the direction `u` with `G_θ(u, v) = ℓ(v)` for every `v ∈ W`. -/
noncomputable def fisherRiesz (θ : 𝕍) : Module.Dual ℝ 𝕍 ≃ₗ[ℝ] 𝕍 :=
  ((fisherBilin hS ν θ).toDual (fisherBilin_nondegenerate hS ν θ)).symm

theorem fisherInner_fisherRiesz (θ : 𝕍) (ℓ : Module.Dual ℝ 𝕍) (v : 𝕍) :
    G θ (fisherRiesz hS ν θ ℓ) v = ℓ v :=
  LinearMap.BilinForm.apply_toDual_symm_apply (B := fisherBilin hS ν θ)
    (hB := fisherBilin_nondegenerate hS ν θ) ℓ v

omit hS in
/-- The covariance vector `γ_F = (Cov_{P_θ}(F, S_j))_j`. -/
noncomputable def regressionCovVec (F : X → ℝ) (θ : 𝕍) : J → ℝ :=
  fun j ↦ lawCov (Pfam (θ : J → ℝ)) F (S j)

omit hS in
/-- The covariance functional `v ↦ Cov_{P_θ}(F, ⟨v, S⟩)` on the direction space. -/
noncomputable def covFunctional (F : X → ℝ) (θ : 𝕍) : Module.Dual ℝ 𝕍 :=
  ((∑ j, regressionCovVec ν F θ j • LinearMap.proj j : (J → ℝ) →ₗ[ℝ] ℝ)) ∘ₗ (𝕍).subtype

omit [Nonempty J] in
theorem covFunctional_apply {F : X → ℝ} (hF : Bdd F) (θ v : 𝕍) :
    covFunctional ν F θ v = lawCov (Pfam (θ : J → ℝ)) F (dirLoss S (v : J → ℝ)) := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  rw [lawCov_dirLoss_eq_sum hS (Pfam (θ : J → ℝ)) hF]
  simp only [covFunctional, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, regressionCovVec]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- **The regression direction** `u_F ∈ W`: the Fisher–Riesz representative of the covariance
functional, `G_θ(u_F, v) = Cov_{P_θ}(F, ⟨v, S⟩)` for every `v ∈ W`. -/
noncomputable def regressionDir (F : X → ℝ) (θ : 𝕍) : 𝕍 :=
  fisherRiesz hS ν θ (covFunctional ν F θ)

/-- The defining property of the regression direction. -/
theorem fisherInner_regressionDir {F : X → ℝ} (hF : Bdd F) (θ v : 𝕍) :
    G θ (regressionDir hS ν F θ) v = lawCov (Pfam (θ : J → ℝ)) F (dirLoss S (v : J → ℝ)) := by
  rw [regressionDir, fisherInner_fisherRiesz, covFunctional_apply hS ν hF]

/-- The regression `⟨u_F, S⟩` has the same covariance with every feature direction as `F`. -/
theorem lawCov_dirLoss_regressionDir {F : X → ℝ} (hF : Bdd F) (θ v : 𝕍) :
    lawCov (Pfam (θ : J → ℝ)) (dirLoss S (regressionDir hS ν F θ : J → ℝ))
        (dirLoss S (v : J → ℝ)) =
      lawCov (Pfam (θ : J → ℝ)) F (dirLoss S (v : J → ℝ)) :=
  fisherInner_regressionDir hS ν hF θ v

/-- **The regression residual is uncorrelated with every feature direction.** -/
theorem lawCov_regressionResidual_dirLoss {F : X → ℝ} (hF : Bdd F) (θ v : 𝕍) :
    lawCov (Pfam (θ : J → ℝ)) (fun x ↦ F x - dirLoss S (regressionDir hS ν F θ : J → ℝ) x)
      (dirLoss S (v : J → ℝ)) = 0 := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  rw [lawCov_sub_left_eq _ hF (bdd_dirLoss hS _) (bdd_dirLoss hS _),
    lawCov_dirLoss_regressionDir hS ν hF, sub_self]

/-- The explained variance is the covariance of `F` with its regression. -/
theorem fisherInner_regressionDir_self {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) :
    G θ (regressionDir hS ν F θ) (regressionDir hS ν F θ) =
      lawCov (Pfam (θ : J → ℝ)) F (dirLoss S (regressionDir hS ν F θ : J → ℝ)) :=
  fisherInner_regressionDir hS ν hF θ _

omit [Nonempty J] in
/-- Cauchy–Schwarz for the Fisher form. -/
theorem fisherInner_sq_le (θ u v : 𝕍) : G θ u v ^ 2 ≤ G θ u u * G θ v v := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  exact lawCov_sq_le _ (bdd_dirLoss hS _) (bdd_dirLoss hS _)

/-- **The explained variance is at most the variance**: `G_θ(u_F, u_F) ≤ Var_{P_θ} F`. -/
theorem fisherInner_regressionDir_self_le {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) :
    G θ (regressionDir hS ν F θ) (regressionDir hS ν F θ) ≤ lawCov (Pfam (θ : J → ℝ)) F F := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hcs := lawCov_sq_le (Pfam (θ : J → ℝ)) hF (bdd_dirLoss hS (regressionDir hS ν F θ : J → ℝ))
  rw [← fisherInner_regressionDir_self hS ν hF θ] at hcs
  have hnn := lawCov_self_nonneg (Pfam (θ : J → ℝ)) hF
  rcases eq_or_lt_of_le (fisherVar_nonneg hS ν (θ : J → ℝ) (regressionDir hS ν F θ : J → ℝ))
    with h0 | hpos
  · rw [← fisherInner_self] at h0
    rw [← h0]
    exact hnn
  · rw [← fisherInner_self] at hpos
    have hcs' : G θ (regressionDir hS ν F θ) (regressionDir hS ν F θ) ^ 2 ≤
        lawCov (Pfam (θ : J → ℝ)) F F *
          G θ (regressionDir hS ν F θ) (regressionDir hS ν F θ) := hcs
    rw [sq] at hcs'
    exact le_of_mul_le_mul_right hcs' hpos

/-- **Pythagoras for the regression**: `Var(F − ⟨u_F,S⟩) = Var F − G_θ(u_F, u_F)`. -/
theorem lawCov_regressionResidual_self {F : X → ℝ} (hF : Bdd F) (θ : 𝕍) :
    lawCov (Pfam (θ : J → ℝ)) (fun x ↦ F x - dirLoss S (regressionDir hS ν F θ : J → ℝ) x)
        (fun x ↦ F x - dirLoss S (regressionDir hS ν F θ : J → ℝ) x) =
      lawCov (Pfam (θ : J → ℝ)) F F -
        G θ (regressionDir hS ν F θ) (regressionDir hS ν F θ) := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hu := bdd_dirLoss hS (regressionDir hS ν F θ : J → ℝ)
  rw [lawCov_sub_left_eq _ hF hu (hF.sub hu), lawCov_comm _ F, lawCov_sub_left_eq _ hF hu hF,
    lawCov_comm _ (dirLoss S (regressionDir hS ν F θ : J → ℝ))
      (fun x ↦ F x - dirLoss S (regressionDir hS ν F θ : J → ℝ) x),
    lawCov_sub_left_eq _ hF hu hu, lawCov_comm _ (dirLoss S (regressionDir hS ν F θ : J → ℝ)) F,
    ← fisherInner_regressionDir_self hS ν hF θ]
  change _ - G θ _ _ - (G θ _ _ - G θ _ _) = _
  ring

/-- The response line at time `0` is the base point. -/
theorem responseLine_zero (θ₀ e : 𝕍) : responseLine hS ν θ₀ e 0 = θ₀ := by
  unfold responseLine
  rw [zero_smul, add_zero]
  exact responseTheta_meanMap hS ν θ₀

/-- The velocity of the response line at time `0` is `A_{θ₀}⁻¹ e`. -/
theorem responseLineVel_zero (θ₀ e : 𝕍) : responseLineVel hS ν θ₀ e 0 = (CDE θ₀).symm e := by
  unfold responseLineVel
  rw [responseLine_zero]

/-- `⟪u, A_θ⁻¹ e⟫_θ = −⟨u, e⟩` for `e ∈ W`. -/
theorem fisherInner_chartDerivEquiv_symm' (θ u e : 𝕍) :
    G θ u ((CDE θ).symm e) = -dotJ (u : J → ℝ) (e : J → ℝ) :=
  fisherInner_chartDerivEquiv_symm hS ν θ u e.2

/-- **The influence of a mean displacement on an observable**: along the response line
`θ(m(θ₀) + t e)`, `d/dt E_{θ_t} F |_{t=0} = ⟨u_F, e⟩`. -/
theorem hasDerivAt_lineObservable_zero {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) :
    HasDerivAt (lineObservable hS ν F θ₀ e)
      (dotJ (regressionDir hS ν F θ₀ : J → ℝ) (e : J → ℝ)) 0 := by
  have h := hasDerivAt_lineObservable hS ν hF θ₀ e (zero_mem_responseLineDomain hS ν θ₀ e)
  rw [responseLine_zero hS ν θ₀ e, responseLineVel_zero hS ν θ₀ e,
    ← fisherInner_regressionDir hS ν hF θ₀, fisherInner_chartDerivEquiv_symm' hS ν, neg_neg] at h
  exact h

/-- **The observable signal is bounded by the structural signal**:
`⟨u_F, e⟩² ≤ G_θ(u_F, u_F) · |A_θ⁻¹ e|²_F`. -/
theorem sq_dotJ_regressionDir_le (F : X → ℝ) (θ e : 𝕍) :
    dotJ (regressionDir hS ν F θ : J → ℝ) (e : J → ℝ) ^ 2 ≤
      G θ (regressionDir hS ν F θ) (regressionDir hS ν F θ) *
        G θ ((CDE θ).symm e) ((CDE θ).symm e) := by
  have h := fisherInner_sq_le hS ν θ (regressionDir hS ν F θ) ((CDE θ).symm e)
  rw [fisherInner_chartDerivEquiv_symm' hS ν, neg_sq] at h
  exact h

end Regression

section Sampling

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hS hXm hid hlaw

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The raw empirical displacement `M̂_n − m_D`. -/
local notation "raw" n => (fun ω : Ω ↦ fun j : J ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] [IsProbabilityMeasure D] hid
  hlaw in
/-- A product of two coordinates of the empirical displacement is integrable. -/
theorem integrable_sampleResponse_sub_mul_sub {n : ℕ} (hn : 0 < n) (a b : J) :
    Integrable (fun ω ↦ (sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
      (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) P := by
  have e : (fun ω ↦ (sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
      (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) = fun ω ↦ (1 / (n : ℝ) ^ 2) *
        ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
          (S a (Xs i ω) - ∫ x, S a x ∂D) * (S b (Xs k ω) - ∫ x, S b x ∂D) := by
    funext ω
    rw [sampleResponse_sub_eq D Xs hn ω a, sampleResponse_sub_eq D Xs hn ω b, div_mul_div_comm,
      Finset.sum_mul_sum]
    ring
  rw [e]
  exact (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun k _ ↦
    integrable_comp_Xs_mul P Xs hXm i k ((hS a).sub (Bdd.const _))
      ((hS b).sub (Bdd.const _))).const_mul _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The exact sampling covariance of two linear statistics of the empirical displacement**:
`E[⟨u, M̂_n − m_D⟩ ⟨w, M̂_n − m_D⟩] = Cov_D(⟨u,S⟩, ⟨w,S⟩) / n`. -/
theorem integral_dotJ_sampleResponse_sub_mul (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (u w : J → ℝ) :
    ∫ ω, dotJ u ((raw n) ω) * dotJ w ((raw n) ω) ∂P =
      lawCov D (dirLoss S u) (dirLoss S w) / n := by
  have e : ∀ ω, dotJ u ((raw n) ω) * dotJ w ((raw n) ω) = ∑ a, ∑ b, (u a * w b) *
      ((sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
        (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) := by
    intro ω
    simp only [dotJ, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦
    (integrable_sampleResponse_sub_mul_sub hS P D Xs hXm hn a b).const_mul _]
  have e2 : ∀ a, ∫ ω, ∑ b, (u a * w b) * ((sampleResponse S Xs n ω a - ∫ x, S a x ∂D) *
      (sampleResponse S Xs n ω b - ∫ x, S b x ∂D)) ∂P =
      ∑ b, (u a * w b) * (lawCov D (S a) (S b) / n) := by
    intro a
    rw [integral_finsetSum _ fun b _ ↦
      (integrable_sampleResponse_sub_mul_sub hS P D Xs hXm hn a b).const_mul _]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [integral_const_mul, integral_sampleResponse_sub_mul_sub hS P D Xs hXm hid hlaw hind hn,
      lawCov_eq_integral_centred D (hS a) (hS b)]
  simp_rw [e2]
  rw [lawCov_dirLoss_left hS D u _ (bdd_dirLoss hS w), Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [lawCov_comm, lawCov_dirLoss_left hS D w _ (hS a), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [lawCov_comm]
  ring

/-- **The sampling covariance matrix of the linearised posterior expectations**: for observables
`F`, `F'` with regression directions `u_F`, `u_{F'}` at `θ₀`,
`E[⟨u_F, M̂_n − m_D⟩ ⟨u_{F'}, M̂_n − m_D⟩] = Cov_D(⟨u_F,S⟩, ⟨u_{F'},S⟩) / n` for every data law. -/
theorem integral_influence_mul_influence (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (F F' : X → ℝ) (θ₀ : 𝕍) :
    ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) *
        dotJ (regressionDir hS ν F' θ₀ : J → ℝ) ((raw n) ω) ∂P =
      lawCov D (dirLoss S (regressionDir hS ν F θ₀ : J → ℝ))
        (dirLoss S (regressionDir hS ν F' θ₀ : J → ℝ)) / n :=
  integral_dotJ_sampleResponse_sub_mul hS P D Xs hXm hid hlaw hind hn _ _

/-- **At a matched law the sampling covariance matrix is the Fisher Gram matrix of the regression
directions over `n`**: `E[⟨u_F, ξ_n⟩ ⟨u_{F'}, ξ_n⟩] = G_{θ₀}(u_F, u_{F'}) / n`. -/
theorem integral_influence_mul_influence_matched
    (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P) {n : ℕ} (hn : 0 < n) (F F' : X → ℝ)
    (θ₀ : 𝕍) (hD : D = Pfam (θ₀ : J → ℝ)) :
    ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) *
        dotJ (regressionDir hS ν F' θ₀ : J → ℝ) ((raw n) ω) ∂P =
      G θ₀ (regressionDir hS ν F θ₀) (regressionDir hS ν F' θ₀) / n := by
  rw [integral_influence_mul_influence hS ν P D Xs hXm hid hlaw hind hn F F' θ₀, hD]
  rfl

/-- **The sampling variance of a linearised posterior expectation at a matched law is the explained
variance over `n`, at most `Var_{θ₀} F / n`.** -/
theorem integral_sq_influence_matched_le (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) (hD : D = Pfam (θ₀ : J → ℝ)) :
    ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) ^ 2 ∂P ≤
      lawCov (Pfam (θ₀ : J → ℝ)) F F / n := by
  have h := integral_influence_mul_influence_matched hS ν P D Xs hXm hid hlaw hind hn F F θ₀ hD
  simp_rw [← sq] at h
  rw [h]
  exact div_le_div_of_nonneg_right (fisherInner_regressionDir_self_le hS ν hF θ₀)
    (Nat.cast_nonneg n)

/-- **The observable resolution floor**: at a matched law, if the observable `F` resolves the truth
displacement `e` above its own sampling noise, `E[⟨u_F, ξ_n⟩²] ≤ ⟨u_F, e⟩²`, then
`n · |A_{θ₀}⁻¹ e|²_F ≥ 1`: no posterior expectation resolves a truth shift that the structural
coordinate does not resolve. -/
theorem observable_resolution_floor (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P) {n : ℕ}
    (hn : 0 < n) (F : X → ℝ) (θ₀ e : 𝕍) (hD : D = Pfam (θ₀ : J → ℝ))
    (hpos : 0 < G θ₀ (regressionDir hS ν F θ₀) (regressionDir hS ν F θ₀))
    (hres : ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) ^ 2 ∂P ≤
      dotJ (regressionDir hS ν F θ₀ : J → ℝ) (e : J → ℝ) ^ 2) :
    1 ≤ n * G θ₀ ((CDE θ₀).symm e) ((CDE θ₀).symm e) := by
  have h := integral_influence_mul_influence_matched hS ν P D Xs hXm hid hlaw hind hn F F θ₀ hD
  simp_rw [← sq] at h
  rw [h] at hres
  have hcs := sq_dotJ_regressionDir_le hS ν F θ₀ e
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have key : G θ₀ (regressionDir hS ν F θ₀) (regressionDir hS ν F θ₀) / n ≤
      G θ₀ (regressionDir hS ν F θ₀) (regressionDir hS ν F θ₀) *
        G θ₀ ((CDE θ₀).symm e) ((CDE θ₀).symm e) := hres.trans hcs
  rw [div_le_iff₀ hn'] at key
  have := le_of_mul_le_mul_left (by linarith [key] :
    G θ₀ (regressionDir hS ν F θ₀) (regressionDir hS ν F θ₀) * 1 ≤
      G θ₀ (regressionDir hS ν F θ₀) (regressionDir hS ν F θ₀) *
        (G θ₀ ((CDE θ₀).symm e) ((CDE θ₀).symm e) * n)) hpos
  linarith

end Sampling

end Laplace.Multi
