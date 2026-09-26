/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RegressionOrthogonality
import Laplace.Multi.ResponseTransport
import Laplace.Multi.PlugInCovariance

/-!
# Tangent Pythagoras and the Fisher-dual influence function

At a reconstructed law `Q_M` a centred data score `a ∈ L²(Q_M)` splits as its regression on the
tangent scores plus a normal part, and `E_Q a² = g_M(u, u) + E_Q (N_M a)²` with `u = Cov_Q(S, a)`
the visible direction of `a` (`tangent_pythagoras`): the differential version of the KL Pythagoras
of the information projection. The influence function of an observable is exactly its regression
part `ψ_{F,M} = B_M F` (`influence_eq_regProj`), it represents the differential of the reconstructed
response on tangent scores, `E_Q[ψ_{F,M} ℓ_{M,u}] = lin_{F,M}(u)`
(`integral_influence_mul_responseScore`), and its variance is the Fisher form of the covariance vector, `Var_Q ψ_{F,M} = g_M(c_F, c_F)`
(`lawCov_influence_self`). Under the data law the sandwich covariance of plug-in
reconstructions is `E_D[ψ_F ψ_G]` (`plugIn_covariance_tendsto_influence`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

variable {M : J → ℝ}

/-- The regression part has squared `L²(Q)`-norm the Fisher form of the covariance vector. -/
theorem integral_regProj_sq_eq_fisherForm {g : X → ℝ} (hg : Bdd g) :
    ∫ x, regProj hS ν M hg x ^ 2 ∂(Pfam (θr M)) =
      fisherForm hS ν M ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩
        ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩ := by
  unfold regProj fisherForm
  simp only [sq]

/-- The influence function is the regression part of the observable. -/
theorem influence_eq_regProj {F : X → ℝ} (hF : Bdd F) (x : X) :
    influence hS ν M hF x = regProj hS ν M hF x := by
  unfold influence regProj responseScore
  simp only [dotJ, dirLoss, statPoint, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **Tangent Pythagoras**: `E_Q (a − E_Q a)² = g_M(u, u) + E_Q (N_M a)²` with
`u = Cov_Q(S, a)` the visible direction of the data score `a`. -/
theorem tangent_pythagoras {g : X → ℝ} (hg : Bdd g) :
    ∫ x, (g x - ∫ y, g y ∂(Pfam (θr M))) ^ 2 ∂(Pfam (θr M)) =
      fisherForm hS ν M ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩
        ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩ +
        ∫ x, normalProj hS ν M hg x ^ 2 ∂(Pfam (θr M)) := by
  rw [integral_sq_sub_eq_regProj_add_normalProj hS ν hrel hg,
    integral_regProj_sq_eq_fisherForm hS ν hg]

/-- **The influence function represents the differential on tangent scores**:
`E_Q[ψ_{F,M} ℓ_{M,u}] = lin_{F,M}(u)`. -/
theorem integral_influence_mul_responseScore {F : X → ℝ} (hF : Bdd F) (u : 𝕍) :
    ∫ x, influence hS ν M hF x * responseScore hS ν M u x ∂(Pfam (θr M)) =
      linForm hS ν M hF (u : J → ℝ) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  rw [← integral_mul_responseScore_eq_linForm hS ν hF u]
  simp only [influence_eq_regProj hS ν hF]
  have hℓ := bdd_responseScore hS ν M u
  have hB : Bdd (regProj hS ν M hF) := bdd_responseScore hS ν M _
  have hN : Bdd (normalProj hS ν M hF) := bdd_normalProj hS ν hF
  have e : ∀ x, F x * responseScore hS ν M u x =
      ((∫ y, F y ∂(Pfam (θr M))) * responseScore hS ν M u x +
        regProj hS ν M hF x * responseScore hS ν M u x) +
        normalProj hS ν M hF x * responseScore hS ν M u x := by
    intro x
    have := sub_integral_eq_regProj_add_normalProj hS ν (M := M) hF x
    linear_combination (responseScore hS ν M u x) * this
  have h1 : Integrable (fun x ↦ (∫ y, F y ∂(Pfam (θr M))) * responseScore hS ν M u x)
      (Pfam (θr M)) := (integrable_of_bdd_prob _ hℓ).const_mul _
  have h2 : Integrable (fun x ↦ regProj hS ν M hF x * responseScore hS ν M u x) (Pfam (θr M)) :=
    integrable_of_bdd_prob _ (hB.mul hℓ)
  have h3 : Integrable (fun x ↦ normalProj hS ν M hF x * responseScore hS ν M u x)
      (Pfam (θr M)) := integrable_of_bdd_prob _ (hN.mul hℓ)
  have h12 : Integrable (fun x ↦ (∫ y, F y ∂(Pfam (θr M))) * responseScore hS ν M u x +
      regProj hS ν M hF x * responseScore hS ν M u x) (Pfam (θr M)) := h1.add h2
  conv_rhs => rw [integral_congr_ae (Eventually.of_forall e)]
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_responseScore hS ν hrel,
    mul_zero, zero_add, integral_normalProj_mul_responseScore hS ν hrel hF u, add_zero]

/-- The influence function is centred under the reconstruction. -/
theorem integral_influence {F : X → ℝ} (hF : Bdd F) :
    ∫ x, influence hS ν M hF x ∂(Pfam (θr M)) = 0 := by
  simp only [influence_eq_regProj hS ν hF]
  unfold regProj
  exact integral_responseScore hS ν hrel _

/-- **The variance of the influence function is the Fisher form of the covariance vector**:
`Var_Q ψ_{F,M} = g_M(Cov_Q(S,F), Cov_Q(S,F))`. -/
theorem lawCov_influence_self {F : X → ℝ} (hF : Bdd F) :
    lawCov (Pfam (θr M)) (influence hS ν M hF) (influence hS ν M hF) =
      fisherForm hS ν M ⟨respCov hS ν M F, respCov_mem_dirSpan hS ν hF⟩
        ⟨respCov hS ν M F, respCov_mem_dirSpan hS ν hF⟩ := by
  unfold lawCov
  rw [integral_influence hS ν hrel hF, mul_zero, sub_zero,
    ← integral_regProj_sq_eq_fisherForm hS ν hF]
  simp only [influence_eq_regProj hS ν hF, sq]

/-- On visible increments the linear form is the influence function. -/
theorem linForm_statPoint_sub_eq_influence {F : X → ℝ} (hF : Bdd F) {x : X}
    (hx : statPoint S x - M ∈ 𝕍) :
    linForm hS ν M hF (statPoint S x - M) = influence hS ν M hF x := by
  have h := linForm_eq_neg_dotJ_influenceDir hS ν hrel hF ⟨_, hx⟩
  rw [h]
  rfl

omit hrel in
set_option linter.unusedFintypeInType false in
/-- Almost every feature vector of a law `D ≪ ν` differs visibly from a point of the moment body. -/
theorem ae_statPoint_sub_mem_dirSpan (D : Measure X) (hDν : D ≪ ν)
    (hM : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S) : ∀ᵐ x ∂D, statPoint S x - M ∈ 𝕍 := by
  have hν : ∀ᵐ x ∂ν, statPoint S x - M ∈ 𝕍 := by
    filter_upwards [ae_statPoint_mem_essRange measurable_const (fun _ ↦ one_pos) hS] with x hx
    exact sub_mem_dirSpan_of_mem_momentBody' hS ν hM (essRange_subset_momentBody S hx)
  exact hDν.ae_le hν

section Covariance

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hind : iIndepFun Xs P) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hXm hind hid hlaw

omit hrel in
/-- **The joint covariance of plug-in reconstructions is the data covariance of the influence
functions**: `n Cov(Ĝ_{F,n}, Ĝ_{G,n}) → E_D[ψ_{F,M} ψ_{G,M}]`. -/
theorem plugIn_covariance_tendsto_influence (hDν : D ≪ ν)
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ C : Set (J → ℝ), IsCompact C ∧ Convex ℝ C ∧
      C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) ∧ dataMoment D S ∈ C ∧
      ∀ [DecidablePred (· ∈ C)], ∀ {F G : X → ℝ} (hF : Bdd F) (hG : Bdd G) {BF BG : ℝ},
        (∀ x, |F x| ≤ BF) → (∀ x, |G x| ≤ BG) →
        Tendsto (fun n : ℕ ↦ (n : ℝ) *
          ((∫ ω, (plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) -
              obsResponse hS ν F (dataMoment D S)) *
            (plugIn hS ν G C (dataMoment D S) (sampleResponse S Xs n ω) -
              obsResponse hS ν G (dataMoment D S)) ∂P) -
          (∫ ω, plugIn hS ν F C (dataMoment D S) (sampleResponse S Xs n ω) -
              obsResponse hS ν F (dataMoment D S) ∂P) *
            ∫ ω, plugIn hS ν G C (dataMoment D S) (sampleResponse S Xs n ω) -
              obsResponse hS ν G (dataMoment D S) ∂P)) atTop
        (𝓝 (∫ x, influence hS ν (dataMoment D S) hF x * influence hS ν (dataMoment D S) hG x
          ∂D)) := by
  obtain ⟨C, hC, hCc, hCK, hMC, h⟩ :=
    plugIn_covariance_tendsto hS ν P D Xs hXm hind hid hlaw hDν hrel
  refine ⟨C, hC, hCc, hCK, hMC, ?_⟩
  intro _ F G hF hG BF BG hBF hBG
  have hlim := h hF hG hBF hBG
  have hae := ae_statPoint_sub_mem_dirSpan hS ν D hDν (intrinsicInterior_subset hrel)
  have heq : ∫ x, linForm hS ν (dataMoment D S) hF (fun j ↦ S j x - dataMoment D S j) *
      linForm hS ν (dataMoment D S) hG (fun j ↦ S j x - dataMoment D S j) ∂D =
      ∫ x, influence hS ν (dataMoment D S) hF x * influence hS ν (dataMoment D S) hG x ∂D := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have e : (fun j ↦ S j x - dataMoment D S j) = statPoint S x - dataMoment D S := rfl
    rw [e, linForm_statPoint_sub_eq_influence hS ν hrel hF hx,
      linForm_statPoint_sub_eq_influence hS ν hrel hG hx]
  rwa [heq] at hlim

end Covariance

end Laplace.Multi
