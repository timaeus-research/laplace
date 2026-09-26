/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BiasForm
import Laplace.Multi.ReconstructionC1
import Laplace.Multi.ReconstructionBias
import Laplace.Multi.ResponsePathDifferential
import Laplace.Multi.StraightPathAtlas

/-!
# Transport of reconstructed responses along paths of data

The reconstructed response `G_F(M) = ∫ F dQ_M` of a bounded observable changes along a
differentiable curve of interior responses at the rate `lin_{F,M}(Ṁ)`
(`hasDerivAt_integral_response_path`), so `G_F(M(1)) − G_F(M(0)) = ∫₀¹ lin_{F,M(s)}(M'(s)) ds`
(`integral_response_sub_eq_integral_linForm`).
The linear form is represented by the covariance vector, `lin_{F,M}(u) = −⟨R_M u, Cov_{Q_M}(S,F)⟩`
(`linForm_eq_neg_dotJ_respCov`), equivalently by the **influence function**
`ψ_{F,M}(x) = −⟨R_M Cov_{Q_M}(S,F), S(x) − M⟩`: along the affine data path `(1−t)ν + tD`, whose
response path is the straight atlas, `d/dt G_F(M_t) = ∫ ψ_{F,M_t} dD − ∫ ψ_{F,M_t} dν`
(`hasDerivAt_integral_response_atlas_influence`).
-/

open MeasureTheory Filter Topology Set

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

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The inverse chart derivative at a response, as a continuous linear map. -/
local notation "Rat" M => (ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)

/-- The inverse chart derivative at a response. -/
local notation "Rinv" M => ContinuousLinearEquiv.symm (CDE (θr M))

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

variable {M : J → ℝ}

/-- **Covariance representation of the linear form**: `lin_{F,M}(u) = −⟨R_M u, Cov_{Q_M}(S, F)⟩`
for visible `u`. -/
theorem linForm_eq_neg_dotJ_respCov
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {F : X → ℝ} (hF : Bdd F)
    (u : 𝕍) :
    linForm hS ν M hF (u : J → ℝ) = -dotJ ((Rinv M) u : J → ℝ) (respCov hS ν M F) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  rw [← integral_mul_responseScore_eq_linForm hS ν hF u]
  have h : ∫ x, F x * responseScore hS ν M u x ∂(Pfam (θr M)) =
      lawCov (Pfam (θr M)) F (responseScore hS ν M u) := by
    unfold lawCov
    rw [integral_responseScore hS ν hrel, mul_zero, sub_zero]
  rw [h, lawCov_comm]
  unfold responseScore
  rw [lawCov_sub_left_eq _ (Bdd.const _) (bdd_dirLoss hS _) hF, lawCov_const_left_eq_zero,
    zero_sub, lawCov_dirLoss_left hS (Pfam (θr M)) _ _ hF]
  rfl

/-- **The influence function** of the reconstructed response of `F` at `M`:
`ψ_{F,M}(x) = −⟨R_M Cov_{Q_M}(S,F), S(x) − M⟩`. -/
noncomputable def influence (M : J → ℝ) {F : X → ℝ} (hF : Bdd F) : X → ℝ := fun x ↦
  -dotJ ((Rinv M) ⟨respCov hS ν M F, respCov_mem_dirSpan hS ν hF⟩ : J → ℝ) (statPoint S x - M)

/-- The inverse chart derivative is symmetric for the coordinate pairing. -/
theorem dotJ_inverse_chart_symm
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (u w : 𝕍) :
    dotJ ((Rinv M) u : J → ℝ) (w : J → ℝ) = dotJ ((Rinv M) w : J → ℝ) (u : J → ℝ) := by
  have h1 := integral_responseScore_mul hS ν hrel u w
  have h2 := integral_responseScore_mul hS ν hrel w u
  have e : (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x) =
      fun x ↦ responseScore hS ν M w x * responseScore hS ν M u x :=
    funext fun x ↦ mul_comm _ _
  rw [e] at h1
  linarith

/-- The linear form is the pairing of the influence direction with the visible increment. -/
theorem linForm_eq_neg_dotJ_influenceDir
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {F : X → ℝ} (hF : Bdd F)
    (u : 𝕍) :
    linForm hS ν M hF (u : J → ℝ) =
      -dotJ ((Rinv M) ⟨respCov hS ν M F, respCov_mem_dirSpan hS ν hF⟩ : J → ℝ) (u : J → ℝ) := by
  rw [linForm_eq_neg_dotJ_respCov hS ν hrel hF u, dotJ_inverse_chart_symm hS ν hrel]

omit [Nonempty X] [Nonempty J] in
/-- Integrating an affine function of the features against a law gives its response. -/
theorem integral_dotJ_statPoint_sub (D : Measure X) [IsProbabilityMeasure D] (w N : J → ℝ) :
    ∫ x, dotJ w (statPoint S x - N) ∂D = dotJ w (dataMoment D S - N) := by
  simp only [dotJ, Pi.sub_apply, statPoint, dataMoment]
  have hint : ∀ j, Integrable (fun x ↦ w j * (S j x - N j)) D := fun j ↦
    (integrable_of_bdd_prob D ((hS j).sub (Bdd.const _))).const_mul _
  rw [integral_finsetSum _ fun j _ ↦ hint j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_const_mul, integral_sub (integrable_of_bdd_prob D (hS j)) (integrable_const _),
    integral_const, probReal_univ, one_smul]

/-- **The influence identity**: for a data law `D` with response in the moment body, the
linear form on `E_D S − m₀` is the difference of the influence-function expectations under `D`
and under the featureless law. -/
theorem linForm_sub_featureless_eq_integral_influence
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {F : X → ℝ} (hF : Bdd F)
    (D : Measure X) [IsProbabilityMeasure D]
    (hD : dataMoment D S ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S) :
    linForm hS ν M hF (dataMoment D S - m₀) =
      (∫ x, influence hS ν M hF x ∂D) - ∫ x, influence hS ν M hF x ∂ν := by
  have hmem : dataMoment D S - m₀ ∈ 𝕍 := sub_mem_dirSpan_of_mem_momentBody measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS hD
  have h := linForm_eq_neg_dotJ_influenceDir hS ν hrel hF ⟨_, hmem⟩
  rw [h]
  unfold influence
  simp only [← dotJ_neg_left]
  rw [integral_dotJ_statPoint_sub hS D, integral_dotJ_statPoint_sub hS ν]
  have hm : dataMoment ν S = m₀ := by rw [meanMap_zero_eq_mean]; rfl
  rw [hm]
  simp only [dotJ, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Transport of the reconstructed response along a path**: along a differentiable curve of
interior responses, `d/ds G_F(M(s)) = lin_{F,M(s)}(M'(s))`. -/
theorem hasDerivAt_integral_response_path {M : ℝ → J → ℝ} (hV : ∀ s, M s - m₀ ∈ 𝕍)
    {M' : J → ℝ} {s₀ : ℝ} (hrel : M s₀ ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hM' : HasDerivAt M M' s₀) {F : X → ℝ} (hF : Bdd F) :
    HasDerivAt (fun s ↦ ∫ x, F x ∂(Pfam (θr (M s)))) (linForm hS ν (M s₀) hF M') s₀ := by
  have hM'V : M' ∈ 𝕍 := deriv_mem_dirSpan_of_path hV hM'
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → 𝕍, ∀ s, (γ s : J → ℝ) = M s - m₀ :=
    ⟨fun s ↦ ⟨_, hV s⟩, fun s ↦ rfl⟩
  have e : ∀ s, m₀ + (γ s : J → ℝ) = M s := fun s ↦ by rw [hγ s, add_sub_cancel]
  have hγd : HasDerivAt γ ⟨M', hM'V⟩ s₀ := by
    refine hasDerivAt_subtype_of_hasDerivAt hM'V ?_
    simp only [hγ]
    exact hM'.sub_const _
  have hz : m₀ + (γ s₀ : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    rw [e]; exact hrel
  have h := (hasFDerivAt_integral_response_at hS ν hF hz).comp_hasDerivAt s₀ hγd
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp only [Function.comp_def, e]
  · rw [responseDerivField_apply hS ν hF hz, integral_mul_responseScore_eq_linForm hS ν hF]
    simp only [e]

/-- The natural coordinate is continuous along a continuous path of interior responses. -/
theorem continuousOn_responseTheta_path {M : ℝ → J → ℝ} (hV : ∀ s, M s - m₀ ∈ 𝕍) {I : Set ℝ}
    (hint : ∀ s ∈ I, M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hMc : ContinuousOn M I) : ContinuousOn (fun s ↦ θr (M s)) I := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → 𝕍, ∀ s, (γ s : J → ℝ) = M s - m₀ :=
    ⟨fun s ↦ ⟨_, hV s⟩, fun s ↦ rfl⟩
  have e : ∀ s, m₀ + (γ s : J → ℝ) = M s := fun s ↦ by rw [hγ s, add_sub_cancel]
  have hγc : ContinuousOn γ I := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (hMc.sub continuousOn_const).congr fun s _ ↦ hγ s
  have hθ : ContinuousOn (fun w : 𝕍 ↦ θr (m₀ + (w : J → ℝ))) (γ '' I) := by
    refine continuousOn_responseTheta_add hS ν fun z hz ↦ ?_
    obtain ⟨s, hs, rfl⟩ := hz
    rw [e]; exact hint s hs
  refine (hθ.comp hγc (mapsTo_image _ _)).congr fun s _ ↦ ?_
  simp only [Function.comp_def, e]

/-- The velocity field `s ↦ lin_{F,M(s)}(M'(s))` is continuous along a `C¹` path of interior
responses. -/
theorem continuousOn_linForm_path {M M' : ℝ → J → ℝ} (hV : ∀ s, M s - m₀ ∈ 𝕍) {I : Set ℝ}
    (hint : ∀ s ∈ I, M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hMc : ContinuousOn M I) (hM'c : ContinuousOn M' I) (hM'V : ∀ s ∈ I, M' s ∈ 𝕍)
    {F : X → ℝ} (hF : Bdd F) :
    ContinuousOn (fun s ↦ linForm hS ν (M s) hF (M' s)) I := by
  have hR : ContinuousOn (fun s ↦ (Rat (M s))) I :=
    (continuousOn_inverse_chart hS ν).comp hMc hint
  have hv : ContinuousOn (fun s ↦ dirProj S ν (M' s)) I :=
    (LinearMap.continuous_of_finiteDimensional _).comp_continuousOn hM'c
  have hθ := continuousOn_responseTheta_path hS ν hV hint hMc
  have hcov : ContinuousOn (fun s ↦ respCov hS ν (M s) F) I := by
    refine continuousOn_pi.2 fun j ↦ ?_
    have h1 : ContinuousOn (fun s ↦ ∫ x, S j x * F x ∂(Pfam (θr (M s)))) I :=
      (continuous_integral_family hS ν ((hS j).mul hF)).comp_continuousOn
        (continuous_subtype_val.comp_continuousOn hθ)
    have h2 : ContinuousOn (fun s ↦ ∫ x, S j x ∂(Pfam (θr (M s)))) I :=
      (continuous_integral_family hS ν (hS j)).comp_continuousOn
        (continuous_subtype_val.comp_continuousOn hθ)
    have h3 : ContinuousOn (fun s ↦ ∫ x, F x ∂(Pfam (θr (M s)))) I :=
      (continuous_integral_family hS ν hF).comp_continuousOn
        (continuous_subtype_val.comp_continuousOn hθ)
    exact h1.sub (h2.mul h3)
  have hRu : ContinuousOn (fun s ↦ ((Rat (M s)) (dirProj S ν (M' s)) : J → ℝ)) I :=
    continuous_subtype_val.comp_continuousOn (hR.clm_apply hv)
  have hdot : ContinuousOn
      (fun s ↦ -dotJ ((Rat (M s)) (dirProj S ν (M' s)) : J → ℝ) (respCov hS ν (M s) F)) I := by
    refine ContinuousOn.neg ?_
    simp only [dotJ]
    exact continuousOn_finsetSum _ fun j _ ↦
      ((continuous_apply j).comp_continuousOn hRu).mul ((continuous_apply j).comp_continuousOn hcov)
  refine hdot.congr fun s hs ↦ ?_
  have hu : M' s = ((⟨M' s, hM'V s hs⟩ : 𝕍) : J → ℝ) := rfl
  have hproj : dirProj S ν (M' s) = ⟨M' s, hM'V s hs⟩ := dirProj_coe S ν ⟨M' s, hM'V s hs⟩
  rw [hu, linForm_eq_neg_dotJ_respCov hS ν (hint s hs) hF]
  simp only [hproj, ContinuousLinearEquiv.coe_coe]

/-- **The fundamental theorem of calculus for the reconstructed response**: along a `C¹` path
of interior responses, `G_F(M(1)) − G_F(M(0)) = ∫₀¹ lin_{F,M(s)}(M'(s)) ds`. -/
theorem integral_response_sub_eq_integral_linForm {M M' : ℝ → J → ℝ} (hV : ∀ s, M s - m₀ ∈ 𝕍)
    (hint : ∀ s ∈ Icc (0 : ℝ) 1, M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    (hM' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt M (M' s) s) (hM'c : ContinuousOn M' (Icc 0 1))
    {F : X → ℝ} (hF : Bdd F) :
    (∫ x, F x ∂(Pfam (θr (M 1)))) - (∫ x, F x ∂(Pfam (θr (M 0)))) =
      ∫ s in (0 : ℝ)..1, linForm hS ν (M s) hF (M' s) := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ ∫ x, F x ∂(Pfam (θr (M s))))
      (linForm hS ν (M s) hF (M' s)) s := fun s hs ↦ by
    rw [uIcc_of_le zero_le_one] at hs
    exact hasDerivAt_integral_response_path hS ν hV (hint s hs) (hM' s hs) hF
  have hMc : ContinuousOn M (Icc 0 1) := fun s hs ↦ (hM' s hs).continuousAt.continuousWithinAt
  have hM'V : ∀ s ∈ Icc (0 : ℝ) 1, M' s ∈ 𝕍 := fun s hs ↦
    deriv_mem_dirSpan_of_path hV (hM' s hs)
  have hcont := continuousOn_linForm_path hS ν hV hint hMc hM'c hM'V hF
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable_of_Icc zero_le_one)).symm

/-- **The atlas transports the reconstructed response**: for an interior response `M`,
`G_F(M) − G_F(m₀) = ∫₀¹ lin_{F,M_s}(M − m₀) ds` along the straight atlas. -/
theorem integral_response_sub_featureless_eq_integral_atlas
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {F : X → ℝ}
    (hF : Bdd F) :
    (∫ x, F x ∂(Pfam (θr M))) - (∫ x, F x ∂(Pfam (θr m₀))) =
      ∫ s in (0 : ℝ)..1, linForm hS ν (atlasPath S ν M s) hF (M - m₀) := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  have hint : ∀ s ∈ Icc (0 : ℝ) 1,
      atlasPath S ν M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with h1 | h1
    · exact atlas_mem_intrinsicInterior hS ν hfin hs.1 h1
    · rw [h1, atlasPath_one]; exact hrel
  have h := integral_response_sub_eq_integral_linForm hS ν (M := atlasPath S ν M)
    (M' := fun _ ↦ M - m₀) (atlasPath_sub_mem_dirSpan hS ν hfin) hint
    (fun s _ ↦ hasDerivAt_atlasPath ν (M := M) s) continuousOn_const hF
  rwa [atlasPath_one, atlasPath_zero] at h

/-- **Influence form of the atlas transport**: along the affine data path `(1−t)ν + tD`, whose
response path is the straight atlas, the reconstructed response of `F` changes at the rate
`∫ ψ_{F,M_t} dD − ∫ ψ_{F,M_t} dν`, for `0 ≤ t < 1`. -/
theorem hasDerivAt_integral_response_atlas_influence (D : Measure X) [IsProbabilityMeasure D]
    (hrel : dataMoment D S ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {F : X → ℝ} (hF : Bdd F) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt (fun s ↦ ∫ x, F x ∂(Pfam (θr (atlasPath S ν (dataMoment D S) s))))
      ((∫ x, influence hS ν (atlasPath S ν (dataMoment D S) t) hF x ∂D) -
        ∫ x, influence hS ν (atlasPath S ν (dataMoment D S) t) hF x ∂ν) t := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
  have hI := atlas_mem_intrinsicInterior hS ν hfin ht0 ht1 (M := dataMoment D S)
  have h := hasDerivAt_integral_response_path hS ν (atlasPath_sub_mem_dirSpan hS ν hfin) hI
    (hasDerivAt_atlasPath ν (M := dataMoment D S) t) hF
  rwa [linForm_sub_featureless_eq_integral_influence hS ν hI hF D
    (intrinsicInterior_subset hrel)] at h

end Laplace.Multi
