/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSimplexCurvature
import Laplace.Multi.AbsolutelyContinuousForcing
import Laplace.Multi.ResponseBilinearForm
import Laplace.Multi.FacetFisherAccess
import Laplace.Multi.FisherVariational
import Laplace.Multi.NormalGeometry
import Laplace.Multi.NormalCone

/-!
# Saturation from an affinely spanning feature family

`ResponseSimplexCurvature` derived constant Fisher curvature `¼` from the abstract saturation
hypothesis (centred scores closed under products). Here saturation is derived from the natural
expressivity hypothesis on the observables: **every bounded function is affine in the features**,
`h = ⟨b, S⟩ + k` (`ν`-a.e.) for some ambient coefficient vector `b` and constant `k`
(`SpansAffine`). This is the situation of the full simplex of laws on a finite set whose feature
vectors form an affine basis (then it holds pointwise, `spansAffine_of_forall`), but it needs no
finiteness.

The proof avoids any orthogonal decomposition of the ambient coefficient space: the coefficient of
a product of scores is obtained by **regression on the scores** (the inverse Fisher transport of the
covariance vector, which lies in `W` by `covVec_mem_dirSpan`), and the residual, being affine in the
features and uncorrelated with every score, has vanishing variance and is therefore almost surely
constant (`ae_eq_integral_of_lawCov_self_eq_zero`).

* `saturatedAt_of_spansAffine`: `SpansAffine S ν → SaturatedAt S ν θ` for every `θ`.
* `fisherSectional_of_spansAffine`: an affinely spanning family has Fisher sectional curvature `¼`
  on every nondegenerate plane; the finite affine-basis simplex is the model case.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Aux

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]

/-- A bounded function with vanishing variance is almost surely its mean. -/
theorem ae_eq_integral_of_lawCov_self_eq_zero {g : X → ℝ} (hg : Bdd g) (h : lawCov P g g = 0) :
    g =ᵐ[P] fun _ ↦ ∫ y, g y ∂P := by
  rw [lawCov_self_eq_integral_sq P hg] at h
  have hint : Integrable (fun x ↦ (g x - ∫ y, g y ∂P) * (g x - ∫ y, g y ∂P)) P :=
    integrable_of_bdd_prob P ((hg.sub (Bdd.const _)).mul (hg.sub (Bdd.const _)))
  have h0 := (integral_eq_zero_iff_of_nonneg (fun x ↦ mul_self_nonneg _) hint).mp h
  filter_upwards [h0] with x hx
  simp only [Pi.zero_apply, mul_self_eq_zero, sub_eq_zero] at hx
  exact hx

omit [MeasurableSpace X] [IsProbabilityMeasure P] in
/-- The pairing is positive definite. -/
theorem eq_zero_of_dotJ_self_eq_zero {J : Type*} [Fintype J] {a : J → ℝ} (h : dotJ a a = 0) :
    a = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_self_nonneg (a i)).mp h
  funext i
  exact mul_self_eq_zero.mp (this i (Finset.mem_univ i))

end Aux

section Saturation

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- **Affine spanning**: every bounded function is `ν`-a.e. an affine function of the features. -/
def SpansAffine : Prop :=
  ∀ h : X → ℝ, Bdd h → ∃ (b : J → ℝ) (k : ℝ), h =ᵐ[ν] fun x ↦ dirLoss S b x + k

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- Pointwise affine spanning (the finite affine-basis simplex) gives `SpansAffine`. -/
theorem spansAffine_of_forall
    (hspan : ∀ h : X → ℝ, ∃ (b : J → ℝ) (k : ℝ), ∀ x, h x = dirLoss S b x + k) :
    SpansAffine S ν := fun h _ ↦
  let ⟨b, k, hbk⟩ := hspan h
  ⟨b, k, ae_of_all _ hbk⟩

/-- **Affine spanning implies saturation at every `θ`**: the product of two centred scores is,
after centring, the score of the regression coefficient `c = A_θ⁻¹(−Cov_θ(S, f_u f_v))`. -/
theorem saturatedAt_of_spansAffine (hspan : SpansAffine S ν) (θ : 𝕍) : SaturatedAt S ν θ := by
  intro u v
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hPν : Pfam (θ : J → ℝ) ≪ ν := withDensity_absolutelyContinuous _ _
  set h : X → ℝ := fun x ↦ modelScore S ν θ u x * modelScore S ν θ v x with hh
  have hb : Bdd h := (bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)
  -- the covariance vector of `h` lies in `W`; its inverse Fisher transport is the coefficient
  have hcv : (fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) h) ∈ 𝕍 :=
    covVec_mem_dirSpan hS ν (Pfam (θ : J → ℝ)) hPν hb
  have hcvn : -(fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) h) ∈ 𝕍 := Submodule.neg_mem _ hcv
  set c : 𝕍 := (CDE θ).symm ⟨-(fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) h), hcvn⟩ with hc
  refine ⟨c, ?_⟩
  -- (a) `G(w, c) = Cov(⟨w,S⟩, h)`
  have hGc : ∀ w : 𝕍, G θ w c = lawCov (Pfam (θ : J → ℝ)) (dirLoss S (w : J → ℝ)) h := by
    intro w
    rw [hc, fisherInner_chartDerivEquiv_symm hS ν θ w hcvn,
      lawCov_dirLoss_left hS (Pfam (θ : J → ℝ)) _ _ hb]
    simp only [dotJ, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg]
  -- (b) the affine representation of `h`, transported to `P_θ`
  obtain ⟨b, k, hbk⟩ := hspan h hb
  have hbkP : h =ᵐ[Pfam (θ : J → ℝ)] fun x ↦ dirLoss S b x + k := hPν.ae_eq hbk
  set d : J → ℝ := b - (c : J → ℝ) with hd
  set m : ℝ := ∫ y, dirLoss S (c : J → ℝ) y ∂Pfam (θ : J → ℝ) with hm
  have hrep : (fun x ↦ h x - modelScore S ν θ c x) =ᵐ[Pfam (θ : J → ℝ)]
      fun x ↦ dirLoss S d x + (k + m) := by
    filter_upwards [hbkP] with x hx
    simp only [hx, modelScore, hd, dirLoss_sub', ← hm]
    ring
  -- (c) the residual direction `d` is uncorrelated with every score
  have hcov0 : ∀ w : 𝕍, lawCov (Pfam (θ : J → ℝ)) (dirLoss S (w : J → ℝ)) (dirLoss S d) = 0 := by
    intro w
    have e1 := lawCov_congr_ae (Pfam (θ : J → ℝ)) (ae_eq_refl (dirLoss S (w : J → ℝ))) hrep
    rw [lawCov_add_right_eq _ (bdd_dirLoss hS d) (Bdd.const _) (bdd_dirLoss hS _),
      lawCov_comm _ _ (fun _ ↦ k + m), lawCov_const_left_eq_zero, add_zero] at e1
    rw [← e1, lawCov_comm, lawCov_sub_left_eq _ hb (bdd_modelScore hS ν θ c) (bdd_dirLoss hS _),
      lawCov_comm _ h, ← hGc w]
    have e2 : lawCov (Pfam (θ : J → ℝ)) (modelScore S ν θ c) (dirLoss S (w : J → ℝ)) = G θ w c := by
      rw [fisherInner_comm hS ν]
      unfold fisherInner modelScore
      rw [lawCov_sub_left_eq _ (bdd_dirLoss hS _) (Bdd.const _) (bdd_dirLoss hS _),
        lawCov_const_left_eq_zero, sub_zero]
    rw [e2, sub_self]
  -- (d) hence the covariance vector of `⟨d,S⟩` vanishes
  have hcv' : (fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) (dirLoss S d)) ∈ 𝕍 :=
    covVec_mem_dirSpan hS ν (Pfam (θ : J → ℝ)) hPν (bdd_dirLoss hS d)
  have hdot : ∀ w : 𝕍,
      dotJ (w : J → ℝ) (fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) (dirLoss S d)) = 0 := by
    intro w
    have := hcov0 w
    rw [lawCov_dirLoss_left hS (Pfam (θ : J → ℝ)) _ _ (bdd_dirLoss hS d)] at this
    exact this
  have hcv0 : (fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) (dirLoss S d)) = 0 :=
    eq_zero_of_dotJ_self_eq_zero (hdot ⟨_, hcv'⟩)
  have hcv0' : ∀ i, lawCov (Pfam (θ : J → ℝ)) (S i) (dirLoss S d) = 0 := fun i ↦ by
    have := congrFun hcv0 i
    simpa using this
  -- (e) so `⟨d,S⟩` has zero variance and is a.s. constant
  have hvar : lawCov (Pfam (θ : J → ℝ)) (dirLoss S d) (dirLoss S d) = 0 := by
    rw [lawCov_dirLoss_left hS (Pfam (θ : J → ℝ)) _ _ (bdd_dirLoss hS d)]
    simp [hcv0']
  have hconst := ae_eq_integral_of_lawCov_self_eq_zero (Pfam (θ : J → ℝ)) (bdd_dirLoss hS d) hvar
  -- (f) expectations
  have hEh : ∫ x, h x ∂Pfam (θ : J → ℝ) = G θ u v :=
    (fisherInner_eq_integral_modelScore hS ν θ u v).symm
  have hE1 : ∫ x, (h x - modelScore S ν θ c x) ∂Pfam (θ : J → ℝ) = ∫ x, h x ∂Pfam (θ : J → ℝ) := by
    rw [integral_sub (integrable_of_bdd_prob _ hb)
      (integrable_of_bdd_prob _ (bdd_modelScore hS ν θ c)), integral_modelScore hS ν, sub_zero]
  have hE2 : ∫ x, (h x - modelScore S ν θ c x) ∂Pfam (θ : J → ℝ) =
      (∫ x, dirLoss S d x ∂Pfam (θ : J → ℝ)) + (k + m) := by
    rw [integral_congr_ae hrep, integral_add (integrable_of_bdd_prob _ (bdd_dirLoss hS d))
      (integrable_const _), integral_const, probReal_univ, one_smul]
  filter_upwards [hrep, hconst] with x hx hx'
  rw [← hEh, ← hE1, hE2]
  linarith

/-- **Affinely spanning families are round**: Fisher sectional curvature `¼` on every nondegenerate
plane. The finite simplex with an affine basis of features is the model case. -/
theorem fisherSectional_of_spansAffine (hspan : SpansAffine S ν) (θ u v : 𝕍)
    (hden : 0 < G θ u u * G θ v v - G θ u v ^ 2) :
    fisherSectional hS ν θ u v = 1 / 4 :=
  fisherSectional_of_saturated hS ν θ (saturatedAt_of_spansAffine hS ν hspan θ) u v hden

/-- The constant-curvature tensor of an affinely spanning family. -/
theorem fisherInner_alphaCurvature_of_spansAffine (hspan : SpansAffine S ν) (θ : 𝕍) (α : ℝ)
    (u v w x : 𝕍) :
    G θ (alphaCurvature hS ν α θ u v w) x =
      ((1 - α ^ 2) / 4) * (G θ u x * G θ v w - G θ v x * G θ u w) :=
  fisherInner_alphaCurvature_of_saturated hS ν θ (saturatedAt_of_spansAffine hS ν hspan θ) α u v w x

end Saturation

end Laplace.Multi
