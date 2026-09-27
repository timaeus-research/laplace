/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponsePullbackMetric
import Laplace.Multi.ResponseAtFeaturelessLaw
import Laplace.Multi.DataResponseMap
import Laplace.Multi.DataRayFacet
import Laplace.Multi.ResponsePathDifferential

/-!
# The pulled-back response form on the data manifold

For a data law `ρ_g ∝ e^g ν` (any bounded `g`) and a tangent observable `k`, the response
velocity is `DΦ_g[k] = (Dm(Φ(g)))⁻¹ b_g(k)` with the forcing `b_g(k) = Cov_{ρ_g}(S, k)`, and the
**pulled-back response form** is its Fisher energy

`G^{resp}_g(k) = |DΦ_g[k]|²_{F, Φ(g)} = b_g(k)ᵀ C_{Φ(g)}⁻¹ b_g(k) = Cov_{ρ_g}(⟨−DΦ_g[k], S⟩, k)`.

This module proves:

* the direction space is invariant under bounded tilts of the base law, so the forcing lies in
  it (`forcing_mem_dirSpan`);
* the form is nonnegative and **vanishes exactly on the covariance-invisible directions**
  `Cov_{ρ_g}(S,k) = 0` (`pullbackForm_eq_zero_iff`): a positive-semidefinite tensor whose kernel
  is what the statistics cannot see;
* **relative-covariance amplification**: if `Var_{ρ_g}⟨w,S⟩ ≤ κ Var_{P_{Φ(g)}}⟨w,S⟩` for all `w`,
  then `G^{resp}_g(k) ≤ κ Var_{ρ_g} k` (`pullbackForm_le_of_relCov`);
* **the matched orthogonal score decomposition**: if `ρ_g = P_{Φ(g)}`, with the visible part
  `k_vis = ⟨−DΦ_g[k], S⟩`,
  `Var_{ρ_g} k = G^{resp}_g(k) + Var_{ρ_g}(k − k_vis)` and `k − k_vis` is uncorrelated with every
  visible contrast (`lawCov_self_eq_pullbackForm_add`, `lawCov_residual_dirLoss_eq_zero`).

At a matched law, response formation is orthogonal projection of the data score onto the
structural tangent space: response Fisher energy is retained score energy, and the residual is
invisible energy. This is the infinitesimal mechanism of mapping responses across the data
manifold, in every tangent direction and at every data law.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Pullback

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

omit [Nonempty X] [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **The direction space is invariant under bounded tilts of the base law.** -/
theorem dirSpan_tilted_eq {g : X → ℝ} (hg : Bdd g) :
    dirSpan (ν.tilted g) (fun _ ↦ (1 : ℝ)) S = 𝕍 := by
  have h1 : ν.tilted g ≪ ν := tilted_absolutelyContinuous ν g
  have h2 : ν ≪ ν.tilted g := absolutelyContinuous_tilted (integrable_exp_of_bdd ν hg)
  change (affineSpan ℝ
      (closure (convexHull ℝ (essRange (ν.tilted g) (fun _ ↦ (1 : ℝ)) S)))).direction =
    (affineSpan ℝ (closure (convexHull ℝ (essRange ν (fun _ ↦ (1 : ℝ)) S)))).direction
  rw [essRange_eq_of_equiv hS ν (ν.tilted g) h1 h2]

variable (S) in
/-- The data forcing `b_g(k) = Cov_{ρ_g}(S, k)`. -/
noncomputable def forcing (g k : X → ℝ) : J → ℝ := fun i ↦ lawCov (ν.tilted g) (S i) k

set_option linter.unusedFintypeInType false in
/-- The forcing lies in the direction space. -/
theorem forcing_mem_dirSpan {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) : forcing S ν g k ∈ 𝕍 := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  rw [← dirSpan_tilted_eq hS ν hg]
  have h := dataCov_mem_dirSpan hS (ν.tilted g) hk 0
  rwa [dataCov_zero] at h

/-- The response of the data law `ρ_g`: `Φ(g) = θ(E_{ρ_g} S)`. -/
noncomputable def responseOf (g : X → ℝ) : 𝕍 := θr (fun i ↦ ∫ x, S i x ∂ν.tilted g)

/-- The response velocity `DΦ_g[k] = (Dm(Φ(g)))⁻¹ b_g(k)`. -/
noncomputable def responseVel {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) : 𝕍 :=
  (CDE (responseOf hS ν g)).symm ⟨forcing S ν g k, forcing_mem_dirSpan hS ν hg hk⟩

/-- The pulled-back response form `G^{resp}_g(k) = |DΦ_g[k]|²_F`. -/
noncomputable def pullbackForm {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) : ℝ :=
  fisherVar S ν (responseOf hS ν g : J → ℝ) (responseVel hS ν hg hk : J → ℝ)

/-- The chart derivative of the velocity is the forcing. -/
theorem chartDeriv_responseVel {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) :
    (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
      (responseOf hS ν g) (responseVel hS ν hg hk) : J → ℝ) = forcing S ν g k := by
  rw [responseVel, ← ContinuousLinearMap.coe_coe (chartDeriv measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (responseOf hS ν g)), ← coe_chartDerivEquiv,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **The pull-back form is the pairing of the velocity with the forcing**:
`G^{resp}_g(k) = −⟨DΦ_g[k], b_g(k)⟩ = bᵀC⁻¹b`. -/
theorem pullbackForm_eq_neg_dotJ {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) :
    pullbackForm hS ν hg hk = -dotJ (responseVel hS ν hg hk : J → ℝ) (forcing S ν g k) := by
  rw [pullbackForm, fisherVar_eq_neg_dotJ hS ν, ← chartDeriv_responseVel hS ν hg hk]
  rfl

/-- **The pull-back form is a covariance under the data law**:
`G^{resp}_g(k) = Cov_{ρ_g}(⟨−DΦ_g[k], S⟩, k)`. -/
theorem pullbackForm_eq_lawCov {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) :
    pullbackForm hS ν hg hk =
      lawCov (ν.tilted g) (dirLoss S (-(responseVel hS ν hg hk : J → ℝ))) k := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  rw [pullbackForm_eq_neg_dotJ hS ν hg hk]
  have e : dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) =
      fun x ↦ -dirLoss S (responseVel hS ν hg hk : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [e, lawCov_neg_left, lawCov_dirLoss_left hS _ _ k hk]
  rfl

theorem pullbackForm_nonneg {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) :
    0 ≤ pullbackForm hS ν hg hk :=
  fisherVar_nonneg hS ν _ _

/-- The Fisher form is positive on nonzero directions of the direction space. -/
theorem fisherVar_pos_of_ne_zero (θ : 𝕍) {v : 𝕍} (hv : v ≠ 0) :
    0 < fisherVar S ν (θ : J → ℝ) (v : J → ℝ) := by
  rw [fisherVar_eq_neg_dotJ hS ν, neg_pos]
  exact dotJ_chartDeriv_self_neg measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ hv

/-- **The kernel of the pull-back form is the covariance-invisible directions**:
`G^{resp}_g(k) = 0 ↔ Cov_{ρ_g}(S, k) = 0`. -/
theorem pullbackForm_eq_zero_iff {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) :
    pullbackForm hS ν hg hk = 0 ↔ forcing S ν g k = 0 := by
  constructor
  · intro h0
    by_contra hne
    have hv : responseVel hS ν hg hk ≠ 0 := fun hv ↦ by
      have := congrArg (CDE (responseOf hS ν g)) hv
      rw [responseVel, ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
      exact hne (congrArg Subtype.val this)
    exact (fisherVar_pos_of_ne_zero hS ν _ hv).ne' h0
  · intro h0
    rw [pullbackForm_eq_neg_dotJ hS ν hg hk, h0, (isLinearMap_dotJ _).map_zero, neg_zero]

/-- **Relative-covariance amplification**: if `Var_{ρ_g}⟨w,S⟩ ≤ κ Var_{P_{Φ(g)}}⟨w,S⟩` for all
`w`, then `G^{resp}_g(k) ≤ κ Var_{ρ_g} k`. -/
theorem pullbackForm_le_of_relCov {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ w : J → ℝ, lawCov (ν.tilted g) (dirLoss S w) (dirLoss S w) ≤
      κ * fisherVar S ν (responseOf hS ν g : J → ℝ) w) :
    pullbackForm hS ν hg hk ≤ κ * lawCov (ν.tilted g) k k := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  obtain ⟨w, hw⟩ : ∃ w : J → ℝ, w = (responseVel hS ν hg hk : J → ℝ) := ⟨_, rfl⟩
  have hX : pullbackForm hS ν hg hk = lawCov (ν.tilted g) (dirLoss S (-w)) k := by
    rw [pullbackForm_eq_lawCov hS ν hg hk, hw]
  have hF : pullbackForm hS ν hg hk = fisherVar S ν (responseOf hS ν g : J → ℝ) w := by
    rw [pullbackForm, hw]
  have hD : 0 ≤ lawCov (ν.tilted g) k k := lawCov_self_nonneg _ hk
  have hcs := lawCov_sq_le (ν.tilted g) (bdd_dirLoss hS (-w)) hk
  have hvar : lawCov (ν.tilted g) (dirLoss S (-w)) (dirLoss S (-w)) =
      lawCov (ν.tilted g) (dirLoss S w) (dirLoss S w) := by
    have e : dirLoss S (-w) = fun x ↦ -dirLoss S w x := funext fun x ↦ dirLoss_neg (S := S) _ x
    rw [e, lawCov_neg_left, lawCov_neg_right_eq, neg_neg]
  rw [hvar] at hcs
  have key : pullbackForm hS ν hg hk ^ 2 ≤
      κ * pullbackForm hS ν hg hk * lawCov (ν.tilted g) k k := by
    calc pullbackForm hS ν hg hk ^ 2 = lawCov (ν.tilted g) (dirLoss S (-w)) k ^ 2 := by rw [hX]
      _ ≤ lawCov (ν.tilted g) (dirLoss S w) (dirLoss S w) * lawCov (ν.tilted g) k k := hcs
      _ ≤ (κ * fisherVar S ν (responseOf hS ν g : J → ℝ) w) * lawCov (ν.tilted g) k k :=
          mul_le_mul_of_nonneg_right (hκ w) hD
      _ = κ * pullbackForm hS ν hg hk * lawCov (ν.tilted g) k k := by rw [hF]
  rcases (pullbackForm_nonneg hS ν hg hk).lt_or_eq with hpos | hzero
  · have key' : pullbackForm hS ν hg hk * pullbackForm hS ν hg hk ≤
        pullbackForm hS ν hg hk * (κ * lawCov (ν.tilted g) k k) := by
      rw [← sq]
      calc pullbackForm hS ν hg hk ^ 2 ≤ κ * pullbackForm hS ν hg hk * lawCov (ν.tilted g) k k :=
            key
        _ = pullbackForm hS ν hg hk * (κ * lawCov (ν.tilted g) k k) := by ring
    exact le_of_mul_le_mul_left key' hpos
  · rw [← hzero]
    exact mul_nonneg hκ0 hD

section Matched

variable {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k)
include hg hk

/-- The matching condition: the data law is the reconstructed law at its own response. -/
local notation "IsMatched" =>
  ν.tilted g = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (responseOf hS ν g : J → ℝ)

/-- **At a matched law the visible part `⟨−DΦ_g[k], S⟩` is the regression of `k` on the
statistics**: `Cov(⟨e,S⟩, k_vis) = Cov(⟨e,S⟩, k)` for every direction `e`. -/
theorem lawCov_dirLoss_visible (hm : IsMatched) (e : J → ℝ) :
    lawCov (ν.tilted g) (dirLoss S e) (dirLoss S (-(responseVel hS ν hg hk : J → ℝ))) =
      lawCov (ν.tilted g) (dirLoss S e) k := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hP := isProbabilityMeasure_family hS ν (responseOf hS ν g : J → ℝ)
  have h1 := dotJ_chartDeriv_eq_neg_lawCov hS ν (responseOf hS ν g) e (responseVel hS ν hg hk)
  rw [chartDeriv_responseVel hS ν hg hk] at h1
  have e1 : dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) =
      fun x ↦ -dirLoss S (responseVel hS ν hg hk : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [e1, lawCov_neg_right_eq, hm, ← h1, ← hm, lawCov_dirLoss_left hS _ e k hk]
  rfl

/-- **The matched orthogonal score decomposition**:
`Var_{ρ_g} k = G^{resp}_g(k) + Var_{ρ_g}(k − k_vis)`. -/
theorem lawCov_self_eq_pullbackForm_add (hm : IsMatched) :
    lawCov (ν.tilted g) k k = pullbackForm hS ν hg hk +
      lawCov (ν.tilted g) (fun x ↦ k x - dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) x)
        (fun x ↦ k x - dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) x) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hvis := bdd_dirLoss hS (-(responseVel hS ν hg hk : J → ℝ))
  have hvv := lawCov_dirLoss_visible hS ν hg hk hm (-(responseVel hS ν hg hk : J → ℝ))
  have hX := pullbackForm_eq_lawCov hS ν hg hk
  have hc := lawCov_comm (ν.tilted g) k (dirLoss S (-(responseVel hS ν hg hk : J → ℝ)))
  rw [lawCov_sub_self _ hk hvis, hvv, hX, hc]
  ring

/-- **The residual is invisible**: `Cov_{ρ_g}(k − k_vis, ⟨e,S⟩) = 0` for every direction `e`. -/
theorem lawCov_residual_dirLoss_eq_zero (hm : IsMatched) (e : J → ℝ) :
    lawCov (ν.tilted g) (fun x ↦ k x - dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) x)
      (dirLoss S e) = 0 := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  rw [lawCov_sub_left_eq _ hk (bdd_dirLoss hS _) (bdd_dirLoss hS e),
    lawCov_comm (ν.tilted g) (dirLoss S (-(responseVel hS ν hg hk : J → ℝ))) (dirLoss S e),
    lawCov_dirLoss_visible hS ν hg hk hm e, lawCov_comm (ν.tilted g) (dirLoss S e) k, sub_self]

/-- At a matched law the pull-back form is dominated by the data variance (contraction). -/
theorem pullbackForm_le_lawCov_self (hm : IsMatched) :
    pullbackForm hS ν hg hk ≤ lawCov (ν.tilted g) k k := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hvis := bdd_dirLoss hS (-(responseVel hS ν hg hk : J → ℝ))
  rw [lawCov_self_eq_pullbackForm_add hS ν hg hk hm]
  linarith [lawCov_self_nonneg (ν.tilted g) (hk.sub hvis)]

end Matched

end Pullback

end Laplace.Multi
