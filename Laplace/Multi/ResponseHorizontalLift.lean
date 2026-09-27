/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponsePullbackForm
import Laplace.Multi.FisherNormalisedSampling
import Laplace.Multi.BoundedTiltFisherComparison
import Laplace.Multi.FiniteResponse

/-!
# The horizontal lift: the response map is a covariance quotient

At a data law `ρ_g ∝ e^g ν` the differential of the response map, `k ↦ DΦ_g[k] ∈ W`, has kernel
the covariance-invisible directions (`ResponsePullbackForm`). This module shows it is **onto**
`W`, with a canonical right inverse: the **horizontal lift**

`hor_g(v) = ⟨C_{ρ_g}⁻¹ Dm(Φ(g)) v, S⟩`   (`horizontalLift`),

where `C_{ρ_g}` is the data covariance operator on `W` (positive definite for every bounded tilt,
`dataCovOp`, `dataCovEquiv`). Then

* `DΦ_g[hor_g(v)] = v` (`responseVel_horizontalLift`), so `DΦ_g` is surjective
  (`exists_responseVel_eq`), and the pull-back form of the lift is the Fisher form,
  `G^{resp}_g(hor_g v) = |v|²_{F,Φ(g)}` (`pullbackForm_horizontalLift`);
* the lift is the **variance-minimising** contrast with response velocity `v`
  (`lawCov_self_ge_horizontalLift`), with `Var_{ρ_g} hor_g(v) = ⟨C_{ρ_g}⁻¹ Dm v, Dm v⟩`
  (`lawCov_horizontalLift_self`);
* at a **matched** law `ρ_g = P_{Φ(g)}`: `hor_g(v) = −⟨v, S⟩` and `Var_{ρ_g} hor_g(v) = |v|²_F`
  (`horizontalLift_of_matched`, `lawCov_horizontalLift_self_of_matched`): the differential of the
  response map is a Riemannian submersion from scores (modulo constants) with the data Fisher
  metric onto `W` with the response Fisher metric.

Together with the kernel and the score decomposition of `ResponsePullbackForm` this is the
covariance-quotient theorem: response discards precisely the feature-invisible scores, and at
matched points the horizontal quotient is Fisher-isometric.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Ambient

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (S : J → X → ℝ)

/-- The ambient data covariance map `v ↦ (∑ᵢ vᵢ Cov_D(Sᵢ, S_a))_a`. -/
noncomputable def covLin (D : Measure X) : (J → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun v := fun a ↦ ∑ i, v i * lawCov D (S i) (S a)
  map_add' v w := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem covLin_apply (D : Measure X) (v : J → ℝ) (a : J) :
    covLin S D v a = ∑ i, v i * lawCov D (S i) (S a) := rfl

end Ambient

section Lift

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g : X → ℝ} (hg : Bdd g)
include hS hg

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The ambient Jacobian of the mean map. -/
local notation "Dm" => meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The response of the data law. -/
local notation "Φg" => responseOf hS ν g

omit [Nonempty X] [Nonempty J] in
theorem covLin_eq_forcing (v : J → ℝ) :
    covLin S (ν.tilted g) v = forcing S ν g (dirLoss S v) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  funext a
  rw [covLin_apply, forcing, lawCov_comm, lawCov_dirLoss_left hS _ v (S a) (hS a)]

theorem covLin_mem_dirSpan (v : J → ℝ) : covLin S (ν.tilted g) v ∈ 𝕍 := by
  rw [covLin_eq_forcing hS ν hg]
  exact forcing_mem_dirSpan hS ν hg (bdd_dirLoss hS v)

/-- The data covariance operator on the direction space: `w ↦ Cov_{ρ_g}(S, ⟨w,S⟩)`. -/
noncomputable def dataCovOp : 𝕍 →ₗ[ℝ] 𝕍 :=
  ((covLin S (ν.tilted g)).comp (𝕍).subtype).codRestrict 𝕍 fun w ↦ covLin_mem_dirSpan hS ν hg w

theorem dataCovOp_apply (w : 𝕍) :
    (dataCovOp hS ν hg w : J → ℝ) = forcing S ν g (dirLoss S (w : J → ℝ)) := by
  rw [← covLin_eq_forcing hS ν hg]
  rfl

/-- `⟨w, C_{ρ_g} w⟩ = Var_{ρ_g}⟨w,S⟩`. -/
theorem dotJ_dataCovOp (w : 𝕍) :
    dotJ (w : J → ℝ) (dataCovOp hS ν hg w : J → ℝ) =
      lawCov (ν.tilted g) (dirLoss S (w : J → ℝ)) (dirLoss S (w : J → ℝ)) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  rw [dataCovOp_apply, lawCov_dirLoss_left hS _ (w : J → ℝ) _ (bdd_dirLoss hS _)]
  rfl

/-- **The data variance of a nonzero visible contrast is positive** for every bounded tilt. -/
theorem lawCov_dirLoss_tilted_pos {w : 𝕍} (hw : w ≠ 0) :
    0 < lawCov (ν.tilted g) (dirLoss S (w : J → ℝ)) (dirLoss S (w : J → ℝ)) := by
  have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have h0 : 0 < lawCov ν (dirLoss S (w : J → ℝ)) (dirLoss S (w : J → ℝ)) := by
    have h1 := dotJ_chartDeriv_self_neg measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS 0 hw
    rw [dotJ_chartDeriv_eq_neg_lawCov hS ν 0 w w, show ((0 : 𝕍) : J → ℝ) = 0 from rfl,
      familyMeasure_zero_eq hS ν, neg_lt_zero] at h1
    exact h1
  obtain ⟨K, hK⟩ := hg.2
  have hle := lawCov_tilted_le_exp_osc (ν.tilted g) (bdd_neg hg) (lo := -K) (hi := K)
    (Eventually.of_forall fun x ↦ by linarith [(abs_le.1 (hK x)).2])
    (Eventually.of_forall fun x ↦ by linarith [(abs_le.1 (hK x)).1])
    (bdd_dirLoss hS (w : J → ℝ))
  have e : (ν.tilted g).tilted (fun x ↦ -g x) = ν := tilted_neg_same (integrable_exp_of_bdd ν hg)
  rw [e] at hle
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).1 (h0.trans_le hle)

theorem dataCovOp_injective : Function.Injective (dataCovOp hS ν hg) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  by_contra hne
  have h := dotJ_dataCovOp hS ν hg w
  rw [hw, Submodule.coe_zero, (isLinearMap_dotJ _).map_zero] at h
  exact (lawCov_dirLoss_tilted_pos hS ν hg hne).ne' h.symm

/-- The data covariance operator as a linear automorphism of the direction space. -/
noncomputable def dataCovEquiv : 𝕍 ≃ₗ[ℝ] 𝕍 :=
  LinearEquiv.ofInjectiveEndo (dataCovOp hS ν hg) (dataCovOp_injective hS ν hg)

theorem dataCovEquiv_apply (w : 𝕍) : dataCovEquiv hS ν hg w = dataCovOp hS ν hg w := rfl

/-- **The horizontal lift** `hor_g(v) = ⟨C_{ρ_g}⁻¹ Dm(Φ(g)) v, S⟩`. -/
noncomputable def horizontalLift (v : 𝕍) : X → ℝ :=
  dirLoss S (((dataCovEquiv hS ν hg).symm (CDE Φg v) : 𝕍) : J → ℝ)

theorem bdd_horizontalLift (v : 𝕍) : Bdd (horizontalLift hS ν hg v) := bdd_dirLoss hS _

/-- The forcing of the horizontal lift is the chart derivative of `v`. -/
theorem forcing_horizontalLift (v : 𝕍) :
    forcing S ν g (horizontalLift hS ν hg v) = (CDE Φg v : J → ℝ) := by
  rw [horizontalLift, ← dataCovOp_apply hS ν hg, ← dataCovEquiv_apply, LinearEquiv.apply_symm_apply]

/-- **The horizontal lift is a right inverse of the differential**: `DΦ_g[hor_g(v)] = v`. -/
theorem responseVel_horizontalLift (v : 𝕍) :
    responseVel hS ν hg (bdd_horizontalLift hS ν hg v) = v := by
  rw [responseVel]
  have e : (⟨forcing S ν g (horizontalLift hS ν hg v),
      forcing_mem_dirSpan hS ν hg (bdd_horizontalLift hS ν hg v)⟩ : 𝕍) = CDE Φg v :=
    Subtype.ext (forcing_horizontalLift hS ν hg v)
  rw [e, ContinuousLinearEquiv.symm_apply_apply]

/-- **The differential of the response map is onto the direction space.** -/
theorem exists_responseVel_eq (v : 𝕍) : ∃ k : X → ℝ, ∃ hk : Bdd k, responseVel hS ν hg hk = v :=
  ⟨_, _, responseVel_horizontalLift hS ν hg v⟩

/-- The pull-back form of the horizontal lift is the response Fisher form. -/
theorem pullbackForm_horizontalLift (v : 𝕍) :
    pullbackForm hS ν hg (bdd_horizontalLift hS ν hg v) = fisherVar S ν (Φg : J → ℝ) v := by
  rw [pullbackForm, responseVel_horizontalLift]

/-- **The data variance of the horizontal lift**: `Var_{ρ_g} hor_g(v) = ⟨C_{ρ_g}⁻¹ Dm v, Dm v⟩`. -/
theorem lawCov_horizontalLift_self (v : 𝕍) :
    lawCov (ν.tilted g) (horizontalLift hS ν hg v) (horizontalLift hS ν hg v) =
      dotJ (((dataCovEquiv hS ν hg).symm (CDE Φg v) : 𝕍) : J → ℝ) (CDE Φg v : J → ℝ) := by
  rw [horizontalLift, ← dotJ_dataCovOp hS ν hg, ← dataCovEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The forcing of a contrast with response velocity `v` is the chart derivative of `v`. -/
theorem forcing_eq_of_responseVel_eq {k : X → ℝ} (hk : Bdd k) {v : 𝕍}
    (hv : responseVel hS ν hg hk = v) : forcing S ν g k = (CDE Φg v : J → ℝ) := by
  rw [← chartDeriv_responseVel hS ν hg hk, hv]
  rfl

/-- **The horizontal lift minimises the data variance among contrasts with the same response
velocity.** -/
theorem lawCov_self_ge_horizontalLift {k : X → ℝ} (hk : Bdd k) {v : 𝕍}
    (hv : responseVel hS ν hg hk = v) :
    lawCov (ν.tilted g) (horizontalLift hS ν hg v) (horizontalLift hS ν hg v) ≤
      lawCov (ν.tilted g) k k := by
  have hP := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hhor := bdd_horizontalLift hS ν hg v
  have hres : Bdd fun x ↦ k x - horizontalLift hS ν hg v x := hk.sub hhor
  -- the residual is covariance-invisible
  have hinv : ∀ a, lawCov (ν.tilted g) (S a) (fun x ↦ k x - horizontalLift hS ν hg v x) = 0 := by
    intro a
    have h1 := congrFun (forcing_eq_of_responseVel_eq hS ν hg hk hv) a
    have h2 := congrFun (forcing_horizontalLift hS ν hg v) a
    simp only [forcing] at h1 h2
    rw [lawCov_comm, lawCov_sub_left_eq _ hk hhor (hS a), lawCov_comm _ k, lawCov_comm _ _ (S a),
      h1, h2, sub_self]
  have hc : lawCov (ν.tilted g) (horizontalLift hS ν hg v)
      (fun x ↦ k x - horizontalLift hS ν hg v x) = 0 := by
    have h := lawCov_dirLoss_left hS (ν.tilted g)
      (((dataCovEquiv hS ν hg).symm (CDE Φg v) : 𝕍) : J → ℝ)
      (fun x ↦ k x - horizontalLift hS ν hg v x) hres
    exact h.trans (Finset.sum_eq_zero fun a _ ↦ by rw [hinv a, mul_zero])
  have e : k = fun x ↦ horizontalLift hS ν hg v x + (k x - horizontalLift hS ν hg v x) := by
    funext x
    ring
  rw [e, lawCov_add_self _ hhor hres, hc]
  linarith [lawCov_self_nonneg (ν.tilted g) hres]

section Matched

/-- The matching condition: the data law is the reconstructed law at its own response. -/
local notation "IsMatched" =>
  ν.tilted g = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (responseOf hS ν g : J → ℝ)

/-- At a matched law the data covariance operator is minus the chart derivative. -/
theorem dataCovOp_eq_neg_of_matched (hm : IsMatched) (w : 𝕍) :
    dataCovOp hS ν hg w = -(CDE Φg w) := by
  classical
  apply Subtype.ext
  funext a
  rw [dataCovOp_apply, Submodule.coe_neg, Pi.neg_apply]
  have h := dotJ_chartDeriv_eq_neg_lawCov hS ν Φg (Pi.single a 1) w
  rw [dotJ_single_left, dirLoss_single_one, ← hm] at h
  have hc : ((CDE Φg w : 𝕍) : J → ℝ) = (chartDeriv measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS Φg w : J → ℝ) := rfl
  rw [hc, h, neg_neg]
  rfl

/-- At a matched law the horizontal lift is `−⟨v, S⟩`. -/
theorem horizontalLift_of_matched (hm : IsMatched) (v : 𝕍) :
    horizontalLift hS ν hg v = dirLoss S (-(v : J → ℝ)) := by
  have e : (dataCovEquiv hS ν hg).symm (CDE Φg v) = -v := by
    apply (dataCovEquiv hS ν hg).injective
    rw [LinearEquiv.apply_symm_apply, dataCovEquiv_apply, dataCovOp_eq_neg_of_matched hS ν hg hm,
      map_neg, neg_neg]
  rw [horizontalLift, e, Submodule.coe_neg]

/-- **The matched submersion**: at a matched law `Var_{ρ_g} hor_g(v) = |v|²_{F,Φ(g)}`. -/
theorem lawCov_horizontalLift_self_of_matched (hm : IsMatched) (v : 𝕍) :
    lawCov (ν.tilted g) (horizontalLift hS ν hg v) (horizontalLift hS ν hg v) =
      fisherVar S ν (Φg : J → ℝ) v := by
  have e : (dataCovEquiv hS ν hg).symm (CDE Φg v) = -v := by
    apply (dataCovEquiv hS ν hg).injective
    rw [LinearEquiv.apply_symm_apply, dataCovEquiv_apply, dataCovOp_eq_neg_of_matched hS ν hg hm,
      map_neg, neg_neg]
  rw [lawCov_horizontalLift_self, e, Submodule.coe_neg, fisherVar_eq_neg_dotJ hS ν]
  simp only [dotJ, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rfl

end Matched

end Lift

end Laplace.Multi
