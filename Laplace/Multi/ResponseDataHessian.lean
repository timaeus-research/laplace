/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponsePullbackForm
import Laplace.Multi.CovarianceFrechet
import Laplace.Multi.CubicResponse
import Laplace.Multi.ResponseSusceptibility
import Laplace.Multi.CanonicalDataJourney

/-!
# The Hessian of the response map in the data direction

The first-order theory (`ResponsePullbackForm`) says that along a bounded data journey
`ρ_t = ν.tilted (g + t k)` the response `Φ(g + t k) = θ(E_{ρ_t} S)` moves with velocity
`DΦ_g[k] = (Dm(Φ(g)))⁻¹ Cov_{ρ_g}(S, k)`: the moment forcing transported through the inverse chart
derivative. This module differentiates once more.

Two `W`-valued third cumulants enter:

* the **data cumulant** `B_g(k,ℓ) = Cov_{ρ_g}(S, (k − E k)(ℓ − E ℓ))`, whose coordinates are the
  third central moments `κ_{ρ_g}(S_j, k, ℓ)` (`dataThird`, `dataThird_apply`), and which is the
  derivative of the forcing along the journey (`hasDerivAt_forcing_add`);
* the **model cumulant** `T_θ(v, w)`, the third-cumulant operator of `CovarianceFrechet` with
  coordinates `κ_{P_θ}(S_j, ⟨v,S⟩, ⟨w,S⟩)` (`thirdOp_apply_apply`), the derivative of the chart
  derivative.

**The response Hessian** is
`H_g(k,ℓ) = (Dm(Φ(g)))⁻¹ (B_g(k,ℓ) − T_{Φ(g)}(DΦ_g[k], DΦ_g[ℓ]))` (`responseHess`), and the main
theorem `hasDerivAt_responseVel_add` says that the velocity field `t ↦ DΦ_{g+tk}[ℓ]` is
differentiable with derivative `H_{g+tk}(k, ℓ)`; with `hasDerivAt_responseOf_add` this is the second
derivative of the response curve. The Hessian is symmetric (`responseHess_symm`) — a cumulant
symmetry, not a Schwarz theorem. Note the sign convention `P_θ = ν.tilted(−⟨θ,S⟩)`: the inverse
chart derivative is minus the inverse covariance operator, so in covariance form `H = C⁻¹(T − B)`.

The exponential journey `ν.tilted (t h)` is the case `g = 0` (`hasDerivAt_responseVel_exp`): its
response is exponentially straight to second order exactly when the data cumulant `B_{th}(h,h)`
equals the model cumulant on the matched velocity.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Bridge

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The centred product `(k − E_ρ k)(ℓ − E_ρ ℓ)`. -/
noncomputable def centredProd (ρ : Measure X) (k ℓ : X → ℝ) : X → ℝ :=
  fun x ↦ (k x - ∫ y, k y ∂ρ) * (ℓ x - ∫ y, ℓ y ∂ρ)

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem bdd_centredProd (ρ : Measure X) {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    Bdd (centredProd ρ k ℓ) :=
  (hk.sub (Bdd.const _)).mul (hℓ.sub (Bdd.const _))

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem centredProd_comm (ρ : Measure X) (k ℓ : X → ℝ) :
    centredProd ρ k ℓ = centredProd ρ ℓ k := by
  funext x
  simp only [centredProd]
  ring

/-- **The data third-cumulant vector** `B_g(k,ℓ) = Cov_{ρ_g}(S, (k − Ek)(ℓ − Eℓ)) ∈ W`. -/
noncomputable def dataThird {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ) : 𝕍 :=
  ⟨forcing S ν g (centredProd (ν.tilted g) k ℓ),
    forcing_mem_dirSpan hS ν hg (bdd_centredProd _ hk hℓ)⟩

/-- The coordinates of the data cumulant are third central moments:
`B_g(k,ℓ)_j = κ_{ρ_g}(S_j,k,ℓ)`. -/
theorem dataThird_apply {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ) (j : J) :
    (dataThird hS ν hg hk hℓ : J → ℝ) j = thirdCentral (ν.tilted g) (S j) k ℓ := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  change lawCov (ν.tilted g) (S j) (centredProd (ν.tilted g) k ℓ) = _
  simp only [lawCov, thirdCentral, centredProd]
  have hP : Integrable (fun x ↦ S j x * ((k x - ∫ y, k y ∂ν.tilted g) *
      (ℓ x - ∫ y, ℓ y ∂ν.tilted g))) (ν.tilted g) :=
    integrable_of_bdd_prob _ ((hS j).mul (bdd_centredProd (ν.tilted g) hk hℓ))
  have hP' : Integrable (fun x ↦ (∫ y, S j y ∂ν.tilted g) * ((k x - ∫ y, k y ∂ν.tilted g) *
      (ℓ x - ∫ y, ℓ y ∂ν.tilted g))) (ν.tilted g) :=
    (integrable_of_bdd_prob _ (bdd_centredProd (ν.tilted g) hk hℓ)).const_mul _
  rw [← integral_const_mul, ← integral_sub hP hP']
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- The data cumulant is symmetric. -/
theorem dataThird_symm {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ) :
    dataThird hS ν hg hk hℓ = dataThird hS ν hg hℓ hk := by
  apply Subtype.ext
  funext j
  rw [dataThird_apply, dataThird_apply, thirdCentral_comm₂₃]

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- Rebasing a bounded tilt: `ν.tilted (g + t k) = (ν.tilted g).tilted (t k)`. -/
theorem tilted_add_mul {g : X → ℝ} (hg : Bdd g) (k : X → ℝ) (t : ℝ) :
    ν.tilted (fun x ↦ g x + t * k x) = (ν.tilted g).tilted (fun x ↦ t * k x) := by
  rw [tilted_tilted (integrable_exp_of_bdd ν hg)]
  rfl

/-- **The forcing is differentiable along a data journey**, with derivative the data cumulant:
`d/dt Cov_{ρ_{g+tk}}(S, ℓ) = B_{g+tk}(k, ℓ)`. -/
theorem hasDerivAt_forcing_add {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ forcing S ν (fun x ↦ g x + t * k x) ℓ)
      (dataThird hS ν (hg.add (Bdd.const_mul t₀ hk)) hk hℓ : J → ℝ) t₀ := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  refine hasDerivAt_pi.2 fun j ↦ ?_
  rw [dataThird_apply]
  have h := hasDerivAt_lawCov_tilted (ν.tilted g) (hS j) hℓ hk t₀
  rw [← tilted_add_mul ν hg k t₀, thirdCentral_comm₂₃] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
  simp only [forcing]
  rw [tilted_add_mul ν hg k t]

/-- The coordinates of the model cumulant operator: `T_θ(v,w)_j = κ_{P_θ}(S_j, ⟨w,S⟩, ⟨v,S⟩)`. -/
theorem thirdOp_apply_apply (θ v w : 𝕍) (j : J) :
    (thirdOp hS ν θ v w : J → ℝ) j =
      thirdCentral (Pfam θ) (S j) (dirLoss S (w : J → ℝ)) (dirLoss S (v : J → ℝ)) := by
  rw [thirdOp_coe_apply]
  rfl

/-- The model cumulant operator is symmetric. -/
theorem thirdOp_symm (θ v w : 𝕍) : thirdOp hS ν θ v w = thirdOp hS ν θ w v := by
  apply Subtype.ext
  funext j
  rw [thirdOp_apply_apply, thirdOp_apply_apply, thirdCentral_comm₂₃]

end Bridge

section Hessian

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The response Hessian** `H_g(k,ℓ) = (Dm(Φ(g)))⁻¹ (B_g(k,ℓ) − T_{Φ(g)}(DΦ_g[k], DΦ_g[ℓ]))`. -/
noncomputable def responseHess {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ) : 𝕍 :=
  (CDE (responseOf hS ν g)).symm
    (dataThird hS ν hg hk hℓ -
      thirdOp hS ν (responseOf hS ν g) (responseVel hS ν hg hk) (responseVel hS ν hg hℓ))

/-- **The response Hessian is symmetric.** -/
theorem responseHess_symm {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ) :
    responseHess hS ν hg hk hℓ = responseHess hS ν hg hℓ hk := by
  unfold responseHess
  rw [dataThird_symm, thirdOp_symm]

variable (S) in
/-- The data means along the journey `g + t k`. -/
noncomputable def addMean (g k : X → ℝ) (t : ℝ) : J → ℝ :=
  fun i ↦ ∫ x, S i x ∂ν.tilted (fun x ↦ g x + t * k x)

theorem responseOf_add_eq (g k : X → ℝ) (t : ℝ) :
    responseOf hS ν (fun x ↦ g x + t * k x) = θr (addMean S ν g k t) := rfl

theorem responseVel_add_eq {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ) (t : ℝ) :
    responseVel hS ν (hg.add (Bdd.const_mul t hk)) hℓ =
      (CDE (θr (addMean S ν g k t))).symm ⟨forcing S ν (fun x ↦ g x + t * k x) ℓ,
        forcing_mem_dirSpan hS ν (hg.add (Bdd.const_mul t hk)) hℓ⟩ := rfl

/-- The Hessian depends only on the data law. -/
theorem responseHess_congr {g g' k ℓ : X → ℝ} (hg : Bdd g) (hg' : Bdd g') (hk : Bdd k)
    (hℓ : Bdd ℓ) (eg : g = g') : responseHess hS ν hg hk hℓ = responseHess hS ν hg' hk hℓ := by
  subst eg
  rfl

omit [Fintype J] [Nonempty J] in
theorem hasDerivAt_addMean {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) (t₀ : ℝ) :
    HasDerivAt (addMean S ν g k) (forcing S ν (fun x ↦ g x + t₀ * k x) k) t₀ := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  refine hasDerivAt_pi.2 fun i ↦ ?_
  have h := hasDerivAt_integral_tilted (ν.tilted g) hk (hS i) t₀
  simp_rw [← tilted_add_mul ν hg k] at h
  exact h

set_option linter.unusedFintypeInType false in
omit [Nonempty J] in
theorem addMean_mem_intrinsicInterior {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) (t : ℝ) :
    addMean S ν g k t ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
  mean_tilted_mem_intrinsicInterior hS ν (hg.add (Bdd.const_mul t hk))

/-- **The response is differentiable along a data journey** with velocity the response
velocity: `d/dt Φ(g + t k) = DΦ_{g+tk}[k]`. -/
theorem hasDerivAt_responseOf_add {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseOf hS ν (fun x ↦ g x + t * k x))
      (responseVel hS ν (hg.add (Bdd.const_mul t₀ hk)) hk) t₀ := by
  have hrel := addMean_mem_intrinsicInterior hS ν hg hk t₀
  have hstrict := hasStrictFDerivAt_responseTheta_add hS ν hrel
  have hmemz : ∀ t, addMean S ν g k t - addMean S ν g k t₀ ∈ 𝕍 := fun t ↦
    sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hrel)
      (intrinsicInterior_subset (addMean_mem_intrinsicInterior hS ν hg hk t))
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → 𝕍,
      z = fun t ↦ ⟨addMean S ν g k t - addMean S ν g k t₀, hmemz t⟩ := ⟨_, rfl⟩
  have hz : HasDerivAt z ⟨forcing S ν (fun x ↦ g x + t₀ * k x) k,
      forcing_mem_dirSpan hS ν (hg.add (Bdd.const_mul t₀ hk)) hk⟩ t₀ := by
    rw [hzdef]
    exact hasDerivAt_subtype_of_hasDerivAt _ ((hasDerivAt_addMean hS ν hg hk t₀).sub_const _)
  have hz0 : z t₀ = 0 := by
    rw [hzdef]
    exact Subtype.ext (sub_self _)
  have hF : HasFDerivAt (fun w : 𝕍 ↦ θr (addMean S ν g k t₀ + w))
      ((CDE (θr (addMean S ν g k t₀))).symm : 𝕍 →L[ℝ] 𝕍) (z t₀) := by
    rw [hz0]
    exact hstrict.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt t₀ hz
  refine (hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · change θr (addMean S ν g k t) = θr (addMean S ν g k t₀ + (z t : J → ℝ))
    rw [hzdef]
    change θr (addMean S ν g k t) =
      θr (addMean S ν g k t₀ + (addMean S ν g k t - addMean S ν g k t₀))
    rw [add_sub_cancel]
  · rfl

/-- **THE RESPONSE HESSIAN THEOREM**: the velocity field `t ↦ DΦ_{g+tk}[ℓ]` along a data journey is
differentiable, with derivative the response Hessian `H_{g+tk}(k, ℓ)`. -/
theorem hasDerivAt_responseVel_add {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ)
    (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseVel hS ν (hg.add (Bdd.const_mul t hk)) hℓ)
      (responseHess hS ν (hg.add (Bdd.const_mul t₀ hk)) hk hℓ) t₀ := by
  have hrel := addMean_mem_intrinsicInterior hS ν hg hk t₀
  have hmemz : ∀ t, addMean S ν g k t - addMean S ν g k t₀ ∈ 𝕍 := fun t ↦
    sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hrel)
      (intrinsicInterior_subset (addMean_mem_intrinsicInterior hS ν hg hk t))
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → 𝕍,
      z = fun t ↦ ⟨addMean S ν g k t - addMean S ν g k t₀, hmemz t⟩ := ⟨_, rfl⟩
  have hz : HasDerivAt z ⟨forcing S ν (fun x ↦ g x + t₀ * k x) k,
      forcing_mem_dirSpan hS ν (hg.add (Bdd.const_mul t₀ hk)) hk⟩ t₀ := by
    rw [hzdef]
    exact hasDerivAt_subtype_of_hasDerivAt _ ((hasDerivAt_addMean hS ν hg hk t₀).sub_const _)
  have hz0 : z t₀ = 0 := by
    rw [hzdef]
    exact Subtype.ext (sub_self _)
  -- the inverse chart derivative along the journey
  have hinv0 := hasFDerivAt_inverse_response hS ν hrel
  rw [← hz0] at hinv0
  have hinv := hinv0.comp_hasDerivAt t₀ hz
  -- the forcing along the journey
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → 𝕍, F = fun t ↦
      ⟨forcing S ν (fun x ↦ g x + t * k x) ℓ,
        forcing_mem_dirSpan hS ν (hg.add (Bdd.const_mul t hk)) hℓ⟩ := ⟨_, rfl⟩
  have hF : HasDerivAt F (dataThird hS ν (hg.add (Bdd.const_mul t₀ hk)) hk hℓ) t₀ := by
    rw [hFdef]
    exact hasDerivAt_subtype_of_hasDerivAt _ (hasDerivAt_forcing_add hS ν hg hk hℓ t₀)
  have h := hinv.clm_apply hF
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · change responseVel hS ν (hg.add (Bdd.const_mul t hk)) hℓ =
      (CDE (θr (addMean S ν g k t₀ + (z t : J → ℝ)))).symm (F t)
    rw [hzdef, hFdef]
    change responseVel hS ν (hg.add (Bdd.const_mul t hk)) hℓ =
      (CDE (θr (addMean S ν g k t₀ + (addMean S ν g k t - addMean S ν g k t₀)))).symm
        ⟨forcing S ν (fun x ↦ g x + t * k x) ℓ, _⟩
    simp only [add_sub_cancel]
    rfl
  · simp only [Function.comp_def, hz0, Submodule.coe_zero, add_zero, hFdef]
    rw [← ContinuousLinearMap.flip_apply, inverse_response_deriv_apply, responseHess, map_sub,
      responseOf_add_eq hS ν g k t₀, responseVel_add_eq hS ν hg hk hk t₀,
      responseVel_add_eq hS ν hg hk hℓ t₀, sub_eq_neg_add]
    rfl

/-- **The second derivative of the response curve** `t ↦ Φ(g + t k)` is `H_{g+tk}(k, k)`. -/
theorem hasDerivAt_responseVel_add_self {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseVel hS ν (hg.add (Bdd.const_mul t hk)) hk)
      (responseHess hS ν (hg.add (Bdd.const_mul t₀ hk)) hk hk) t₀ :=
  hasDerivAt_responseVel_add hS ν hg hk hk t₀

/-- **The exponential journey** `ρ_t = ν.tilted (t h)`: the velocity field `t ↦ DΦ_{th}[h]` has
derivative `H_{th}(h,h) = (Dm)⁻¹(B_{th}(h,h) − T_{Φ(th)}(v_t, v_t))`; the response is exponentially
straight to second order exactly when the data and model cumulants agree on the matched velocity. -/
theorem hasDerivAt_responseVel_exp {h : X → ℝ} (hh : Bdd h) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ responseVel hS ν (Bdd.const_mul t hh) hh)
      (responseHess hS ν (Bdd.const_mul t₀ hh) hh hh) t₀ := by
  have h0 := hasDerivAt_responseVel_add hS ν (Bdd.const (0 : ℝ)) hh hh t₀
  have e : ∀ t : ℝ, (fun x ↦ (fun _ : X ↦ (0 : ℝ)) x + t * h x) = fun x ↦ t * h x := fun t ↦ by
    funext x
    simp
  rw [responseHess_congr hS ν _ _ hh hh (e t₀)] at h0
  exact h0.congr_of_eventuallyEq (Eventually.of_forall fun t ↦
    (responseVel_congr hS ν _ _ _ _ (e t) rfl).symm)

end Hessian

end Laplace.Multi
