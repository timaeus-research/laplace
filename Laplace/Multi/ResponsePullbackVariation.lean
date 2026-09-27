/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDataHessian
import Laplace.Multi.ResponseBilinearForm
import Laplace.Multi.DataRayFacet
import Laplace.Multi.ObservableCurvature

/-!
# Variation of the pulled-back response form along a data journey

The bilinear response form `G_g(h,ℓ) = Cov_{P_{Φ(g)}}(⟨DΦ_g[h],S⟩, ⟨DΦ_g[ℓ],S⟩)` (the pull-back of
the Fisher form of the family by the response map, `ResponseBilinearForm`) is differentiated along
a data journey `g + t k`. Its derivative is a combination of three third cumulants (`pullbackVar`,
`hasDerivAt_pullbackBilin_add`):

`D_k G_g(h,ℓ) = κ_{P_{Φ(g)}}(L_{DΦ[ℓ]}, L_{DΦ[h]}, L_{DΦ[k]}) − κ_{ρ_g}(L_{DΦ[ℓ]}, k, h) −
κ_{ρ_g}(L_{DΦ[h]}, k, ℓ)`,

where `L_v = ⟨v,S⟩`. The proof is the product rule for `G = −⟨DΦ[h], b(ℓ)⟩` (velocity times
forcing), the response Hessian theorem for the velocity, the data cumulant for the forcing, and the
symmetry of the chart derivative under the pairing (`dotJ_chartDeriv_symm`,
`dotJ_symm_chartDeriv`), which turns `⟨A⁻¹ w, A v⟩` into `⟨w, v⟩`. The diagonal
(`hasDerivAt_pullbackForm_add`) gives the variation of the response speed² along the journey:
`κ_q(L_v,L_v,L_v) − 2 κ_ρ(L_v, k, k)` with `v = DΦ_g[k]`. These are third-cumulant variation
identities, not curvature theorems.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section DotDeriv

variable {J : Type*} [Fintype J]

/-- The product rule for the pairing. -/
theorem hasDerivAt_dotJ {a b : ℝ → J → ℝ} {a' b' : J → ℝ} {t : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s ↦ dotJ (a s) (b s)) (dotJ a' (b t) + dotJ (a t) b') t := by
  simp only [dotJ]
  rw [← Finset.sum_add_distrib]
  refine HasDerivAt.fun_sum fun i _ ↦ ?_
  exact (hasDerivAt_pi.1 ha i).mul (hasDerivAt_pi.1 hb i)

end DotDeriv

section Pairing

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The chart derivative is symmetric under the pairing**: `⟨u, A_θ v⟩ = ⟨A_θ u, v⟩`. -/
theorem dotJ_chartDeriv_symm (θ u v : 𝕍) :
    dotJ (u : J → ℝ) (CD θ v : J → ℝ) = dotJ (CD θ u : J → ℝ) (v : J → ℝ) := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  rw [dotJ_chartDeriv_eq_neg_lawCov hS ν, dotJ_comm', dotJ_chartDeriv_eq_neg_lawCov hS ν,
    lawCov_comm]

/-- `⟨A_θ⁻¹ w, A_θ v⟩ = ⟨w, v⟩`. -/
theorem dotJ_symm_chartDeriv (θ w v : 𝕍) :
    dotJ ((CDE θ).symm w : J → ℝ) (CD θ v : J → ℝ) = dotJ (w : J → ℝ) (v : J → ℝ) := by
  rw [dotJ_chartDeriv_symm hS ν]
  congr 1
  rw [← ContinuousLinearMap.coe_coe (CD θ), ← coe_chartDerivEquiv, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- Pairing with the data cumulant is a third cumulant of a visible contrast:
`⟨v, B_g(k,ℓ)⟩ = κ_{ρ_g}(⟨v,S⟩, k, ℓ)`. -/
theorem dotJ_dataThird (v : J → ℝ) {g k ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hℓ : Bdd ℓ) :
    dotJ v (dataThird hS ν hg hk hℓ : J → ℝ) = thirdCentral (ν.tilted g) (dirLoss S v) k ℓ := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  rw [thirdCentral_dirLoss_left _ hS v hk hℓ]
  simp only [dotJ]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [dataThird_apply]

/-- Pairing with the model cumulant: `⟨u, T_θ(v,w)⟩ = κ_{P_θ}(⟨u,S⟩, ⟨w,S⟩, ⟨v,S⟩)`. -/
theorem dotJ_thirdOp (u : J → ℝ) (θ v w : 𝕍) :
    dotJ u (thirdOp hS ν θ v w : J → ℝ) =
      thirdCentral (Pfam (θ : J → ℝ)) (dirLoss S u) (dirLoss S (w : J → ℝ))
        (dirLoss S (v : J → ℝ)) := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  rw [thirdCentral_dirLoss_left _ hS u (bdd_dirLoss hS _) (bdd_dirLoss hS _)]
  simp only [dotJ]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [thirdOp_apply_apply]

end Pairing

section Variation

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

/-- **The variation of the bilinear response form** in the data direction `k`:
`D_k G_g(h,ℓ) = κ_q(L_{DΦ[ℓ]}, L_{DΦ[h]}, L_{DΦ[k]}) − κ_ρ(L_{DΦ[ℓ]}, k, h)
  − κ_ρ(L_{DΦ[h]}, k, ℓ)`. -/
noncomputable def pullbackVar {g k h ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hh : Bdd h)
    (hℓ : Bdd ℓ) : ℝ :=
  thirdCentral (Pfam (responseOf hS ν g : J → ℝ))
      (dirLoss S (responseVel hS ν hg hℓ : J → ℝ)) (dirLoss S (responseVel hS ν hg hh : J → ℝ))
      (dirLoss S (responseVel hS ν hg hk : J → ℝ)) -
    thirdCentral (ν.tilted g) (dirLoss S (responseVel hS ν hg hℓ : J → ℝ)) k h -
    thirdCentral (ν.tilted g) (dirLoss S (responseVel hS ν hg hh : J → ℝ)) k ℓ

/-- The product-rule form of the variation. -/
theorem pullbackVar_eq {g k h ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hh : Bdd h) (hℓ : Bdd ℓ) :
    pullbackVar hS ν hg hk hh hℓ =
      -(dotJ (responseHess hS ν hg hk hh : J → ℝ) (forcing S ν g ℓ) +
        dotJ (responseVel hS ν hg hh : J → ℝ) (dataThird hS ν hg hk hℓ : J → ℝ)) := by
  rw [← chartDeriv_responseVel hS ν hg hℓ, responseHess, dotJ_symm_chartDeriv hS ν,
    Submodule.coe_sub, dotJ_sub_left, dotJ_comm', dotJ_dataThird hS ν, dotJ_comm',
    dotJ_thirdOp hS ν, dotJ_dataThird hS ν, pullbackVar]
  ring

/-- **THE PULL-BACK VARIATION THEOREM**: along the data journey `g + t k` the bilinear response form
`G_{g+tk}(h,ℓ)` is differentiable with derivative `pullbackVar`, a combination of three third
cumulants. -/
theorem hasDerivAt_pullbackBilin_add {g k h ℓ : X → ℝ} (hg : Bdd g) (hk : Bdd k) (hh : Bdd h)
    (hℓ : Bdd ℓ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ pullbackBilin hS ν (hg.add (Bdd.const_mul t hk)) hh hℓ)
      (pullbackVar hS ν (hg.add (Bdd.const_mul t₀ hk)) hk hh hℓ) t₀ := by
  have hV := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t₀
    (hasDerivAt_responseVel_add hS ν hg hk hh t₀)
  have hF := hasDerivAt_forcing_add hS ν hg hk hℓ t₀
  have h := (hasDerivAt_dotJ hV hF).neg
  rw [pullbackVar_eq]
  exact h

/-- **The variation of the response speed²** along the journey: with `v = DΦ_{g+tk}[k]`,
`d/dt G_{g+tk}(k,k) = κ_q(L_v,L_v,L_v) − 2 κ_ρ(L_v, k, k)`. -/
theorem hasDerivAt_pullbackForm_add {g k : X → ℝ} (hg : Bdd g) (hk : Bdd k) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ pullbackForm hS ν (hg.add (Bdd.const_mul t hk)) hk)
      (thirdCentral (Pfam (responseOf hS ν (fun x ↦ g x + t₀ * k x) : J → ℝ))
          (dirLoss S (responseVel hS ν (hg.add (Bdd.const_mul t₀ hk)) hk : J → ℝ))
          (dirLoss S (responseVel hS ν (hg.add (Bdd.const_mul t₀ hk)) hk : J → ℝ))
          (dirLoss S (responseVel hS ν (hg.add (Bdd.const_mul t₀ hk)) hk : J → ℝ)) -
        2 * thirdCentral (ν.tilted (fun x ↦ g x + t₀ * k x))
          (dirLoss S (responseVel hS ν (hg.add (Bdd.const_mul t₀ hk)) hk : J → ℝ)) k k) t₀ := by
  have h := hasDerivAt_pullbackBilin_add hS ν hg hk hk hk t₀
  simp only [pullbackBilin_self] at h
  refine h.congr_deriv ?_
  unfold pullbackVar
  ring

end Variation

end Laplace.Multi
