/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponsePullbackForm

/-!
# The pulled-back response form as a bilinear form

The pull-back form of `ResponsePullbackForm` is the diagonal of the **bilinear response form**

`G_g(k, ℓ) = −⟨DΦ_g[k], b_g(ℓ)⟩ = ⟨b_g(k), C_{Φ(g)}⁻¹ b_g(ℓ)⟩`
`= Cov_{P_{Φ(g)}}(⟨DΦ_g[k],S⟩, ⟨DΦ_g[ℓ],S⟩)`

(`pullbackBilin`, `pullbackBilin_eq_lawCov_family`), which is symmetric (`pullbackBilin_comm`),
bilinear (`pullbackBilin_add_right`, `pullbackBilin_const_mul_right`, and the left versions),
satisfies Cauchy–Schwarz against the diagonal (`pullbackBilin_sq_le`), and at a matched law
gives the **bilinear score decomposition**

`Cov_{ρ_g}(k, ℓ) = G_g(k, ℓ) + Cov_{ρ_g}(k − k_vis, ℓ − ℓ_vis)`   (`lawCov_eq_pullbackBilin_add`):

the data covariance of two contrasts is their response covariance plus the covariance of their
invisible parts. This is the Riemannian-submersion statement at the level of the metric tensors.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Cov

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]

/-- Left additivity of the covariance. -/
theorem lawCov_add_left_eq {f g k : X → ℝ} (hf : Bdd f) (hg : Bdd g) (hk : Bdd k) :
    lawCov ρ (fun x ↦ f x + g x) k = lawCov ρ f k + lawCov ρ g k := by
  have h := lawCov_sub_left_eq ρ hf (bdd_neg hg) hk
  rw [lawCov_neg_left] at h
  simpa [sub_neg_eq_add] using h

/-- Right additivity of the covariance. -/
theorem lawCov_add_right_eq {f g k : X → ℝ} (hf : Bdd f) (hg : Bdd g) (hk : Bdd k) :
    lawCov ρ k (fun x ↦ f x + g x) = lawCov ρ k f + lawCov ρ k g := by
  rw [lawCov_comm, lawCov_add_left_eq ρ hf hg hk, lawCov_comm ρ f, lawCov_comm ρ g]

omit [IsProbabilityMeasure ρ] in
/-- Left homogeneity of the covariance. -/
theorem lawCov_const_mul_left_eq (c : ℝ) (f k : X → ℝ) :
    lawCov ρ (fun x ↦ c * f x) k = c * lawCov ρ f k := by
  simp only [lawCov, mul_assoc, integral_const_mul]
  ring

end Cov

section Bilinear

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g : X → ℝ} (hg : Bdd g)
include hS hg

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The response of the data law. -/
local notation "Φg" => responseOf hS ν g

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- The forcing is additive. -/
theorem forcing_add {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    forcing S ν g (fun x ↦ k x + ℓ x) = forcing S ν g k + forcing S ν g ℓ := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  funext a
  simp only [forcing, Pi.add_apply]
  rw [lawCov_add_right_eq _ hk hℓ (hS a)]

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg in
/-- The forcing is homogeneous. -/
theorem forcing_const_mul (c : ℝ) (k : X → ℝ) :
    forcing S ν g (fun x ↦ c * k x) = c • forcing S ν g k := by
  funext a
  simp only [forcing, Pi.smul_apply, smul_eq_mul]
  rw [lawCov_comm, lawCov_const_mul_left_eq, lawCov_comm]

/-- The response velocity is additive. -/
theorem responseVel_add {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    responseVel hS ν hg (hk.add hℓ) = responseVel hS ν hg hk + responseVel hS ν hg hℓ := by
  rw [responseVel, responseVel, responseVel, ← map_add]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_add]
  exact forcing_add hS ν hg hk hℓ

/-- The response velocity is homogeneous. -/
theorem responseVel_const_mul {k : X → ℝ} (hk : Bdd k) (c : ℝ) :
    responseVel hS ν hg (hk.const_mul c) = c • responseVel hS ν hg hk := by
  rw [responseVel, responseVel, ← map_smul]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_smul]
  exact forcing_const_mul ν c k

/-- **The bilinear response form** `G_g(k, ℓ) = −⟨DΦ_g[k], b_g(ℓ)⟩`. -/
noncomputable def pullbackBilin {k ℓ : X → ℝ} (hk : Bdd k) (_hℓ : Bdd ℓ) : ℝ :=
  -dotJ (responseVel hS ν hg hk : J → ℝ) (forcing S ν g ℓ)

/-- The diagonal of the bilinear form is the pull-back form. -/
theorem pullbackBilin_self {k : X → ℝ} (hk : Bdd k) :
    pullbackBilin hS ν hg hk hk = pullbackForm hS ν hg hk :=
  (pullbackForm_eq_neg_dotJ hS ν hg hk).symm

/-- **The bilinear form is the response covariance of the velocities**:
`G_g(k,ℓ) = Cov_{P_{Φ(g)}}(⟨DΦ_g[k],S⟩, ⟨DΦ_g[ℓ],S⟩)`. -/
theorem pullbackBilin_eq_lawCov_family {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    pullbackBilin hS ν hg hk hℓ = lawCov (Pfam (Φg : J → ℝ))
      (dirLoss S (responseVel hS ν hg hk : J → ℝ))
      (dirLoss S (responseVel hS ν hg hℓ : J → ℝ)) := by
  rw [pullbackBilin, ← chartDeriv_responseVel hS ν hg hℓ, dotJ_chartDeriv_eq_neg_lawCov hS ν,
    neg_neg]

/-- The bilinear form is symmetric. -/
theorem pullbackBilin_comm {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    pullbackBilin hS ν hg hk hℓ = pullbackBilin hS ν hg hℓ hk := by
  have := isProbabilityMeasure_family hS ν (Φg : J → ℝ)
  rw [pullbackBilin_eq_lawCov_family, pullbackBilin_eq_lawCov_family, lawCov_comm]

/-- The bilinear form as a covariance under the data law:
`G_g(k,ℓ) = Cov_{ρ_g}(⟨−DΦ_g[k],S⟩, ℓ)`. -/
theorem pullbackBilin_eq_lawCov_data {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    pullbackBilin hS ν hg hk hℓ =
      lawCov (ν.tilted g) (dirLoss S (-(responseVel hS ν hg hk : J → ℝ))) ℓ := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have e : dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) =
      fun x ↦ -dirLoss S (responseVel hS ν hg hk : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [pullbackBilin, e, lawCov_neg_left, lawCov_dirLoss_left hS _ _ ℓ hℓ]
  rfl

theorem pullbackBilin_add_right {k ℓ ℓ' : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) (hℓ' : Bdd ℓ') :
    pullbackBilin hS ν hg hk (hℓ.add hℓ') =
      pullbackBilin hS ν hg hk hℓ + pullbackBilin hS ν hg hk hℓ' := by
  simp only [pullbackBilin, forcing_add hS ν hg hℓ hℓ', (isLinearMap_dotJ _).map_add]
  ring

theorem pullbackBilin_const_mul_right {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) (c : ℝ) :
    pullbackBilin hS ν hg hk (hℓ.const_mul c) = c * pullbackBilin hS ν hg hk hℓ := by
  simp only [pullbackBilin, forcing_const_mul ν c ℓ, (isLinearMap_dotJ _).map_smul, smul_eq_mul]
  ring

theorem pullbackBilin_add_left {k k' ℓ : X → ℝ} (hk : Bdd k) (hk' : Bdd k') (hℓ : Bdd ℓ) :
    pullbackBilin hS ν hg (hk.add hk') hℓ =
      pullbackBilin hS ν hg hk hℓ + pullbackBilin hS ν hg hk' hℓ := by
  rw [pullbackBilin_comm hS ν hg (hk.add hk') hℓ, pullbackBilin_add_right hS ν hg hℓ hk hk',
    pullbackBilin_comm hS ν hg hℓ hk, pullbackBilin_comm hS ν hg hℓ hk']

theorem pullbackBilin_const_mul_left {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) (c : ℝ) :
    pullbackBilin hS ν hg (hk.const_mul c) hℓ = c * pullbackBilin hS ν hg hk hℓ := by
  rw [pullbackBilin_comm hS ν hg (hk.const_mul c) hℓ, pullbackBilin_const_mul_right hS ν hg hℓ hk c,
    pullbackBilin_comm hS ν hg hℓ hk]

/-- **Cauchy–Schwarz for the response form**: `G_g(k,ℓ)² ≤ G_g(k,k) G_g(ℓ,ℓ)`. -/
theorem pullbackBilin_sq_le {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    pullbackBilin hS ν hg hk hℓ ^ 2 ≤ pullbackForm hS ν hg hk * pullbackForm hS ν hg hℓ := by
  have := isProbabilityMeasure_family hS ν (Φg : J → ℝ)
  rw [← pullbackBilin_self, ← pullbackBilin_self, pullbackBilin_eq_lawCov_family,
    pullbackBilin_eq_lawCov_family, pullbackBilin_eq_lawCov_family]
  exact lawCov_sq_le _ (bdd_dirLoss hS _) (bdd_dirLoss hS _)

section Matched

/-- The matching condition: the data law is the reconstructed law at its own response. -/
local notation "IsMatched" =>
  ν.tilted g = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (responseOf hS ν g : J → ℝ)

/-- At a matched law the covariance of the visible parts is the bilinear form. -/
theorem lawCov_visible_visible_of_matched (hm : IsMatched) {k ℓ : X → ℝ} (hk : Bdd k)
    (hℓ : Bdd ℓ) :
    lawCov (ν.tilted g) (dirLoss S (-(responseVel hS ν hg hk : J → ℝ)))
      (dirLoss S (-(responseVel hS ν hg hℓ : J → ℝ))) = pullbackBilin hS ν hg hk hℓ := by
  have ek : dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) =
      fun x ↦ -dirLoss S (responseVel hS ν hg hk : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  have eℓ : dirLoss S (-(responseVel hS ν hg hℓ : J → ℝ)) =
      fun x ↦ -dirLoss S (responseVel hS ν hg hℓ : J → ℝ) x :=
    funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [ek, eℓ, lawCov_neg_left, lawCov_neg_right_eq, neg_neg, hm,
    pullbackBilin_eq_lawCov_family hS ν hg hk hℓ]

/-- **The bilinear score decomposition at a matched law**:
`Cov_{ρ_g}(k, ℓ) = G_g(k, ℓ) + Cov_{ρ_g}(k − k_vis, ℓ − ℓ_vis)`. -/
theorem lawCov_eq_pullbackBilin_add (hm : IsMatched) {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    lawCov (ν.tilted g) k ℓ = pullbackBilin hS ν hg hk hℓ +
      lawCov (ν.tilted g) (fun x ↦ k x - dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) x)
        (fun x ↦ ℓ x - dirLoss S (-(responseVel hS ν hg hℓ : J → ℝ)) x) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hkv := bdd_dirLoss hS (-(responseVel hS ν hg hk : J → ℝ))
  have hℓv := bdd_dirLoss hS (-(responseVel hS ν hg hℓ : J → ℝ))
  have hkr : Bdd fun x ↦ k x - dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) x := hk.sub hkv
  have hℓr : Bdd fun x ↦ ℓ x - dirLoss S (-(responseVel hS ν hg hℓ : J → ℝ)) x := hℓ.sub hℓv
  have ek : k = fun x ↦ dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) x +
      (k x - dirLoss S (-(responseVel hS ν hg hk : J → ℝ)) x) := by
    funext x
    ring
  have eℓ : ℓ = fun x ↦ dirLoss S (-(responseVel hS ν hg hℓ : J → ℝ)) x +
      (ℓ x - dirLoss S (-(responseVel hS ν hg hℓ : J → ℝ)) x) := by
    funext x
    ring
  have h1 := lawCov_residual_dirLoss_eq_zero hS ν hg hℓ hm (-(responseVel hS ν hg hk : J → ℝ))
  have h2 := lawCov_residual_dirLoss_eq_zero hS ν hg hk hm (-(responseVel hS ν hg hℓ : J → ℝ))
  conv_lhs => rw [ek, eℓ]
  rw [lawCov_add_left_eq _ hkv hkr (hℓv.add hℓr), lawCov_add_right_eq _ hℓv hℓr hkv,
    lawCov_add_right_eq _ hℓv hℓr hkr, lawCov_visible_visible_of_matched hS ν hg hm hk hℓ,
    lawCov_comm _ (dirLoss S (-(responseVel hS ν hg hk : J → ℝ))), h1, h2]
  ring

end Matched

end Bilinear

end Laplace.Multi
