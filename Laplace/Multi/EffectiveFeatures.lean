/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TwoAxisResponse

/-!
# The effective feature space: the response map on a complement of the invisible directions

Without any nondegeneracy assumption, let `N = invisibleSubmodule μ R` be the directions whose
contrast `R_v` is a.e. constant. Then

* the posterior does not see `N`: `P_b = P_a` whenever `b − a ∈ N` (`priorExp_eq_of_sub_mem`);
* the feature covariance has kernel exactly `N`: `C u = 0 ↔ u ∈ N` (`featCov_mulVec_eq_zero_iff`);
* on any complement `W` of `N` the mean map is injective (`injOn_meanMap_of_isCompl`), its image is
  the whole response range (`image_meanMap_of_isCompl`), so `m|_W : W ≃ range m`
  (`bijOn_meanMap_of_isCompl`), and the response form is positive definite on `W`
  (`responseForm_pos_of_isCompl`).

So the intrinsic response theory lives on the effective feature space `W ≅ (ι → ℝ)/N`, of dimension
`|ι| − dim N` (`finrank_compl_invisible`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] in
/-- A covariance with an a.e. constant observable vanishes. -/
theorem priorCov_eq_zero_of_ae_const (a : ι → ℝ) (φ : X → ℝ) {ψ : X → ℝ} {c : ℝ}
    (hc : ∀ᵐ x ∂μ, ψ x = c) : priorCov μ π (affLoss L₀ R a) φ ψ t = 0 := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  unfold priorCov
  have h1 : priorExp μ π (affLoss L₀ R a) (fun x ↦ φ x * ψ x) t =
      priorExp μ π (affLoss L₀ R a) (fun x ↦ c * φ x) t :=
    priorExp_congr_ae' π _ (hc.mono fun x hx ↦ by rw [hx, mul_comm]) t
  rw [h1, priorExp_const_mul_bdd, priorExp_congr_ae' π _ hc t, priorExp_const_fun hZ]
  ring

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
/-- **The posterior is constant along the invisible directions.** -/
theorem priorExp_eq_of_sub_mem (a b : ι → ℝ) (h : b - a ∈ invisibleSubmodule μ R) (φ : X → ℝ)
    (t : ℝ) : priorExp μ π (affLoss L₀ R b) φ t = priorExp μ π (affLoss L₀ R a) φ t := by
  have := priorExp_affLoss_add_of_invisible (L₀ := L₀) (π := π) a h φ t
  rwa [add_sub_cancel] at this

/-- **The kernel of the feature covariance is the invisible subspace**: `C u = 0 ↔ u ∈ N`. -/
theorem featCov_mulVec_eq_zero_iff (ht : 0 < t) (a u : ι → ℝ) :
    (featCov μ π L₀ R t a).mulVec u = 0 ↔ u ∈ invisibleSubmodule μ R := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  constructor
  · intro h
    have hq : priorCov μ π (affLoss L₀ R a) (dirLoss R u) (dirLoss R u) t = 0 := by
      have := congrArg (dotProduct u) h
      rw [dotProduct_zero] at this
      rw [← this]
      simp only [dotProduct, featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a u]
      rw [← sum_mul_priorCov_eq hν hR (bdd_dirLoss hR u) u]
    have hform : responseForm μ π L₀ R a t u u = 0 := by
      unfold responseForm
      rw [hq, mul_zero]
    exact (responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht a u).1 hform
  · rintro ⟨c, hc⟩
    funext i
    rw [featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a u i,
      priorCov_eq_zero_of_ae_const hπm hπi hπ hπpos hL₀m hL₀ hR a (R i) hc]
    rfl

/-- **The mean map is injective on any complement of the invisible subspace.** -/
theorem injOn_meanMap_of_isCompl (ht : 0 < t) {W : Submodule ℝ (ι → ℝ)}
    (hW : IsCompl (invisibleSubmodule μ R) W) :
    Set.InjOn (meanMap μ π L₀ R t) (W : Set (ι → ℝ)) := by
  intro a ha b hb hab
  have hk : b - a ∈ invisibleSubmodule μ R :=
    (meanMap_eq_iff_invisible hπm hπi hπ hπpos hL₀m hL₀ hR ht a b).1 hab
  have hW' : b - a ∈ W := W.sub_mem hb ha
  have hmem : b - a ∈ invisibleSubmodule μ R ⊓ W := Submodule.mem_inf.2 ⟨hk, hW'⟩
  rw [hW.inf_eq_bot, Submodule.mem_bot] at hmem
  exact (sub_eq_zero.1 hmem).symm

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
/-- **A complement of the invisible subspace reaches every response.** -/
theorem image_meanMap_of_isCompl {W : Submodule ℝ (ι → ℝ)}
    (hW : IsCompl (invisibleSubmodule μ R) W) :
    meanMap μ π L₀ R t '' (W : Set (ι → ℝ)) = Set.range (meanMap μ π L₀ R t) := by
  refine Set.Subset.antisymm (Set.image_subset_range _ _) ?_
  rintro y ⟨a, rfl⟩
  obtain ⟨n, w, hn, hw, hnw⟩ := (Submodule.codisjoint_iff_exists_add_eq.1 hW.codisjoint) a
  refine ⟨w, hw, ?_⟩
  rw [← hnw, add_comm, meanMap_add_of_invisible (L₀ := L₀) (π := π) (t := t) w hn]

/-- **The response chart on the effective feature space**: `m|_W : W ≃ range m`. -/
theorem bijOn_meanMap_of_isCompl (ht : 0 < t) {W : Submodule ℝ (ι → ℝ)}
    (hW : IsCompl (invisibleSubmodule μ R) W) :
    Set.BijOn (meanMap μ π L₀ R t) (W : Set (ι → ℝ)) (Set.range (meanMap μ π L₀ R t)) :=
  ⟨fun a _ ↦ ⟨a, rfl⟩, injOn_meanMap_of_isCompl hπm hπi hπ hπpos hL₀m hL₀ hR ht hW,
    fun y hy ↦ by
      rw [← image_meanMap_of_isCompl (L₀ := L₀) (π := π) (t := t) hW] at hy
      exact hy⟩

/-- **The response form is positive definite on a complement of the invisible subspace.** -/
theorem responseForm_pos_of_isCompl (ht : 0 < t) {W : Submodule ℝ (ι → ℝ)}
    (hW : IsCompl (invisibleSubmodule μ R) W) (a : ι → ℝ) {w : ι → ℝ} (hw : w ∈ W)
    (hw0 : w ≠ 0) : 0 < responseForm μ π L₀ R a t w w := by
  refine lt_of_le_of_ne (mul_nonneg (sq_nonneg _)
    (priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a (bdd_dirLoss hR w))) fun h ↦ ?_
  obtain ⟨c, hc⟩ := (responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht a w).1 h.symm
  have hmem : w ∈ invisibleSubmodule μ R ⊓ W := Submodule.mem_inf.2 ⟨⟨c, hc⟩, hw⟩
  rw [hW.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hw0 hmem

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
/-- The effective feature dimension is `|ι| − dim N`. -/
theorem finrank_compl_invisible {W : Submodule ℝ (ι → ℝ)}
    (hW : IsCompl (invisibleSubmodule μ R) W) :
    Module.finrank ℝ W + Module.finrank ℝ (invisibleSubmodule μ R) = Fintype.card ι := by
  rw [add_comm, Submodule.finrank_add_eq_of_isCompl hW, Module.finrank_fintype_fun_eq_card]

end

end Laplace.Multi
