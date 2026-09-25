/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RelativeMomentBody
import Laplace.Multi.QuotientMeanMap

/-!
# The intrinsic response chart

The mean map `θ ↦ E_θ S` of a family with possibly dependent features is not injective: it is
constant along invisible directions (a.s.-constant contrasts). Restricted to the direction subspace
`𝕍` of the affine span of the moment body it becomes a **bijection onto the relative interior**
(`intrinsicChart : 𝕍 ≃ intrinsicInterior ℝ K`): an invisible direction lying in `𝕍` is zero
(`eq_zero_of_invisible_of_mem_dirSpan`), so the mean map is injective on `𝕍`
(`meanMap_injOn_dirSpan`), and the minimiser of the variational functional on `𝕍` gives surjectivity
(`exists_min_variational_rel`, `meanMap_eq_of_min_rel`). This is the coordinate-free chart of the
response space that needs no nondegeneracy hypothesis: every parameter class modulo the invisible
directions has exactly one representative in `𝕍`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]
variable [Nonempty X] {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπi hπ hπpos hS

omit [Nonempty X] [Nonempty J] hπi hπpos in
/-- **An invisible direction in the direction subspace is zero.** -/
theorem eq_zero_of_invisible_of_mem_dirSpan {e : J → ℝ} (he : e ∈ invisibleSet μ S)
    (heV : e ∈ dirSpan μ π S) : e = 0 := by
  obtain ⟨c, hc⟩ := he
  have hle := momentBody_subset_halfspace hπm hπ hS (hc.mono fun x hx ↦ hx.le)
  have hge := momentBody_subset_halfspace hπm hπ hS (u := -e) (β := -c) (by
    filter_upwards [hc] with x hx
    rw [show -e = (-1 : ℝ) • e by rw [neg_one_smul], dirLoss_smul]
    change (-1 : ℝ) * dirLoss S e x ≤ -c
    rw [hx]
    linarith)
  have hhyp : momentBody μ π S ⊆ {y | dotJ e y = c} := fun y hy ↦ by
    have h1 := hle hy
    have h2 := hge hy
    simp only [Set.mem_ofPred_eq, dotJ_neg_left] at h1 h2 ⊢
    linarith
  have hker : dirSpan μ π S ≤ LinearMap.ker (IsLinearMap.mk' (dotJ e) (isLinearMap_dotJ e)) := by
    unfold dirSpan
    rw [direction_affineSpan, vectorSpan_def]
    refine Submodule.span_le.2 fun v hv ↦ ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_vsub.1 hv
    have h1 : dotJ e y = c := hhyp hy
    have h2 : dotJ e z = c := hhyp hz
    rw [SetLike.mem_coe, LinearMap.mem_ker, IsLinearMap.mk'_apply, vsub_eq_sub,
      (isLinearMap_dotJ e).map_sub, h1, h2, sub_self]
  have h := hker heV
  rw [LinearMap.mem_ker, IsLinearMap.mk'_apply] at h
  funext j
  exact mul_self_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_self_nonneg _).1 h j (Finset.mem_univ j))

omit [Nonempty J] in
/-- **The mean map is injective on the direction subspace.** -/
theorem meanMap_injOn_dirSpan :
    Set.InjOn (meanMap μ π (fun _ ↦ (0 : ℝ)) S 1) (dirSpan μ π S) := by
  intro a ha b hb hab
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hinv := (meanMap_eq_iff_invisible hπm hπi hπ hπpos measurable_const h0 hS one_pos a b).1 hab
  have hz := eq_zero_of_invisible_of_mem_dirSpan hπm hπ hS hinv (Submodule.sub_mem _ hb ha)
  exact (sub_eq_zero.1 hz).symm

/-- **The intrinsic response chart**: the mean map restricted to the direction subspace is a
bijection onto the relative interior of the moment body. -/
noncomputable def intrinsicChart :
    dirSpan μ π S ≃ intrinsicInterior ℝ (momentBody μ π S) :=
  Equiv.ofBijective
    (fun θ ↦ ⟨meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ, by
      rw [← range_meanMap_eq_intrinsicInterior_momentBody hπm hπi hπ hπpos hS]
      exact ⟨θ, rfl⟩⟩)
    ⟨fun θ θ' h ↦ Subtype.ext (meanMap_injOn_dirSpan hπm hπi hπ hπpos hS θ.2 θ'.2
        (congrArg Subtype.val h)),
      fun M ↦ by
        obtain ⟨θ₀, hθ₀V, hmin⟩ := exists_min_variational_rel hπm hπi hπ hπpos hS M.2
        exact ⟨⟨θ₀, hθ₀V⟩, Subtype.ext (meanMap_eq_of_min_rel hπm hπi hπ hπpos hS
          (intrinsicInterior_subset M.2) hθ₀V hmin)⟩⟩

theorem intrinsicChart_apply (θ : dirSpan μ π S) :
    (intrinsicChart hπm hπi hπ hπpos hS θ : J → ℝ) = meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 θ := rfl

/-- The inverse chart is a right inverse of the mean map on the relative interior. -/
theorem meanMap_intrinsicChart_symm (M : intrinsicInterior ℝ (momentBody μ π S)) :
    meanMap μ π (fun _ ↦ (0 : ℝ)) S 1 ((intrinsicChart hπm hπi hπ hπpos hS).symm M) = M := by
  have := (intrinsicChart hπm hπi hπ hπpos hS).apply_symm_apply M
  exact congrArg Subtype.val this

end

end Laplace.Multi
