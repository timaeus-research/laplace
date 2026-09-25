/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MomentBody

/-!
# The relative interior of a convex set in feature space

Two characterisations of Mathlib's `intrinsicInterior ℝ K` for `K ⊆ (J → ℝ)`, used to chart the
response space of a family whose features may be affinely dependent:

* **the ball form** (`mem_intrinsicInterior_iff_exists_ball`): `x ∈ relint K` iff `x ∈ K` and
  `x + v ∈ K` for every small `v` in the direction of the affine span of `K`;
* **the supporting form** (`mem_intrinsicInterior_iff_forall_supporting`, `K` convex):
  `x ∈ relint K` iff `x ∈ K` and every functional `e·` maximised at `x` over `K` is constant on
  `K`. The forward direction moves from `x` away from any `y ∈ K`; the converse is Hahn–Banach on
  the direction subspace, with the functional extended to the feature space
  (`LinearMap.exists_extend`) and read as `dotJ e`.
-/

open Set Topology

namespace Laplace.Multi

variable {J : Type*} [Fintype J]

/-- **The intrinsic interior through the direction of the affine span.** -/
theorem mem_intrinsicInterior_iff_exists_ball {K : Set (J → ℝ)} {x : J → ℝ} :
    x ∈ intrinsicInterior ℝ K ↔
      x ∈ K ∧ ∃ δ > 0, ∀ v ∈ (affineSpan ℝ K).direction, ‖v‖ < δ → x + v ∈ K := by
  rw [mem_intrinsicInterior]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyK : y ∈ Subtype.val ⁻¹' K := interior_subset hy
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hy
    obtain ⟨u, hu, hsub⟩ := hy
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨hyK, δ, hδ, fun v hv hvδ ↦ ?_⟩
    have hmem : (y : J → ℝ) + v ∈ affineSpan ℝ K := by
      have := (AffineSubspace.vadd_mem_iff_mem_direction v y.2).2 hv
      simpa [vadd_eq_add, add_comm] using this
    have hu' : (y : J → ℝ) + v ∈ u := by
      refine hball ?_
      rw [Metric.mem_ball, dist_eq_norm]
      simpa using hvδ
    exact hsub (show (⟨_, hmem⟩ : affineSpan ℝ K) ∈ Subtype.val ⁻¹' u from hu')
  · rintro ⟨hxK, δ, hδ, h⟩
    refine ⟨⟨x, mem_affineSpan ℝ hxK⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype]
    refine ⟨Metric.ball x δ, Metric.ball_mem_nhds x hδ, fun z hz ↦ ?_⟩
    have hv : (z : J → ℝ) - x ∈ (affineSpan ℝ K).direction := by
      have := AffineSubspace.vsub_mem_direction z.2 (mem_affineSpan ℝ hxK)
      simpa [vsub_eq_sub] using this
    have hz' : ‖(z : J → ℝ) - x‖ < δ := by
      have : (z : J → ℝ) ∈ Metric.ball x δ := hz
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have := h _ hv hz'
    have e : x + ((z : J → ℝ) - x) = z := by abel
    rw [e] at this
    exact this

omit [Fintype J] in
/-- Displacements from `x` into `K`, as a subset of the direction subspace. -/
def displacements (K : Set (J → ℝ)) (x : J → ℝ) : Set (affineSpan ℝ K).direction :=
  {v | x + (v : J → ℝ) ∈ K}

omit [Fintype J] in
theorem convex_displacements {K : Set (J → ℝ)} (hK : Convex ℝ K) (x : J → ℝ) :
    Convex ℝ (displacements K x) := by
  intro u hu w hw a b ha hb hab
  have h := hK hu hw ha hb hab
  change x + ((a • u + b • w : (affineSpan ℝ K).direction) : J → ℝ) ∈ K
  have e : x + ((a • u + b • w : (affineSpan ℝ K).direction) : J → ℝ) =
      a • (x + (u : J → ℝ)) + b • (x + (w : J → ℝ)) := by
    push_cast
    calc x + (a • (u : J → ℝ) + b • (w : J → ℝ))
        = (a + b) • x + (a • (u : J → ℝ) + b • (w : J → ℝ)) := by rw [hab, one_smul]
      _ = a • (x + (u : J → ℝ)) + b • (x + (w : J → ℝ)) := by module
  rw [e]
  exact h

set_option linter.unusedFintypeInType false in
/-- The displacement to a relative-interior point is an interior displacement. -/
theorem mem_interior_displacements {K : Set (J → ℝ)} {x z : J → ℝ}
    (hz : z ∈ intrinsicInterior ℝ K) (w : (affineSpan ℝ K).direction)
    (hw : (w : J → ℝ) = z - x) : w ∈ interior (displacements K x) := by
  obtain ⟨_, δ, hδ, hball⟩ := mem_intrinsicInterior_iff_exists_ball.1 hz
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨δ, hδ, fun v hv ↦ ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] at hv
  have hmem := hball _ (v - w).2 (by simpa using hv)
  change x + (v : J → ℝ) ∈ K
  have e : x + (v : J → ℝ) = z + ((v - w : (affineSpan ℝ K).direction) : J → ℝ) := by
    push_cast
    rw [hw]
    abel
  rw [e]
  exact hmem

/-- **The relative interior via supporting functionals**: a point of a convex set lies in the
relative interior iff every functional maximised at it over the set is constant on the set. -/
theorem mem_intrinsicInterior_iff_forall_supporting {K : Set (J → ℝ)} (hK : Convex ℝ K)
    {x : J → ℝ} :
    x ∈ intrinsicInterior ℝ K ↔
      x ∈ K ∧ ∀ e : J → ℝ, (∀ y ∈ K, dotJ e y ≤ dotJ e x) → ∀ y ∈ K, dotJ e y = dotJ e x := by
  constructor
  · intro hx
    obtain ⟨hxK, δ, hδ, hball⟩ := mem_intrinsicInterior_iff_exists_ball.1 hx
    refine ⟨hxK, fun e he y hy ↦ le_antisymm (he y hy) ?_⟩
    have hv : x - y ∈ (affineSpan ℝ K).direction := by
      have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hxK) (mem_affineSpan ℝ hy)
      simpa [vsub_eq_sub] using this
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = δ / (2 * (‖x - y‖ + 1)) := ⟨_, rfl⟩
    have hε : 0 < ε := by
      rw [hεdef]
      positivity
    have hεv : ‖ε • (x - y)‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      calc ε * ‖x - y‖ ≤ ε * (‖x - y‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
        _ = δ / 2 := by
          rw [hεdef, div_mul_eq_mul_div, mul_div_mul_right _ _ (by positivity)]
        _ < δ := by linarith
    have hmem := hball _ (Submodule.smul_mem _ ε hv) hεv
    have h1 := he _ hmem
    rw [(isLinearMap_dotJ e).map_add, (isLinearMap_dotJ e).map_smul, smul_eq_mul,
      (isLinearMap_dotJ e).map_sub] at h1
    nlinarith
  · rintro ⟨hxK, hsupp⟩
    by_contra hx
    have hUc := convex_displacements hK x
    have h0 : (0 : (affineSpan ℝ K).direction) ∉ interior (displacements K x) := by
      intro h0
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h0
      obtain ⟨δ, hδ, hball⟩ := h0
      refine hx (mem_intrinsicInterior_iff_exists_ball.2 ⟨hxK, δ, hδ, fun v hv hvδ ↦ ?_⟩)
      have : (⟨v, hv⟩ : (affineSpan ℝ K).direction) ∈ Metric.ball 0 δ := by
        rw [Metric.mem_ball, dist_zero_right]
        exact hvδ
      exact hball this
    obtain ⟨z, hz⟩ := (intrinsicInterior_nonempty hK).2 ⟨x, hxK⟩
    have hzK : z ∈ K := intrinsicInterior_subset hz
    have hwV : z - x ∈ (affineSpan ℝ K).direction := by
      have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hzK) (mem_affineSpan ℝ hxK)
      simpa [vsub_eq_sub] using this
    have hw := mem_interior_displacements hz ⟨z - x, hwV⟩ rfl
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hUc.interior isOpen_interior h0
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (f : (affineSpan ℝ K).direction →ₗ[ℝ] ℝ)
    have hgf : ∀ v : (affineSpan ℝ K).direction, g v = f v := fun v ↦ by
      have := LinearMap.congr_fun hg v
      simpa using this
    classical
    obtain ⟨e, hedef⟩ : ∃ e : J → ℝ, e = fun j ↦ g (Pi.single j 1) := ⟨_, rfl⟩
    have hge : ∀ y : J → ℝ, g y = dotJ e y := fun y ↦ by
      conv_lhs => rw [pi_eq_sum_univ' y]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_comm, hedef]
    have hcl : closure (interior (displacements K x)) ⊆ {u | f u ≤ f 0} :=
      closure_minimal (fun u hu ↦ (hf u hu).le) (isClosed_le f.continuous continuous_const)
    have hUcl : displacements K x ⊆ closure (interior (displacements K x)) := by
      rw [hUc.closure_interior_eq_closure_of_nonempty_interior ⟨_, hw⟩]
      exact subset_closure
    have hle : ∀ y ∈ K, dotJ e y ≤ dotJ e x := fun y hy ↦ by
      have hyV : y - x ∈ (affineSpan ℝ K).direction := by
        have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hy) (mem_affineSpan ℝ hxK)
        simpa [vsub_eq_sub] using this
      have hyU : (⟨y - x, hyV⟩ : (affineSpan ℝ K).direction) ∈ displacements K x := by
        change x + (y - x) ∈ K
        rwa [add_sub_cancel]
      have := hcl (hUcl hyU)
      simp only [Set.mem_ofPred_eq, map_zero] at this
      rw [← hgf, hge, (isLinearMap_dotJ e).map_sub] at this
      linarith
    have hlt : dotJ e z < dotJ e x := by
      have := hf _ hw
      rw [map_zero, ← hgf, hge, (isLinearMap_dotJ e).map_sub] at this
      linarith
    exact hlt.ne (hsupp e hle z hzK)

end Laplace.Multi
