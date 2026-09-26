/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# A compact-uniform second-order Peano remainder

If `F` is differentiable on a compact convex set `C` with derivative field `A`, and `A` is
differentiable on `C` with derivative field `B` continuous on `C`, then the second-order Peano
remainder of `F` is uniformly small on `C`: for every `ε > 0` there is `δ > 0` with

`‖F z' − F z − A z (z' − z) − ½ B z (z' − z) (z' − z)‖ ≤ ε ‖z' − z‖²`

for all `z, z' ∈ C` with `‖z' − z‖ ≤ δ` (`uniform_peano_of_hasFDerivAt`). The proof is two mean
value inequalities along the segment and the uniform continuity of `B` on the compact `C`.
-/

open Filter Topology Set

namespace Laplace.Multi

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- The derivative field of a `C²` map is uniformly first-order approximated by its derivative on
a convex set where the second derivative is `ε`-close: `‖A(z + tw) − A z − t B z w‖ ≤ ε t ‖w‖`. -/
theorem norm_sub_deriv_le_of_uniform {A : E → (E →L[ℝ] G)} {B : E → (E →L[ℝ] (E →L[ℝ] G))}
    {z w : E} {ε : ℝ} (hA : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt A (B (z + t • w)) (z + t • w))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖B (z + t • w) - B z‖ ≤ ε) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖A (z + t • w) - A z - t • B z w‖ ≤ ε * ‖w‖ * t := by
  have hderiv : ∀ s ∈ Icc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ ↦ A (z + s • w) - s • B z w) (B (z + s • w) w - B z w) s := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    have hl : HasDerivAt (fun s : ℝ ↦ z + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add z
    have h1 := (hA s hs').comp_hasDerivAt s hl
    have h2 : HasDerivAt (fun s : ℝ ↦ s • B z w) (B z w) s := by
      simpa using (hasDerivAt_id s).smul_const (B z w)
    exact h1.sub h2
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖B (z + s • w) w - B z w‖ ≤ ε * ‖w‖ := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le.trans ht.2⟩
    calc ‖B (z + s • w) w - B z w‖ = ‖(B (z + s • w) - B z) w‖ := by
          rw [sub_apply]
      _ ≤ ‖B (z + s • w) - B z‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖w‖ := mul_le_mul_of_nonneg_right (hB s hs') (norm_nonneg _)
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := t)
    (fun s hs ↦ (hderiv s hs).hasDerivWithinAt) hbound t (right_mem_Icc.mpr ht.1)
  calc ‖A (z + t • w) - A z - t • B z w‖ = ‖A (z + t • w) - t • B z w - A z‖ := by
        congr 1
        abel
    _ ≤ ε * ‖w‖ * t := by simpa using key

/-- **The compact-uniform second-order Peano remainder.** -/
theorem uniform_peano_of_hasFDerivAt {F : E → G} {A : E → (E →L[ℝ] G)}
    {B : E → (E →L[ℝ] (E →L[ℝ] G))} {C : Set E} (hC : IsCompact C) (hCc : Convex ℝ C)
    (hF : ∀ z ∈ C, HasFDerivAt F (A z) z) (hA : ∀ z ∈ C, HasFDerivAt A (B z) z)
    (hB : ContinuousOn B C) :
    ∀ ε > 0, ∃ δ > 0, ∀ z ∈ C, ∀ z' ∈ C, ‖z' - z‖ ≤ δ →
      ‖F z' - F z - A z (z' - z) - (1 / 2 : ℝ) • B z (z' - z) (z' - z)‖ ≤ ε * ‖z' - z‖ ^ 2 := by
  intro ε hε
  obtain ⟨δ, hδ, hδB⟩ := Metric.uniformContinuousOn_iff.1
    (hC.uniformContinuousOn_of_continuous hB) ε hε
  refine ⟨δ / 2, by positivity, fun z hz z' hz' hzz ↦ ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : E, w = z' - z := ⟨_, rfl⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, z + t • w ∈ C := fun t ht ↦ by
    rw [hw]
    exact hCc.add_smul_sub_mem hz hz' ht
  have hBt : ∀ t ∈ Icc (0 : ℝ) 1, ‖B (z + t • w) - B z‖ ≤ ε := fun t ht ↦ by
    have hd : dist (z + t • w) z < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ = ‖w‖ := one_mul _
        _ ≤ δ / 2 := hw ▸ hzz
        _ < δ := by linarith
    have := hδB _ (hseg t ht) z hz hd
    rw [dist_eq_norm] at this
    exact this.le
  have hAt : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt A (B (z + t • w)) (z + t • w) :=
    fun t ht ↦ hA _ (hseg t ht)
  -- the derivative of the second-order defect along the segment
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ F (z + t • w) - t • A z w - (t ^ 2 / 2) • B z w w)
        ((A (z + t • w) - A z - t • B z w) w) t := by
    intro t ht
    have hl : HasDerivAt (fun t : ℝ ↦ z + t • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add z
    have h1 := (hF _ (hseg t ht)).comp_hasDerivAt t hl
    have h2 : HasDerivAt (fun t : ℝ ↦ t • A z w) (A z w) t := by
      simpa using (hasDerivAt_id t).smul_const (A z w)
    have h3 : HasDerivAt (fun t : ℝ ↦ (t ^ 2 / 2) • B z w w) (t • B z w w) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).smul_const (B z w w)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      congr 1
      ring
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    simp only [sub_apply, smul_apply]
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖(A (z + t • w) - A z - t • B z w) w‖ ≤ ε * ‖w‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    calc ‖(A (z + t • w) - A z - t • B z w) w‖
        ≤ ‖A (z + t • w) - A z - t • B z w‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε * ‖w‖ * t) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_deriv_le_of_uniform hAt hBt ht') (norm_nonneg _)
      _ ≤ (ε * ‖w‖ * 1) * ‖w‖ := by gcongr; exact ht.2.le
      _ = ε * ‖w‖ ^ 2 := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1)
    (fun t ht ↦ (hderiv t ht).hasDerivWithinAt) hbound 1 (right_mem_Icc.mpr zero_le_one)
  simp only [one_smul, zero_smul, add_zero, sub_zero, one_pow, mul_one, zero_pow two_ne_zero,
    zero_div] at key
  rw [hw] at key
  have e : F (z + (z' - z)) - A z (z' - z) - (1 / 2 : ℝ) • B z (z' - z) (z' - z) - F z =
      F z' - F z - A z (z' - z) - (1 / 2 : ℝ) • B z (z' - z) (z' - z) := by
    rw [add_sub_cancel]
    abel
  rw [e] at key
  exact key

end Laplace.Multi
