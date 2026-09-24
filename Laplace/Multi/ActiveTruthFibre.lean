/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthAssembly
import Laplace.Multi.PolytopeFibre

/-!
# The fibre of an active-truth face is a polytope

Step 4 of the transverse active-truth face theorem (`notes/active_truth_handoff.md`). Over a
transverse point `v = (s, h)` the fibre `fibreSet κ Q δ γ L v` (the free coordinates `z' > 0`
whose solved pair lies in the orthant) is the open polytope
`{z' > 0 | c_j · z' < a_j L + b_j(v), j = 0, 1}` with `c_j = N_{j0} κ' − N_{j1} Q'`,
`a_j = N_{j0} δ − N_{j1} γ`, `b_j(v) = (N v)_j`, where `N = M⁻¹` is the inverse transverse matrix
(`mem_fibreSet_iff`). Its volume equals the volume of the closed fibre `fibre2` of
`PolytopeFibre` (`volume_fibreSet_eq`), it is contained in the box
`∏ (0, (s + δL)/κ'_i]` (`volume_fibreSet_le`, the `κ_min` bound of the handoff), and
`volume (fibreSet v) / L^k` converges to the volume of the limiting polytope
`{w ≥ 0 | c_j · w ≤ a_j}` (`tendsto_volume_fibreSet_div`), the face `F_J` of the note projected
to the free coordinates.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-- The coefficient vector of the `j`-th fibre constraint: `N_{j0} κ' − N_{j1} Q'`. -/
noncomputable def fibreCoef (κ Q : Fin k ⊕ Fin 2 → ℝ) (j : Fin 2) : Fin k → ℝ :=
  fun i ↦ (transMat κ Q)⁻¹ j 0 * κ (Sum.inl i) - (transMat κ Q)⁻¹ j 1 * Q (Sum.inl i)

/-- The `L`-coefficient of the `j`-th fibre constraint: `N_{j0} δ − N_{j1} γ`. -/
noncomputable def fibreA (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ : ℝ) (j : Fin 2) : ℝ :=
  (transMat κ Q)⁻¹ j 0 * δ - (transMat κ Q)⁻¹ j 1 * γ

/-- The constant of the `j`-th fibre constraint: `(N v)_j`. -/
noncomputable def fibreB (κ Q : Fin k ⊕ Fin 2 → ℝ) (v : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  (transMat κ Q)⁻¹ j 0 * v 0 + (transMat κ Q)⁻¹ j 1 * v 1

theorem fibreB_eq_mulVec (κ Q : Fin k ⊕ Fin 2 → ℝ) (v : Fin 2 → ℝ) :
    fibreB κ Q v = (transMat κ Q)⁻¹ *ᵥ v := by
  funext j
  simp [fibreB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem fibreB_mulVec {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (b : Fin 2 → ℝ) : fibreB κ Q (transMat κ Q *ᵥ b) = b := by
  rw [fibreB_eq_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hΔ), Matrix.one_mulVec]

theorem fibreCoef_dotProduct (κ Q : Fin k ⊕ Fin 2 → ℝ) (j : Fin 2) (z' : Fin k → ℝ) :
    fibreCoef κ Q j ⬝ᵥ z' =
      (transMat κ Q)⁻¹ j 0 * ∑ i, κ (Sum.inl i) * z' i -
        (transMat κ Q)⁻¹ j 1 * ∑ i, Q (Sum.inl i) * z' i := by
  simp only [fibreCoef, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The solved pair as an affine function of the free coordinates. -/
theorem inv_mulVec_sub_shift (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L : ℝ) (z' : Fin k → ℝ)
    (v : Fin 2 → ℝ) (j : Fin 2) :
    ((transMat κ Q)⁻¹ *ᵥ (v - transShift κ Q δ γ L z')) j =
      fibreA κ Q δ γ j * L + fibreB κ Q v j - fibreCoef κ Q j ⬝ᵥ z' := by
  rw [fibreCoef_dotProduct]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply, transShift,
    Matrix.cons_val_zero, Matrix.cons_val_one, fibreA, fibreB]
  ring

/-- **The fibre is an open polytope.** -/
theorem mem_fibreSet_iff {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (δ γ L : ℝ) (v : Fin 2 → ℝ) (z' : Fin k → ℝ) :
    z' ∈ fibreSet κ Q δ γ L v ↔
      (∀ i, 0 < z' i) ∧ ∀ j, fibreCoef κ Q j ⬝ᵥ z' < fibreA κ Q δ γ j * L + fibreB κ Q v j := by
  unfold fibreSet
  rw [Set.mem_ofPred_eq, image_mulVec_add_orthant hΔ, mem_preimage, Set.mem_ofPred_eq]
  simp only [inv_mulVec_sub_shift, sub_pos]

/-- The closed fibre of `PolytopeFibre`, as the closed orthant condition on the solved pair. -/
theorem mem_fibre2_iff {κ Q : Fin k ⊕ Fin 2 → ℝ} (δ γ L : ℝ) (v : Fin 2 → ℝ)
    (z' : Fin k → ℝ) :
    z' ∈ fibre2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1)
        (fibreB κ Q v 0) (fibreB κ Q v 1) L ↔
      (∀ i, 0 ≤ z' i) ∧ ∀ j, 0 ≤ ((transMat κ Q)⁻¹ *ᵥ (v - transShift κ Q δ γ L z')) j := by
  simp only [fibre2, Set.mem_ofPred_eq, inv_mulVec_sub_shift, sub_nonneg, Fin.forall_fin_two]

theorem fibreSet_subset_fibre2 {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (δ γ L : ℝ) (v : Fin 2 → ℝ) :
    fibreSet κ Q δ γ L v ⊆ fibre2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0)
      (fibreA κ Q δ γ 1) (fibreB κ Q v 0) (fibreB κ Q v 1) L := by
  intro z' hz
  rw [mem_fibreSet_iff hΔ] at hz
  exact ⟨fun i ↦ (hz.1 i).le, (hz.2 0).le, (hz.2 1).le⟩

/-- **The `κ_min` box bound**: on the closed fibre, `κ'_i z'_i ≤ s + δL`. -/
theorem fibre2_subset_box {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (hκ : ∀ i, 0 < κ i) (δ γ L : ℝ) (v : Fin 2 → ℝ) :
    fibre2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1)
        (fibreB κ Q v 0) (fibreB κ Q v 1) L ⊆
      {z' | ∀ i, 0 ≤ z' i ∧ κ (Sum.inl i) * z' i ≤ v 0 + δ * L} := by
  intro z' hz
  rw [mem_fibre2_iff] at hz
  obtain ⟨hz0, hy⟩ := hz
  have hv : transMat κ Q *ᵥ ((transMat κ Q)⁻¹ *ᵥ (v - transShift κ Q δ γ L z')) +
      transShift κ Q δ γ L z' = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΔ),
      Matrix.one_mulVec, sub_add_cancel]
  rw [transMat_mulVec_add_shift] at hv
  have h0 := congrFun hv 0
  simp only [Matrix.cons_val_zero] at h0
  rw [sum_elim_mul] at h0
  intro i
  refine ⟨hz0 i, ?_⟩
  have h1 : κ (Sum.inl i) * z' i ≤ ∑ j, κ (Sum.inl j) * z' j :=
    Finset.single_le_sum (f := fun j ↦ κ (Sum.inl j) * z' j)
      (fun j _ ↦ mul_nonneg (hκ _).le (hz0 j)) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ j, κ (Sum.inr j) * ((transMat κ Q)⁻¹ *ᵥ (v - transShift κ Q δ γ L z')) j :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hκ _).le (hy j)
  linarith

/-- The open fibre and the closed fibre have the same volume (they differ by hyperplanes), as long
as no constraint is the degenerate `0 < 0`. -/
theorem volume_fibreSet_eq {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    {δ γ L : ℝ} {v : Fin 2 → ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 * L + fibreB κ Q v 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 * L + fibreB κ Q v 1 ≠ 0) :
    volume (fibreSet κ Q δ γ L v) =
      volume (fibre2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1)
        (fibreB κ Q v 0) (fibreB κ Q v 1) L) := by
  refine le_antisymm (measure_mono (fibreSet_subset_fibre2 hΔ δ γ L v)) ?_
  set N : Set (Fin k → ℝ) :=
    {x | fibreCoef κ Q 0 ⬝ᵥ x = fibreA κ Q δ γ 0 * L + fibreB κ Q v 0} ∪
      {x | fibreCoef κ Q 1 ⬝ᵥ x = fibreA κ Q δ γ 1 * L + fibreB κ Q v 1} ∪
      ⋃ i, {x : Fin k → ℝ | x i = 0} with hN
  have hnull : volume N = 0 :=
    measure_union_null (measure_union_null (volume_hyperplane' hc₀) (volume_hyperplane' hc₁))
      (measure_iUnion_null fun i ↦ volume_coordHyperplane i)
  calc volume (fibre2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0)
        (fibreA κ Q δ γ 1) (fibreB κ Q v 0) (fibreB κ Q v 1) L)
      ≤ volume (fibreSet κ Q δ γ L v ∪ N) := measure_mono ?_
    _ ≤ volume (fibreSet κ Q δ γ L v) + volume N := measure_union_le _ _
    _ = volume (fibreSet κ Q δ γ L v) := by rw [hnull, add_zero]
  intro x hx
  by_cases hxf : x ∈ fibreSet κ Q δ γ L v
  · exact Or.inl hxf
  · right
    rw [mem_fibreSet_iff hΔ] at hxf
    obtain ⟨hx0, hx1, hx2⟩ := hx
    rw [hN]
    simp only [mem_union, mem_iUnion, Set.mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    exact hxf ⟨fun i ↦ lt_of_le_of_ne (hx0 i) (Ne.symm (hcon.2 i)),
      Fin.forall_fin_two.mpr ⟨lt_of_le_of_ne hx1 hcon.1.1, lt_of_le_of_ne hx2 hcon.1.2⟩⟩

/-- The fibre volume is at most the volume of the box `∏ (0, (s + δL)/κ'_i]`. -/
theorem volume_fibreSet_le {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (hκ : ∀ i, 0 < κ i) (δ γ L : ℝ) (v : Fin 2 → ℝ) :
    volume (fibreSet κ Q δ γ L v) ≤
      ∏ i, ENNReal.ofReal ((v 0 + δ * L) / κ (Sum.inl i)) := by
  calc volume (fibreSet κ Q δ γ L v)
      ≤ volume (Set.pi univ fun i ↦ Ioc 0 ((v 0 + δ * L) / κ (Sum.inl i))) := measure_mono ?_
    _ = _ := by rw [Real.volume_pi_Ioc]; simp only [sub_zero]
  intro z' hz
  have hbox := fibre2_subset_box hΔ hκ δ γ L v (fibreSet_subset_fibre2 hΔ δ γ L v hz)
  rw [mem_fibreSet_iff hΔ] at hz
  rw [Set.mem_univ_pi]
  intro i
  exact ⟨hz.1 i, (le_div_iff₀ (hκ _)).mpr (by rw [mul_comm]; exact (hbox i).2)⟩

theorem poly2_eq_fibre2_one {c₀ c₁ : Fin k → ℝ} (a₀ a₁ a₀' a₁' : ℝ) :
    poly2 c₀ c₁ a₀' a₁' = fibre2 c₀ c₁ a₀ a₁ (a₀' - a₀) (a₁' - a₁) 1 := by
  ext z
  simp [poly2, fibre2]

/-- The limiting polytope is bounded (it sits in the box `∏ [0, (κ_a + κ_b + δ)/κ'_i]`). -/
theorem isBounded_poly2_fibre {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (hκ : ∀ i, 0 < κ i) (δ γ : ℝ) :
    Bornology.IsBounded (poly2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0 + 1)
      (fibreA κ Q δ γ 1 + 1)) := by
  set w : Fin 2 → ℝ := transMat κ Q *ᵥ fun _ ↦ 1 with hw
  have e : poly2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0 + 1)
      (fibreA κ Q δ γ 1 + 1) = fibre2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0)
        (fibreA κ Q δ γ 1) (fibreB κ Q w 0) (fibreB κ Q w 1) 1 := by
    rw [poly2_eq_fibre2_one (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1), hw, fibreB_mulVec hΔ]
    simp
  rw [e]
  refine (Metric.isBounded_Icc (0 : Fin k → ℝ) fun i ↦ (w 0 + δ * 1) / κ (Sum.inl i)).subset ?_
  intro z' hz
  have hbox := fibre2_subset_box hΔ hκ δ γ 1 w hz
  rw [← Set.pi_univ_Icc, Set.mem_univ_pi]
  intro i
  exact ⟨(hbox i).1, (le_div_iff₀ (hκ _)).mpr (by rw [mul_comm]; exact (hbox i).2)⟩

/-- **The fibre-volume asymptotic**: `volume (fibreSet v) / L^k` converges to the volume of the
limiting polytope `{w ≥ 0 | c_j · w ≤ a_j}`. -/
theorem tendsto_volume_fibreSet_div {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (hκ : ∀ i, 0 < κ i) {δ γ : ℝ} (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0) (v : Fin 2 → ℝ) :
    Tendsto (fun L ↦ volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k)) atTop
      (𝓝 (volume (poly2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0)
        (fibreA κ Q δ γ 1)))) := by
  have hev : ∀ j, fibreCoef κ Q j ≠ 0 ∨ fibreA κ Q δ γ j ≠ 0 →
      ∀ᶠ L in atTop, fibreCoef κ Q j ≠ 0 ∨ fibreA κ Q δ γ j * L + fibreB κ Q v j ≠ 0 := by
    intro j hj
    rcases hj with h | h
    · exact Eventually.of_forall fun _ ↦ Or.inl h
    · filter_upwards [eventually_gt_atTop (|fibreB κ Q v j| / |fibreA κ Q δ γ j|)] with L hL
      right
      intro h0
      have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
      have habs : |fibreA κ Q δ γ j| * L = |fibreB κ Q v j| := by
        rw [add_eq_zero_iff_eq_neg] at h0
        rw [← abs_of_pos hL0, ← abs_mul, h0, abs_neg]
      rw [div_lt_iff₀ (abs_pos.mpr h), mul_comm] at hL
      exact lt_irrefl _ (habs ▸ hL)
  refine (tendsto_volume_poly2 hc₀ hc₁ (fibreB κ Q v 0) (fibreB κ Q v 1)
    (isBounded_poly2_fibre hΔ hκ δ γ)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hev 0 hc₀, hev 1 hc₁] with L hL h0 h1
  rw [volume_fibreSet_eq hΔ h0 h1, volume_fibre2 hL, mul_comm,
    ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr (pow_pos hL _)).ne' ENNReal.ofReal_ne_top]

end Laplace.Multi
