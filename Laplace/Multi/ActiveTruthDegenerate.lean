/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthTheorem
import Laplace.Multi.ActiveTruthTraceLimit

/-!
# The face theorem with an identically vanishing fibre constraint

Astra round 12, item (e), constant units. When the second fibre constraint vanishes identically
(`fibreCoef κ Q 1 = 0` and `fibreA κ Q δ γ 1 = 0`), the constraint on the fibre reads
`0 < (M⁻¹ v)_1` independently of the free coordinates and of the scale: the solved coordinate
`x_b = ρ e^{-y_b}` with `y_b = (M⁻¹ v)_1` stays of order one and its box condition survives as a
half-plane restriction in the transverse variables. The fibre volume is then the indicator of that
half-plane times the volume of the one-constraint fibre (`volume_fibreSet_eq_degenerate`), whose
scaled limit is the (now one-constraint) face polytope (`tendsto_volume_fibreSet_div_degenerate`),
and the constant of the face theorem becomes
`A w₀ ρ^{∑(r+1)}/|det M| · (∫⁻ v, vWeight(v) 1_{(M⁻¹v)_1 > 0}) · vol(F')`
(`tendsto_modelKernel_activeTruth_degenerate`) — the old transverse integral restricted to the
half-plane, which is not a Gamma value in general. The nondegenerate theorem is recovered when the
indicator is absent.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-- A vacuous second constraint: the fibre is the half-plane indicator times the one-constraint
fibre. -/
theorem volume_fibreSet_eq_degenerate {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    {δ γ L : ℝ} {v : Fin 2 → ℝ} (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 * L + fibreB κ Q v 0 ≠ 0) (hL : 0 < L) :
    volume (fibreSet κ Q δ γ L v) =
      (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1) *
        volume (fibre2 (fibreCoef κ Q 0) 0 (fibreA κ Q δ γ 0) 1 (fibreB κ Q v 0) 0 L) := by
  by_cases hb : 0 < fibreB κ Q v 1
  · rw [Set.indicator_of_mem (show fibreB κ Q v 1 ∈ Ioi 0 from hb), one_mul]
    refine le_antisymm (measure_mono fun z hz ↦ ?_) ?_
    · rw [mem_fibreSet_iff hΔ] at hz
      exact ⟨fun i ↦ (hz.1 i).le, (hz.2 0).le, by
        rw [zero_dotProduct, one_mul, add_zero]
        exact hL.le⟩
    · set N : Set (Fin k → ℝ) :=
        {x | fibreCoef κ Q 0 ⬝ᵥ x = fibreA κ Q δ γ 0 * L + fibreB κ Q v 0} ∪
          ⋃ i, {x : Fin k → ℝ | x i = 0} with hN
      have hnull : volume N = 0 :=
        measure_union_null (volume_hyperplane' hc₀)
          (measure_iUnion_null fun i ↦ volume_coordHyperplane i)
      calc volume (fibre2 (fibreCoef κ Q 0) 0 (fibreA κ Q δ γ 0) 1 (fibreB κ Q v 0) 0 L)
          ≤ volume (fibreSet κ Q δ γ L v ∪ N) := measure_mono ?_
        _ ≤ volume (fibreSet κ Q δ γ L v) + volume N := measure_union_le _ _
        _ = volume (fibreSet κ Q δ γ L v) := by rw [hnull, add_zero]
      intro x hx
      by_cases hxf : x ∈ fibreSet κ Q δ γ L v
      · exact Or.inl hxf
      · right
        rw [mem_fibreSet_iff hΔ] at hxf
        obtain ⟨hx0, hx1, -⟩ := hx
        rw [hN]
        simp only [mem_union, mem_iUnion, Set.mem_ofPred_eq]
        by_contra hcon
        push Not at hcon
        refine hxf ⟨fun i ↦ lt_of_le_of_ne (hx0 i) (Ne.symm (hcon.2 i)),
          Fin.forall_fin_two.mpr ⟨lt_of_le_of_ne hx1 hcon.1, ?_⟩⟩
        rw [hdeg.1, hdeg.2, zero_dotProduct, zero_mul, zero_add]
        exact hb
  · rw [Set.indicator_of_notMem (show fibreB κ Q v 1 ∉ Ioi 0 from hb), zero_mul]
    refine measure_mono_null (fun z hz ↦ ?_) (measure_empty (μ := volume))
    rw [mem_fibreSet_iff hΔ] at hz
    have := hz.2 1
    rw [hdeg.1, hdeg.2, zero_dotProduct, zero_mul, zero_add] at this
    exact absurd this hb

/-- Under a vacuous second constraint the face polytope is the one-constraint polytope. -/
theorem facePolytope_eq_of_degenerate {κ Q : Fin k ⊕ Fin 2 → ℝ} {δ γ : ℝ}
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0) :
    facePolytope κ Q δ γ = poly2 (fibreCoef κ Q 0) 0 (fibreA κ Q δ γ 0) 1 := by
  ext w
  simp only [facePolytope, poly2, Set.mem_ofPred_eq, hdeg.1, hdeg.2, zero_dotProduct, le_refl,
    and_true, zero_le_one]

theorem poly2_zero_right_subset {c : Fin k → ℝ} {a Y Y' : ℝ} (hY' : 0 ≤ Y') :
    poly2 c 0 a Y ⊆ poly2 c 0 a Y' := fun _ hx ↦
  ⟨hx.1, hx.2.1, by rw [zero_dotProduct]; exact hY'⟩

/-- The scaled fibre volume with a vacuous second constraint: the half-plane indicator times the
volume of the one-constraint face polytope. -/
theorem tendsto_volume_fibreSet_div_degenerate {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {δ γ : ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0) (v : Fin 2 → ℝ) :
    Tendsto (fun L ↦ volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k)) atTop
      (𝓝 ((Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1) *
        volume (facePolytope κ Q δ γ))) := by
  have hev : ∀ᶠ L in atTop,
      fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 * L + fibreB κ Q v 0 ≠ 0 := by
    rcases hc₀ with h | h
    · exact Eventually.of_forall fun _ ↦ Or.inl h
    · filter_upwards [eventually_gt_atTop (|fibreB κ Q v 0| / |fibreA κ Q δ γ 0|)] with L hL
      right
      intro h0
      have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
      have habs : |fibreA κ Q δ γ 0| * L = |fibreB κ Q v 0| := by
        rw [add_eq_zero_iff_eq_neg] at h0
        rw [← abs_of_pos hL0, ← abs_mul, h0, abs_neg]
      rw [div_lt_iff₀ (abs_pos.mpr h), mul_comm] at hL
      exact lt_irrefl _ (habs ▸ hL)
  have hbdd : Bornology.IsBounded (poly2 (fibreCoef κ Q 0) 0 (fibreA κ Q δ γ 0 + 1) (1 + 1)) := by
    have := isBounded_poly2_fibre hΔ hκ δ γ
    rw [hdeg.1, hdeg.2] at this
    exact this.subset (poly2_zero_right_subset (by norm_num))
  have hlim := tendsto_volume_poly2 hc₀ (Or.inr one_ne_zero) (fibreB κ Q v 0) 0 hbdd
  rw [facePolytope_eq_of_degenerate hdeg]
  refine (ENNReal.Tendsto.const_mul hlim (Or.inr (indicator_one_ne_top _ _))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hev] with L hL h0
  rw [volume_fibreSet_eq_degenerate hΔ hdeg h0 hL, volume_fibre2 hL,
    mul_comm (ENNReal.ofReal (L ^ k)), ← mul_assoc,
    ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr (pow_pos hL _)).ne' ENNReal.ofReal_ne_top]

theorem measurable_indicator_fibreB (κ Q : Fin k ⊕ Fin 2 → ℝ) (j : Fin 2) :
    Measurable fun v : Fin 2 → ℝ ↦
      (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v j) := by
  refine (measurable_const.indicator measurableSet_Ioi).comp ?_
  unfold fibreB
  exact (measurable_const.mul (measurable_pi_apply 0)).add
    (measurable_const.mul (measurable_pi_apply 1))

/-- Dominated convergence in the transverse variables with a vacuous second constraint. -/
theorem tendsto_lintegral_vWeight_fibre_degenerate {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {β η c₀ δ γ : ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0) (hβ : 0 < β) (hη : 0 < η) (hc : 0 < c₀)
    (hδ : 0 ≤ δ) (h₀ : ℝ) :
    Tendsto (fun L ↦ ∫⁻ v : Fin 2 → ℝ,
        vWeight β η 0 c₀ h₀ v * (volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k))) atTop
      (𝓝 (∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v *
        ((Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1) *
          volume (facePolytope κ Q δ γ)))) := by
  have hP : 0 < ∏ i, κ (Sum.inl i) := Finset.prod_pos fun i _ ↦ hκ _
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun v ↦ vWeight β η 0 c₀ h₀ v * ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i)))
    (Eventually.of_forall fun L ↦ (measurable_vWeight _ _ _ _ _).mul
      ((measurable_volume_fibreSet hΔ δ γ L).div_const _)) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact Eventually.of_forall fun v ↦
      mul_le_mul_of_nonneg_left (volume_fibreSet_div_le hΔ hκ hδ γ hL v) zero_le
  · have e : (fun v : Fin 2 → ℝ ↦
        vWeight β η 0 c₀ h₀ v * ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i))) =
        fun v ↦ ENNReal.ofReal ((sWeight β c₀ (v 0) * (|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i)) *
          hWeight η h₀ (v 1)) := by
      funext v
      rw [vWeight_zero_eq, ← ENNReal.ofReal_mul
        (mul_nonneg (sWeight_nonneg _ _ _) (hWeight_nonneg _ _ _))]
      congr 1
      ring
    rw [e, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_fin_two_mul ((integrable_sWeight_mul_pow hβ hc hδ k).div_const _)
        (integrable_hWeight hη h₀))
      (Eventually.of_forall fun v ↦ mul_nonneg
        (div_nonneg (mul_nonneg (sWeight_nonneg _ _ _) (by positivity)) hP.le)
        (hWeight_nonneg _ _ _))]
    exact ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun v ↦ ?_
    refine ENNReal.Tendsto.const_mul (tendsto_volume_fibreSet_div_degenerate hΔ hκ hc₀ hdeg v)
      (Or.inr ?_)
    rw [vWeight_zero_eq]
    exact ENNReal.ofReal_ne_top

/-- **The face theorem with an identically vanishing second fibre constraint** (constant units):
the transverse integral is restricted to the half-plane `(M⁻¹v)_1 > 0` and the face polytope has a
single constraint. -/
theorem tendsto_modelKernel_activeTruth_degenerate {ρ A B D γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat κ Q).det ≠ 0) (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A * w₀ * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹ *
        (∫⁻ v : Fin 2 → ℝ, vWeight β η 0 (B * a₀ * ρ ^ (∑ i, κ i))
          (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) v *
          (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1)).toReal *
        (volume (facePolytope κ Q δ γ)).toReal)) := by
  set c₀ := B * a₀ * ρ ^ (∑ i, κ i) with hc₀def
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  have hc : 0 < c₀ := mul_pos (mul_pos hB ha₀) (Real.rpow_pos_of_pos hρ _)
  have hF := volume_facePolytope_ne_top hΔ hκ δ γ
  set J := ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v *
    (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1) with hJ
  have hJne : J ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v) ?_
      (lintegral_mono fun v ↦ ?_)
    · rw [lintegral_vWeight_zero hβ hη hc]
      exact ENNReal.ofReal_ne_top
    · calc vWeight β η 0 c₀ h₀ v * (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1)
          ≤ vWeight β η 0 c₀ h₀ v * 1 :=
            mul_le_mul_of_nonneg_left (Set.indicator_le_self' (fun _ _ ↦ zero_le_one) _) zero_le
        _ = vWeight β η 0 c₀ h₀ v := mul_one _
  have hI : ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v *
      ((Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1) *
        volume (facePolytope κ Q δ γ)) = J * volume (facePolytope κ Q δ γ) := by
    have hm : Measurable fun v : Fin 2 → ℝ ↦ vWeight β η 0 c₀ h₀ v *
        (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1) :=
      (measurable_vWeight _ _ _ _ _).mul (measurable_indicator_fibreB κ Q 1)
    rw [hJ, ← lintegral_mul_const _ hm]
    simp_rw [mul_assoc]
  have hlim := (tendsto_lintegral_vWeight_fibre_degenerate hΔ hκ hc₀ hdeg hβ hη hc hδ h₀).comp
    Real.tendsto_log_atTop
  rw [hI] at hlim
  have hne : J * volume (facePolytope κ Q δ γ) ≠ ⊤ := ENNReal.mul_ne_top hJne hF
  have hlim2 := ((ENNReal.tendsto_toReal hne).comp hlim).const_mul
    (A * w₀ * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹)
  rw [ENNReal.toReal_mul, ← mul_assoc] at hlim2
  refine hlim2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hL : 0 < log t := Real.log_pos ht
  simp only [Function.comp]
  rw [modelKernel_const_eq_lintegral hρ hD hq ht0]
  have hB' : B * t ^ δ * a₀ * ρ ^ (∑ i, κ i) = c₀ * exp (δ * log t) := by
    rw [hc₀def, Real.rpow_def_of_pos ht0, mul_comm (log t) δ]
    ring
  rw [hB', lintegral_logIntegrand_eq (fun i ↦ hr i) hΔ, ← hh₀]
  have hJt : ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v *
      (volume (fibreSet κ Q δ γ (log t) v) / ENNReal.ofReal (log t ^ k)) =
      (∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v * volume (fibreSet κ Q δ γ (log t) v)) /
        ENNReal.ofReal (log t ^ k) := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    exact lintegral_mul_const' _ _
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hL k)).ne')
  rw [hJt]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal (pow_pos hL k).le,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), ENNReal.toReal_ofReal (exp_pos _).le]
  have e1 : t ^ (γ * p + (β * δ - η * γ)) = t ^ (γ * p) * exp ((β * δ - η * γ) * log t) := by
    rw [Real.rpow_add ht0, Real.rpow_def_of_pos ht0 (β * δ - η * γ), mul_comm (log t)]
  have e2 : t ^ (-(γ * p)) = (t ^ (γ * p))⁻¹ := Real.rpow_neg ht0.le _
  rw [e1, e2, Real.exp_neg]
  have hpos : (t ^ (γ * p)) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have hLk : log t ^ k ≠ 0 := (pow_pos hL k).ne'
  have hex : exp ((β * δ - η * γ) * log t) ≠ 0 := (exp_pos _).ne'
  have habs : |(transMat κ Q).det| ≠ 0 := abs_ne_zero.mpr hΔ
  field_simp

end Laplace.Multi
