/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthTraceTheorem

/-!
# The weighted fibre limit

Astra round 9, item 2. Over a transverse point `v`, the fibre `fibreSet κ Q δ γ L v` carries the
reconstructed log coordinate `z(z') = (z', N(v − shift(z')))` (`fibreLift`), hence the chart point
`x = ρe^{-z(z')}`. For an amplitude `Φ(x)`, bounded and measurable, with a limit `Φ₀` as `x → 0`
inside the box, `L^{-k} ∫_{fibreSet} Φ(ρe^{-z(z')}) dz' → Φ₀ · vol(F')`
(`tendsto_lintegral_fibre_weighted`): after the scaling `z' = Lw` the integrand converges to
`Φ₀ 1_{F'}(w)` for every `w` off the null boundary hyperplanes (there every reconstructed
coordinate `L(a_j − c_j·w) + b_j`, `L w_i` tends to `+∞`, so `x → 0`), with the fixed dominating
function `M 1_{F'(a+1)}`. The constant-unit fibre limit is the case `Φ ≡ 1`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix Pointwise

namespace Laplace.Multi

variable {k : ℕ}

/-- The reconstructed log coordinate over `v`: `z(z') = (z', N(v − shift(z')))`. -/
noncomputable def fibreLift (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L : ℝ) (v : Fin 2 → ℝ)
    (z' : Fin k → ℝ) : Fin k ⊕ Fin 2 → ℝ :=
  Sum.elim z' ((transMat κ Q)⁻¹ *ᵥ (v - transShift κ Q δ γ L z'))

theorem fibreLift_inl (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L : ℝ) (v : Fin 2 → ℝ) (z' : Fin k → ℝ)
    (i : Fin k) : fibreLift κ Q δ γ L v z' (Sum.inl i) = z' i := rfl

theorem fibreLift_inr (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L : ℝ) (v : Fin 2 → ℝ) (z' : Fin k → ℝ)
    (j : Fin 2) : fibreLift κ Q δ γ L v z' (Sum.inr j) =
      fibreA κ Q δ γ j * L + fibreB κ Q v j - fibreCoef κ Q j ⬝ᵥ z' := by
  unfold fibreLift
  rw [Sum.elim_inr, inv_mulVec_sub_shift]

theorem measurable_fibreLift (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L : ℝ) (v : Fin 2 → ℝ) :
    Measurable (fibreLift κ Q δ γ L v) := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  cases i with
  | inl i => exact measurable_pi_apply i
  | inr j =>
    simp only [fibreLift_inr]
    exact (measurable_const.sub (measurable_dotProduct_left _))

/-- Scaling on `Fin k → ℝ`: `∫⁻ y, F (L • y) = L^{-k} ∫⁻ u, F u`. -/
theorem lintegral_comp_smul_fin {L : ℝ} (hL : 0 < L) {F : (Fin k → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ y : Fin k → ℝ, F (L • y) = ENNReal.ofReal ((L ^ k)⁻¹) * ∫⁻ u, F u := by
  have hdet : (L • (1 : Matrix (Fin k) (Fin k) ℝ)).det = L ^ k := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have h := lintegral_comp_mulVec_add (L • (1 : Matrix (Fin k) (Fin k) ℝ))
    (by rw [hdet]; exact (pow_pos hL k).ne') 0 hF
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, add_zero, hdet, abs_pow, abs_of_pos hL,
    ← inv_pow] at h
  rw [h, inv_pow]

/-- The chart point `ρe^{-z}` lies in the box iff `z > 0`. -/
theorem negExpMap_mem_box_iff {ρ : ℝ} (hρ : 0 < ρ) (z : Fin k ⊕ Fin 2 → ℝ) :
    negExpMap ρ z ∈ Set.pi univ (fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ) ↔ ∀ i, 0 < z i := by
  rw [← image_negExpMap_orthant hρ, (negExpMap_injective hρ).mem_set_image]
  simp only [Set.mem_univ_pi, mem_Ioi]

/-- **The weighted fibre limit.** -/
theorem tendsto_lintegral_fibre_weighted {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {δ γ : ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0) (v : Fin 2 → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {Φ : (Fin k ⊕ Fin 2 → ℝ) → ℝ} {M Φ₀ : ℝ} (hΦm : Measurable Φ)
    (hΦb : ∀ x, 0 ≤ Φ x ∧ Φ x ≤ M)
    (hΦ : Tendsto Φ (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 Φ₀)) :
    Tendsto (fun L ↦ (∫⁻ z' in fibreSet κ Q δ γ L v,
        ENNReal.ofReal (Φ (negExpMap ρ (fibreLift κ Q δ γ L v z')))) / ENNReal.ofReal (L ^ k))
      atTop (𝓝 (ENNReal.ofReal Φ₀ * volume (facePolytope κ Q δ γ))) := by
  set c₀ := fibreCoef κ Q 0 with hc₀def
  set c₁ := fibreCoef κ Q 1 with hc₁def
  set a₀ := fibreA κ Q δ γ 0 with ha₀def
  set a₁ := fibreA κ Q δ γ 1 with ha₁def
  set b₀ := fibreB κ Q v 0 with hb₀def
  set b₁ := fibreB κ Q v 1 with hb₁def
  have hM : 0 ≤ M := (hΦb 0).1.trans (hΦb 0).2
  -- the scaled integrand
  set G : ℝ → (Fin k → ℝ) → ℝ≥0∞ := fun L w ↦ (fibreSet κ Q δ γ L v).indicator
    (fun z' ↦ ENNReal.ofReal (Φ (negExpMap ρ (fibreLift κ Q δ γ L v z')))) (L • w) with hG
  have hGm : ∀ L, Measurable (G L) := fun L ↦ by
    rw [hG]
    beta_reduce
    exact ((ENNReal.measurable_ofReal.comp (hΦm.comp ((continuous_pi fun i ↦ by
      unfold negExpMap; fun_prop : Continuous (negExpMap ρ)).measurable.comp
      (measurable_fibreLift κ Q δ γ L v)))).indicator (measurableSet_fibreSet hΔ δ γ L v)).comp
      (measurable_const_smul L : Measurable fun x : Fin k → ℝ ↦ L • x)
  -- the scaled form of the fibre integral
  have hscale : ∀ᶠ L in atTop, (∫⁻ z' in fibreSet κ Q δ γ L v,
      ENNReal.ofReal (Φ (negExpMap ρ (fibreLift κ Q δ γ L v z')))) / ENNReal.ofReal (L ^ k) =
      ∫⁻ w, G L w := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [← lintegral_indicator (measurableSet_fibreSet hΔ δ γ L v), hG]
    simp only
    rw [lintegral_comp_smul_fin hL (F := fun z' ↦ (fibreSet κ Q δ γ L v).indicator
      (fun z' ↦ ENNReal.ofReal (Φ (negExpMap ρ (fibreLift κ Q δ γ L v z')))) z')
      ((ENNReal.measurable_ofReal.comp (hΦm.comp ((continuous_pi fun i ↦ by
        unfold negExpMap; fun_prop : Continuous (negExpMap ρ)).measurable.comp
        (measurable_fibreLift κ Q δ γ L v)))).indicator (measurableSet_fibreSet hΔ δ γ L v)),
      ENNReal.ofReal_inv_of_pos (pow_pos hL k), div_eq_mul_inv, mul_comm]
  refine Tendsto.congr' (EventuallyEq.symm hscale) ?_
  -- dominated convergence
  rw [show facePolytope κ Q δ γ = poly2 c₀ c₁ a₀ a₁ from rfl,
    ← lintegral_indicator_const measurableSet_poly2 (ENNReal.ofReal Φ₀)]
  refine tendsto_lintegral_filter_of_dominated_convergence
    ((poly2 c₀ c₁ (a₀ + 1) (a₁ + 1)).indicator fun _ ↦ ENNReal.ofReal M)
    (Eventually.of_forall hGm) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (max 1 (max |b₀| |b₁|))] with L hL
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
    have hL0 : 0 < L := zero_lt_one.trans_le hL1
    have hb : ∀ b : ℝ, |b| ≤ L → b / L ≤ 1 := fun b hbL ↦ by
      rw [div_le_one hL0]
      exact (le_abs_self b).trans hbL
    refine Eventually.of_forall fun w ↦ ?_
    rw [hG]
    simp only
    by_cases hw : L • w ∈ fibreSet κ Q δ γ L v
    · rw [Set.indicator_of_mem hw]
      rw [mem_fibreSet_iff hΔ] at hw
      have hwP : w ∈ poly2 c₀ c₁ (a₀ + 1) (a₁ + 1) := by
        refine ⟨fun i ↦ ?_, ?_, ?_⟩
        · have := hw.1 i
          rw [Pi.smul_apply, smul_eq_mul] at this
          exact (pos_of_mul_pos_right this hL0.le).le
        · have := hw.2 0
          rw [dotProduct_smul, smul_eq_mul] at this
          have h2 : c₀ ⬝ᵥ w < a₀ + b₀ / L := by
            rw [show a₀ + b₀ / L = (a₀ * L + b₀) / L by field_simp, lt_div_iff₀ hL0, mul_comm]
            exact this
          exact h2.le.trans (add_le_add le_rfl
            (hb b₀ ((le_max_left _ _).trans ((le_max_right _ _).trans hL))))
        · have := hw.2 1
          rw [dotProduct_smul, smul_eq_mul] at this
          have h2 : c₁ ⬝ᵥ w < a₁ + b₁ / L := by
            rw [show a₁ + b₁ / L = (a₁ * L + b₁) / L by field_simp, lt_div_iff₀ hL0, mul_comm]
            exact this
          exact h2.le.trans (add_le_add le_rfl
            (hb b₁ ((le_max_right _ _).trans ((le_max_right _ _).trans hL))))
      rw [Set.indicator_of_mem hwP]
      exact ENNReal.ofReal_le_ofReal (hΦb _).2
    · rw [Set.indicator_of_notMem hw]
      exact zero_le
  · rw [lintegral_indicator_const measurableSet_poly2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (isBounded_poly2_fibre hΔ hκ δ γ).measure_lt_top.ne
  · have hnull : volume ({x : Fin k → ℝ | c₀ ⬝ᵥ x = a₀} ∪ {x | c₁ ⬝ᵥ x = a₁} ∪
        ⋃ i, {x : Fin k → ℝ | x i = 0}) = 0 :=
      measure_union_null (measure_union_null (volume_hyperplane' hc₀) (volume_hyperplane' hc₁))
        (measure_iUnion_null fun i ↦ volume_coordHyperplane i)
    filter_upwards [compl_mem_ae_iff.mpr hnull] with w hw
    simp only [mem_compl_iff, mem_union, mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at hw
    obtain ⟨⟨hw1, hw2⟩, hw0⟩ := hw
    by_cases hwP : w ∈ poly2 c₀ c₁ a₀ a₁
    · -- the interior case: the reconstructed coordinates tend to `+∞`
      rw [Set.indicator_of_mem hwP]
      have hlt0 : c₀ ⬝ᵥ w < a₀ := lt_of_le_of_ne hwP.2.1 hw1
      have hlt1 : c₁ ⬝ᵥ w < a₁ := lt_of_le_of_ne hwP.2.2 hw2
      have hwi : ∀ i, 0 < w i := fun i ↦ lt_of_le_of_ne (hwP.1 i) (Ne.symm (hw0 i))
      -- eventually in the fibre
      have hmem : ∀ᶠ L in atTop, L • w ∈ fibreSet κ Q δ γ L v := by
        have h0 : Tendsto (fun L ↦ L * (a₀ - c₀ ⬝ᵥ w) + b₀) atTop atTop :=
          tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const (sub_pos.mpr hlt0))
        have h1 : Tendsto (fun L ↦ L * (a₁ - c₁ ⬝ᵥ w) + b₁) atTop atTop :=
          tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const (sub_pos.mpr hlt1))
        filter_upwards [eventually_gt_atTop (0 : ℝ), h0.eventually_gt_atTop 0,
          h1.eventually_gt_atTop 0] with L hL hL0 hL1
        rw [mem_fibreSet_iff hΔ]
        refine ⟨fun i ↦ by rw [Pi.smul_apply, smul_eq_mul]; exact mul_pos hL (hwi i),
          Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
        · rw [dotProduct_smul, smul_eq_mul]; linarith
        · rw [dotProduct_smul, smul_eq_mul]; linarith
      -- the chart point tends to `0` inside the box
      have hz : Tendsto (fun L ↦ negExpMap ρ (fibreLift κ Q δ γ L v (L • w))) atTop
          (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) := by
        have hcoord : ∀ i, Tendsto (fun L ↦ fibreLift κ Q δ γ L v (L • w) i) atTop atTop := by
          intro i
          cases i with
          | inl i =>
            simp only [fibreLift_inl, Pi.smul_apply, smul_eq_mul]
            exact tendsto_id.atTop_mul_const (hwi i)
          | inr j =>
            simp only [fibreLift_inr, dotProduct_smul, smul_eq_mul]
            have : (fun L ↦ fibreA κ Q δ γ j * L + fibreB κ Q v j - L * (fibreCoef κ Q j ⬝ᵥ w)) =
                fun L ↦ L * (fibreA κ Q δ γ j - fibreCoef κ Q j ⬝ᵥ w) + fibreB κ Q v j := by
              funext L; ring
            rw [this]
            refine tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const ?_)
            fin_cases j
            · exact sub_pos.mpr hlt0
            · exact sub_pos.mpr hlt1
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · refine tendsto_pi_nhds.mpr fun i ↦ ?_
          simp only [negExpMap, Pi.zero_apply]
          have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hcoord i)).const_mul ρ
          simpa using this
        · filter_upwards [eventually_all.mpr fun i ↦ (hcoord i).eventually_gt_atTop 0] with L hL
          exact (negExpMap_mem_box_iff hρ _).mpr hL
      have hΦL := hΦ.comp hz
      refine (ENNReal.tendsto_ofReal hΦL).congr' ?_
      filter_upwards [hmem] with L hL
      rw [hG]
      simp only
      rw [Set.indicator_of_mem hL]
      rfl
    · rw [Set.indicator_of_notMem hwP]
      refine tendsto_const_nhds.congr' ?_
      have hcases : (∃ i, w i < 0) ∨ a₀ < c₀ ⬝ᵥ w ∨ a₁ < c₁ ⬝ᵥ w := by
        by_contra h
        push Not at h
        exact hwP ⟨h.1, h.2.1, h.2.2⟩
      have hnot : ∀ᶠ L in atTop, L • w ∉ fibreSet κ Q δ γ L v := by
        rcases hcases with ⟨i, hi⟩ | h | h
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL hm
          rw [mem_fibreSet_iff hΔ] at hm
          have := hm.1 i
          rw [Pi.smul_apply, smul_eq_mul] at this
          exact absurd (pos_of_mul_pos_right this hL.le) (not_lt.mpr hi.le)
        · have h0 : Tendsto (fun L ↦ L * (a₀ - c₀ ⬝ᵥ w) + b₀) atTop atBot :=
            tendsto_atBot_add_const_right _ _ (tendsto_id.atTop_mul_const_of_neg (sub_neg.mpr h))
          filter_upwards [h0.eventually_lt_atBot 0] with L hL hm
          rw [mem_fibreSet_iff hΔ] at hm
          have := hm.2 0
          rw [dotProduct_smul, smul_eq_mul] at this
          linarith
        · have h1 : Tendsto (fun L ↦ L * (a₁ - c₁ ⬝ᵥ w) + b₁) atTop atBot :=
            tendsto_atBot_add_const_right _ _ (tendsto_id.atTop_mul_const_of_neg (sub_neg.mpr h))
          filter_upwards [h1.eventually_lt_atBot 0] with L hL hm
          rw [mem_fibreSet_iff hΔ] at hm
          have := hm.2 1
          rw [dotProduct_smul, smul_eq_mul] at this
          linarith
      filter_upwards [hnot] with L hL
      rw [hG]
      simp only
      rw [Set.indicator_of_notMem hL]

end Laplace.Multi
