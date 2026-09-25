/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthDegenerate
import Laplace.Multi.ActiveTruthGeneral

/-!
# The boundary regime with general units: the partial trace

Astra round 13, item 1. In the boundary regime `c_1 = a_1 = 0` (`ActiveTruthDegenerate.lean`) the
solved coordinate `x_b = ρ e^{-(M⁻¹v)_1}` (`survCoord`) stays of order one while the other active
coordinates collapse to the wall. With general units `W(x, u)`, `a(x, u)` the trace is therefore a
**partial** trace: for fixed `z, u ∈ (0, ρ)`, `W(x, u) → W_tr(z, u)` as the coordinates other than
`inr 1` tend to `0` inside the box with the `inr 1` coordinate held at `z`
(`Function.update y (inr 1) z`, `y → 0`), likewise `a`. The transverse weight is then
`vWeightTD v = 1_{h > h₀} 1_{(M⁻¹v)_1 > 0} W_tr(z(v), u(v)) e^{-βs} e^{-ηh}
e^{-c_ρ a_tr(z(v), u(v)) e^{-s}}` with `z(v) = ρ e^{-(M⁻¹v)_1}`, `u(v) = truthOf h`: the phase unit
stays inside the transverse exponential (it cannot be pulled out as a power since the surviving
coordinate depends on `v`), and the limit is
`A ρ^{∑(r+1)}/|det M| · (∫⁻ vWeightTD).toReal · vol(F')`
(`tendsto_modelKernel_general_degenerate`). The weighted fibre limit with the surviving coordinate
(`tendsto_lintegral_fibre_weighted_degenerate`) is the nondegenerate one with the second
hyperplane dropped, the path through the fibre having its `inr 1` coordinate exactly equal to
`z(v)`; the same domination (`W ≤ W_*`, `a ≥ a_-`) as in the nondegenerate case applies. Constant
traces recover `tendsto_modelKernel_activeTruth_degenerate`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-- The surviving solved coordinate `ρ e^{-(M⁻¹v)_1}` of the boundary regime. -/
noncomputable def survCoord (ρ : ℝ) (κ Q : Fin k ⊕ Fin 2 → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  ρ * exp (-fibreB κ Q v 1)

theorem survCoord_mem_Ioo {ρ : ℝ} (hρ : 0 < ρ) {κ Q : Fin k ⊕ Fin 2 → ℝ} {v : Fin 2 → ℝ}
    (hb : 0 < fibreB κ Q v 1) : survCoord ρ κ Q v ∈ Ioo 0 ρ := by
  unfold survCoord
  refine ⟨by positivity, ?_⟩
  have : exp (-fibreB κ Q v 1) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  exact mul_lt_of_lt_one_right hρ this

theorem continuous_fibreB (κ Q : Fin k ⊕ Fin 2 → ℝ) (j : Fin 2) :
    Continuous fun v : Fin 2 → ℝ ↦ fibreB κ Q v j := by
  unfold fibreB
  fun_prop

theorem continuous_survCoord (ρ : ℝ) (κ Q : Fin k ⊕ Fin 2 → ℝ) :
    Continuous (survCoord ρ κ Q) := by
  unfold survCoord
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_fibreB κ Q 1).neg)

/-- With a vacuous second constraint and `(M⁻¹v)_1 ≤ 0` the fibre is empty. -/
theorem fibreSet_eq_empty_of_degenerate {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    {δ γ L : ℝ} {v : Fin 2 → ℝ} (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0)
    (hb : fibreB κ Q v 1 ≤ 0) : fibreSet κ Q δ γ L v = ∅ := by
  ext z'
  simp only [mem_empty_iff_false, iff_false]
  intro hz
  rw [mem_fibreSet_iff hΔ] at hz
  have := hz.2 1
  rw [hdeg.1, hdeg.2, zero_dotProduct, zero_mul, zero_add] at this
  exact absurd this (not_lt.mpr hb)

/-- The reconstructed log coordinate with the surviving coordinate replaced by `L`. -/
theorem negExpMap_fibreLift_eq_update {ρ : ℝ} {κ Q : Fin k ⊕ Fin 2 → ℝ} {δ γ : ℝ}
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0) (L : ℝ) (v : Fin 2 → ℝ)
    (z' : Fin k → ℝ) :
    negExpMap ρ (fibreLift κ Q δ γ L v z') =
      Function.update (negExpMap ρ (Function.update (fibreLift κ Q δ γ L v z') (Sum.inr 1) L))
        (Sum.inr 1) (survCoord ρ κ Q v) := by
  funext i
  by_cases hi : i = Sum.inr 1
  · subst hi
    rw [Function.update_self]
    unfold negExpMap survCoord
    rw [fibreLift_inr, hdeg.1, hdeg.2, zero_dotProduct, zero_mul, zero_add, sub_zero]
  · rw [Function.update_of_ne hi]
    unfold negExpMap
    rw [Function.update_of_ne hi]

/-- **The weighted fibre limit with a surviving coordinate.** -/
theorem tendsto_lintegral_fibre_weighted_degenerate {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {δ γ : ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0) {v : Fin 2 → ℝ}
    (hb : 0 < fibreB κ Q v 1) {ρ : ℝ} (hρ : 0 < ρ)
    {Φ : (Fin k ⊕ Fin 2 → ℝ) → ℝ} {M Φ₀ : ℝ} (hΦm : Measurable Φ)
    (hΦb : ∀ x, 0 ≤ Φ x ∧ Φ x ≤ M)
    (hΦ : Tendsto (fun y ↦ Φ (Function.update y (Sum.inr 1) (survCoord ρ κ Q v)))
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 Φ₀)) :
    Tendsto (fun L ↦ (∫⁻ z' in fibreSet κ Q δ γ L v,
        ENNReal.ofReal (Φ (negExpMap ρ (fibreLift κ Q δ γ L v z')))) / ENNReal.ofReal (L ^ k))
      atTop (𝓝 (ENNReal.ofReal Φ₀ * volume (facePolytope κ Q δ γ))) := by
  set c₀ := fibreCoef κ Q 0 with hc₀def
  set a₀ := fibreA κ Q δ γ 0 with ha₀def
  set b₀ := fibreB κ Q v 0 with hb₀def
  set b₁ := fibreB κ Q v 1 with hb₁def
  have hM : 0 ≤ M := (hΦb 0).1.trans (hΦb 0).2
  -- the scaled integrand
  set G : ℝ → (Fin k → ℝ) → ℝ≥0∞ := fun L w ↦ (fibreSet κ Q δ γ L v).indicator
    (fun z' ↦ ENNReal.ofReal (Φ (negExpMap ρ (fibreLift κ Q δ γ L v z')))) (L • w) with hG
  have hGm : ∀ L, Measurable (G L) := fun L ↦ by
    rw [hG]
    beta_reduce
    exact ((ENNReal.measurable_ofReal.comp (hΦm.comp ((continuous_negExpMap ρ).measurable.comp
      (measurable_fibreLift κ Q δ γ L v)))).indicator (measurableSet_fibreSet hΔ δ γ L v)).comp
      (measurable_const_smul L : Measurable fun x : Fin k → ℝ ↦ L • x)
  have hscale : ∀ᶠ L in atTop, (∫⁻ z' in fibreSet κ Q δ γ L v,
      ENNReal.ofReal (Φ (negExpMap ρ (fibreLift κ Q δ γ L v z')))) / ENNReal.ofReal (L ^ k) =
      ∫⁻ w, G L w := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [← lintegral_indicator (measurableSet_fibreSet hΔ δ γ L v), hG]
    simp only
    rw [lintegral_comp_smul_fin hL (F := fun z' ↦ (fibreSet κ Q δ γ L v).indicator
      (fun z' ↦ ENNReal.ofReal (Φ (negExpMap ρ (fibreLift κ Q δ γ L v z')))) z')
      ((ENNReal.measurable_ofReal.comp (hΦm.comp ((continuous_negExpMap ρ).measurable.comp
        (measurable_fibreLift κ Q δ γ L v)))).indicator (measurableSet_fibreSet hΔ δ γ L v)),
      ENNReal.ofReal_inv_of_pos (pow_pos hL k), div_eq_mul_inv, mul_comm]
  refine Tendsto.congr' (EventuallyEq.symm hscale) ?_
  -- dominated convergence
  rw [facePolytope_eq_of_degenerate hdeg,
    ← lintegral_indicator_const measurableSet_poly2 (ENNReal.ofReal Φ₀)]
  have hbdd : Bornology.IsBounded (poly2 c₀ 0 (a₀ + 1) (1 + 1)) := by
    have := isBounded_poly2_fibre hΔ hκ δ γ
    rw [hdeg.1, hdeg.2] at this
    exact this.subset (poly2_zero_right_subset (by norm_num))
  refine tendsto_lintegral_filter_of_dominated_convergence
    ((poly2 c₀ 0 (a₀ + 1) (1 + 1)).indicator fun _ ↦ ENNReal.ofReal M)
    (Eventually.of_forall hGm) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (max 1 |b₀|)] with L hL
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
    have hL0 : 0 < L := zero_lt_one.trans_le hL1
    refine Eventually.of_forall fun w ↦ ?_
    rw [hG]
    simp only
    by_cases hw : L • w ∈ fibreSet κ Q δ γ L v
    · rw [Set.indicator_of_mem hw]
      rw [mem_fibreSet_iff hΔ] at hw
      have hwP : w ∈ poly2 c₀ 0 (a₀ + 1) (1 + 1) := by
        refine ⟨fun i ↦ ?_, ?_, ?_⟩
        · have := hw.1 i
          rw [Pi.smul_apply, smul_eq_mul] at this
          exact (pos_of_mul_pos_right this hL0.le).le
        · have := hw.2 0
          rw [dotProduct_smul, smul_eq_mul] at this
          have h2 : c₀ ⬝ᵥ w < a₀ + b₀ / L := by
            rw [show a₀ + b₀ / L = (a₀ * L + b₀) / L by field_simp, lt_div_iff₀ hL0, mul_comm]
            exact this
          have h3 : b₀ / L ≤ 1 := by
            rw [div_le_one hL0]
            exact (le_abs_self b₀).trans ((le_max_right _ _).trans hL)
          exact h2.le.trans (add_le_add le_rfl h3)
        · rw [zero_dotProduct]; norm_num
      rw [Set.indicator_of_mem hwP]
      exact ENNReal.ofReal_le_ofReal (hΦb _).2
    · rw [Set.indicator_of_notMem hw]
      exact zero_le
  · rw [lintegral_indicator_const measurableSet_poly2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbdd.measure_lt_top.ne
  · have hnull : volume ({x : Fin k → ℝ | c₀ ⬝ᵥ x = a₀} ∪ ⋃ i, {x : Fin k → ℝ | x i = 0}) = 0 :=
      measure_union_null (volume_hyperplane' hc₀)
        (measure_iUnion_null fun i ↦ volume_coordHyperplane i)
    filter_upwards [compl_mem_ae_iff.mpr hnull] with w hw
    simp only [mem_compl_iff, mem_union, mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at hw
    obtain ⟨hw1, hw0⟩ := hw
    by_cases hwP : w ∈ poly2 c₀ 0 a₀ 1
    · -- the interior case: the collapsing coordinates tend to `+∞`, the surviving one is fixed
      rw [Set.indicator_of_mem hwP]
      have hlt0 : c₀ ⬝ᵥ w < a₀ := lt_of_le_of_ne hwP.2.1 hw1
      have hwi : ∀ i, 0 < w i := fun i ↦ lt_of_le_of_ne (hwP.1 i) (Ne.symm (hw0 i))
      have hmem : ∀ᶠ L in atTop, L • w ∈ fibreSet κ Q δ γ L v := by
        have h0 : Tendsto (fun L ↦ L * (a₀ - c₀ ⬝ᵥ w) + b₀) atTop atTop :=
          tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const (sub_pos.mpr hlt0))
        filter_upwards [eventually_gt_atTop (0 : ℝ), h0.eventually_gt_atTop 0] with L hL hL0
        rw [mem_fibreSet_iff hΔ]
        refine ⟨fun i ↦ by rw [Pi.smul_apply, smul_eq_mul]; exact mul_pos hL (hwi i),
          Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
        · rw [dotProduct_smul, smul_eq_mul]; linarith
        · rw [hdeg.1, hdeg.2, zero_dotProduct, zero_mul, zero_add]; exact hb
      -- the path with the surviving coordinate replaced by `L` tends to `0` inside the box
      set zL : ℝ → Fin k ⊕ Fin 2 → ℝ := fun L ↦
        Function.update (fibreLift κ Q δ γ L v (L • w)) (Sum.inr 1) L with hzL
      have hcoord : ∀ i, Tendsto (fun L ↦ zL L i) atTop atTop := by
        intro i
        by_cases hi : i = Sum.inr 1
        · subst hi
          simp only [hzL, Function.update_self]
          exact tendsto_id
        · simp only [hzL, Function.update_of_ne hi]
          cases i with
          | inl i =>
            simp only [fibreLift_inl, Pi.smul_apply, smul_eq_mul]
            exact tendsto_id.atTop_mul_const (hwi i)
          | inr j =>
            have hj : j = 0 := by
              fin_cases j
              · rfl
              · exact absurd rfl hi
            subst hj
            simp only [fibreLift_inr, dotProduct_smul, smul_eq_mul]
            have : (fun L ↦ fibreA κ Q δ γ 0 * L + fibreB κ Q v 0 - L * (fibreCoef κ Q 0 ⬝ᵥ w)) =
                fun L ↦ L * (a₀ - c₀ ⬝ᵥ w) + b₀ := by
              funext L; ring
            rw [this]
            exact tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const (sub_pos.mpr hlt0))
      have hz : Tendsto (fun L ↦ negExpMap ρ (zL L)) atTop
          (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) := by
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
      rw [Set.indicator_of_mem hL, negExpMap_fibreLift_eq_update hdeg]
      rfl
    · rw [Set.indicator_of_notMem hwP]
      refine tendsto_const_nhds.congr' ?_
      have hcases : (∃ i, w i < 0) ∨ a₀ < c₀ ⬝ᵥ w := by
        by_contra h
        push Not at h
        exact hwP ⟨h.1, h.2, by rw [zero_dotProduct]; exact zero_le_one⟩
      have hnot : ∀ᶠ L in atTop, L • w ∉ fibreSet κ Q δ γ L v := by
        rcases hcases with ⟨i, hi⟩ | h
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
      filter_upwards [hnot] with L hL
      rw [hG]
      simp only
      rw [Set.indicator_of_notMem hL]

/-! ### The partial trace of the amplitude -/

/-- The amplitude converges to its partial trace as the collapsing coordinates tend to `0` with the
surviving coordinate held at `z(v)`. -/
theorem ampG_tendsto_degenerate {ρ D q c₀ : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    {κ Q : Fin k ⊕ Fin 2 → ℝ} {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} {Wtr atr : ℝ → ℝ → ℝ}
    (hWtr : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ,
      Tendsto (fun y ↦ W (Function.update y (Sum.inr 1) z) u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr z u)))
    (hatr : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ,
      Tendsto (fun y ↦ a (Function.update y (Sum.inr 1) z) u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr z u)))
    {v : Fin 2 → ℝ} (hv : -(q * log (ρ / D) + (∑ i, Q i) * log ρ) < v 1)
    (hb : 0 < fibreB κ Q v 1) :
    Tendsto (fun y ↦ ampG ρ D q c₀ Q W a v (Function.update y (Sum.inr 1) (survCoord ρ κ Q v)))
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0)
      (𝓝 (Wtr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) *
        exp (-(c₀ * atr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) * exp (-v 0))))) := by
  have hu := truthOf_mem_Ioo hρ hD hq Q hv
  have hz := survCoord_mem_Ioo hρ hb
  have h2 : Tendsto (fun y ↦ exp (-(c₀ * a (Function.update y (Sum.inr 1) (survCoord ρ κ Q v))
      (truthOf ρ D q Q (v 1)) * exp (-v 0))))
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0)
      (𝓝 (exp (-(c₀ * atr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) * exp (-v 0))))) :=
    (Real.continuous_exp.tendsto _).comp
      (((hatr _ hz _ hu).const_mul c₀).mul_const (exp (-v 0))).neg
  exact (hWtr _ hz _ hu).mul h2

/-- The transverse weight of the boundary regime with general units: the traces are evaluated at
the surviving coordinate `z(v)` and the truth coordinate `u(v)`, on the half-plane
`(M⁻¹v)_1 > 0`. -/
noncomputable def vWeightTD (ρ D q : ℝ) (κ Q : Fin k ⊕ Fin 2 → ℝ) (β η c₀ h₀ : ℝ)
    (Wtr atr : ℝ → ℝ → ℝ) (v : Fin 2 → ℝ) : ℝ≥0∞ :=
  (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
    (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) (fibreB κ Q v 1) *
    ENNReal.ofReal (Wtr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) *
      exp (-(β * v 0 + η * v 1 + 0)) *
      exp (-(c₀ * atr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) * exp (-v 0))))

theorem measurable_vWeightTD (ρ D q : ℝ) (κ Q : Fin k ⊕ Fin 2 → ℝ) (β η c₀ h₀ : ℝ)
    {Wtr atr : ℝ → ℝ → ℝ} (hW : Measurable (Function.uncurry Wtr))
    (ha : Measurable (Function.uncurry atr)) :
    Measurable (vWeightTD ρ D q κ Q β η c₀ h₀ Wtr atr) := by
  unfold vWeightTD
  have hpair : Measurable fun v : Fin 2 → ℝ ↦ (survCoord ρ κ Q v, truthOf ρ D q Q (v 1)) :=
    (continuous_survCoord ρ κ Q).measurable.prodMk
      ((continuous_truthOf ρ D q Q).measurable.comp (measurable_pi_apply 1))
  refine (((measurable_const.indicator measurableSet_Ioi).comp (measurable_pi_apply 1)).mul
    (measurable_indicator_fibreB κ Q 1)).mul (ENNReal.measurable_ofReal.comp ?_)
  refine ((hW.comp hpair).mul (Real.measurable_exp.comp (Measurable.neg
    (((measurable_const.mul (measurable_pi_apply 0)).add
      (measurable_const.mul (measurable_pi_apply 1))).add measurable_const)))).mul
    (Real.measurable_exp.comp ?_)
  exact ((measurable_const.mul (ha.comp hpair)).mul
    (Real.measurable_exp.comp (measurable_pi_apply 0).neg)).neg

theorem vWeightTD_ne_top (ρ D q : ℝ) (κ Q : Fin k ⊕ Fin 2 → ℝ) (β η c₀ h₀ : ℝ)
    (Wtr atr : ℝ → ℝ → ℝ) (v : Fin 2 → ℝ) : vWeightTD ρ D q κ Q β η c₀ h₀ Wtr atr v ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (indicator_one_ne_top _ _) (indicator_one_ne_top _ _))
    ENNReal.ofReal_ne_top

/-- **Domination**: the partial-trace weight is at most `W_*` times the constant-unit weight at
`c₀ a_-`. -/
theorem vWeightTD_le {ρ D q : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    {κ Q : Fin k ⊕ Fin 2 → ℝ} {β η c₀ Wstar amin : ℝ} (hc : 0 < c₀) {Wtr atr : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ Wtr z u ∧ Wtr z u ≤ Wstar)
    (ha : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ, amin ≤ atr z u) (hWs : 0 ≤ Wstar)
    (v : Fin 2 → ℝ) :
    vWeightTD ρ D q κ Q β η c₀ (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) Wtr atr v ≤
      ENNReal.ofReal Wstar *
        vWeight β η 0 (c₀ * amin) (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) v := by
  unfold vWeightTD vWeight
  by_cases hv : v 1 ∈ Ioi (-(q * log (ρ / D) + (∑ i, Q i) * log ρ))
  · by_cases hb : fibreB κ Q v 1 ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hb, one_mul, one_mul, one_mul,
        ← ENNReal.ofReal_mul hWs]
      refine ENNReal.ofReal_le_ofReal ?_
      have hu := truthOf_mem_Ioo hρ hD hq Q hv
      have hz := survCoord_mem_Ioo hρ hb
      have h1 := hw _ hz _ hu
      have h2 := ha _ hz _ hu
      have hE : 0 ≤ exp (-(β * v 0 + η * v 1 + 0)) := (exp_pos _).le
      have h3 : exp (-(c₀ * atr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) * exp (-v 0))) ≤
          exp (-(c₀ * amin * exp (-v 0))) := by
        rw [Real.exp_le_exp, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc.le) (exp_pos _).le
      calc Wtr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) * exp (-(β * v 0 + η * v 1 + 0)) *
            exp (-(c₀ * atr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) * exp (-v 0)))
          ≤ Wstar * exp (-(β * v 0 + η * v 1 + 0)) * exp (-(c₀ * amin * exp (-v 0))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h1.2 hE) h3 (exp_pos _).le (by positivity)
        _ = Wstar * (exp (-(β * v 0 + η * v 1 + 0)) * exp (-(c₀ * amin * exp (-v 0)))) := by
            ring
    · rw [Set.indicator_of_notMem hb, mul_zero, zero_mul]
      exact zero_le
  · rw [Set.indicator_of_notMem hv, zero_mul, zero_mul]
    exact zero_le

/-- **The transverse limit of the boundary regime with general units.** -/
theorem tendsto_lintegral_innerKvG_degenerate {ρ D q : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {β η c₀ δ γ : ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0) (hβ : 0 < β) (hη : 0 < η) (hc : 0 < c₀)
    (hδ : 0 ≤ δ) {Wstar amin : ℝ} (hamin : 0 < amin) {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    (hWm : Measurable (Function.uncurry W)) (ham : Measurable (Function.uncurry a))
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) {Wtr atr : ℝ → ℝ → ℝ}
    (hWtr : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ,
      Tendsto (fun y ↦ W (Function.update y (Sum.inr 1) z) u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr z u)))
    (hatr : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ,
      Tendsto (fun y ↦ a (Function.update y (Sum.inr 1) z) u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr z u))) :
    Tendsto (fun L ↦ ∫⁻ v : Fin 2 → ℝ, (∫⁻ z' : Fin k → ℝ, innerKvG ρ D q κ Q δ γ L β η 0 c₀
        (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) W a z' v) / ENNReal.ofReal (L ^ k)) atTop
      (𝓝 (∫⁻ v : Fin 2 → ℝ, vWeightTD ρ D q κ Q β η c₀
        (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) Wtr atr v * volume (facePolytope κ Q δ γ))) := by
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  have hP : 0 < ∏ i, κ (Sum.inl i) := Finset.prod_pos fun i _ ↦ hκ _
  have hca : 0 < c₀ * amin := mul_pos hc hamin
  have hW : 0 ≤ Wstar := (hWb 0 0).1.trans (hWb 0 0).2
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun v ↦ ENNReal.ofReal Wstar * (vWeight β η 0 (c₀ * amin) h₀ v *
      ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i))))
    (Eventually.of_forall fun L ↦ ?_) ?_ ?_ ?_
  · refine Measurable.div_const ?_ _
    exact Measurable.lintegral_prod_right'
      ((measurable_innerKvG_uncurry hΔ δ γ L β η 0 c₀ h₀ hWm ham).comp measurable_swap)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    refine Eventually.of_forall fun v ↦ ?_
    rw [lintegral_innerKvG_eq hΔ]
    have hbd : ∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal (ampG ρ D q c₀ Q W a v
        (negExpMap ρ (fibreLift κ Q δ γ L v z'))) ≤
        ENNReal.ofReal (Wstar * exp (-(c₀ * amin * exp (-v 0)))) *
          volume (fibreSet κ Q δ γ L v) := by
      rw [← setLIntegral_const]
      exact lintegral_mono fun z' ↦ ENNReal.ofReal_le_ofReal
        (ampG_nonneg_le hc hWb hab v _).2
    change (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
      ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0))) *
      (∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal (ampG ρ D q c₀ Q W a v
        (negExpMap ρ (fibreLift κ Q δ γ L v z')))) / ENNReal.ofReal (L ^ k) ≤ _
    calc (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
          ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0))) *
          (∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal (ampG ρ D q c₀ Q W a v
            (negExpMap ρ (fibreLift κ Q δ γ L v z')))) / ENNReal.ofReal (L ^ k)
        = (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
          ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0))) *
          ((∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal (ampG ρ D q c₀ Q W a v
            (negExpMap ρ (fibreLift κ Q δ γ L v z')))) / ENNReal.ofReal (L ^ k)) := by
          rw [mul_div_assoc]
      _ ≤ (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
          ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0))) *
          (ENNReal.ofReal (Wstar * exp (-(c₀ * amin * exp (-v 0)))) *
            ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i))) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          calc (∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal (ampG ρ D q c₀ Q W a v
                (negExpMap ρ (fibreLift κ Q δ γ L v z')))) / ENNReal.ofReal (L ^ k)
              ≤ ENNReal.ofReal (Wstar * exp (-(c₀ * amin * exp (-v 0)))) *
                volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k) :=
                ENNReal.div_le_div_right hbd _
            _ = ENNReal.ofReal (Wstar * exp (-(c₀ * amin * exp (-v 0)))) *
                (volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k)) := by
                rw [mul_div_assoc]
            _ ≤ _ := mul_le_mul_of_nonneg_left (volume_fibreSet_div_le hΔ hκ hδ γ hL v) zero_le
      _ = ENNReal.ofReal Wstar * (vWeight β η 0 (c₀ * amin) h₀ v *
          ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i))) := by
          unfold vWeight
          rw [ENNReal.ofReal_mul hW, ENNReal.ofReal_mul (exp_pos (-(β * v 0 + η * v 1 + 0))).le]
          ring
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_vWeight_mul_pow hβ hη hca hδ hP]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun v ↦ ?_
    simp_rw [lintegral_innerKvG_eq hΔ]
    by_cases hv : v 1 ∈ Ioi h₀
    · by_cases hb : 0 < fibreB κ Q v 1
      · have hlim := tendsto_lintegral_fibre_weighted_degenerate hΔ hκ hc₀ hdeg hb hρ
          (measurable_ampG ρ D q c₀ Q hWm ham v)
          (fun x ↦ ⟨(ampG_nonneg_le hc hWb hab v x).1, ampG_le hc hamin hWb hab v x⟩)
          (ampG_tendsto_degenerate hρ hD hq hWtr hatr hv hb)
        have := ENNReal.Tendsto.const_mul (a := (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
          ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0)))) hlim
          (Or.inr (ENNReal.mul_ne_top (indicator_one_ne_top _ _) ENNReal.ofReal_ne_top))
        have hlimval : (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
            ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0))) *
            (ENNReal.ofReal (Wtr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) *
              exp (-(c₀ * atr (survCoord ρ κ Q v) (truthOf ρ D q Q (v 1)) * exp (-v 0)))) *
              volume (facePolytope κ Q δ γ)) =
            vWeightTD ρ D q κ Q β η c₀ h₀ Wtr atr v * volume (facePolytope κ Q δ γ) := by
          unfold vWeightTD
          rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show fibreB κ Q v 1 ∈ Ioi 0 from hb),
            one_mul, one_mul, one_mul, ← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le]
          congr 2
          ring
        rw [← hlimval]
        refine this.congr' (Eventually.of_forall fun L ↦ ?_)
        simp only [ampG]
        rw [mul_div_assoc]
      · have hz : ∀ L, (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
            ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0))) *
            (∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal
              (W (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
                exp (-(c₀ * a (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
                  exp (-v 0))))) / ENNReal.ofReal (L ^ k) = 0 := fun L ↦ by
          rw [fibreSet_eq_empty_of_degenerate hΔ hdeg (not_lt.mp hb), Measure.restrict_empty,
            lintegral_zero_measure, mul_zero, ENNReal.zero_div]
        simp_rw [hz]
        unfold vWeightTD
        rw [Set.indicator_of_notMem (show fibreB κ Q v 1 ∉ Ioi 0 from hb), mul_zero, zero_mul,
          zero_mul]
        exact tendsto_const_nhds
    · have hz : ∀ L, (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
          ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0))) *
          (∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal
            (W (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
              exp (-(c₀ * a (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
                exp (-v 0))))) / ENNReal.ofReal (L ^ k) = 0 := fun L ↦ by
        rw [Set.indicator_of_notMem hv, zero_mul, zero_mul, ENNReal.zero_div]
      simp_rw [hz]
      unfold vWeightTD
      rw [Set.indicator_of_notMem hv, zero_mul, zero_mul, zero_mul]
      exact tendsto_const_nhds

/-! ### The theorem -/

/-- **The boundary regime with general units (partial trace).** With the second fibre constraint
identically vanishing and units `W(x, u)`, `a(x, u)` with partial traces `W_tr(z, u)`, `a_tr(z, u)`
as the collapsing coordinates tend to `0` with the surviving coordinate held at `z`:
`t^{γp + βδ − ηγ}/(log t)^k · K(t) → A ρ^{∑(r+1)}/|det M| · (∫⁻ vWeightTD).toReal · vol(F')`. -/
theorem tendsto_modelKernel_general_degenerate {ρ A B D γ p q δ β η : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hdeg : fibreCoef κ Q 1 = 0 ∧ fibreA κ Q δ γ 1 = 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    {Wstar amin : ℝ} (hamin : 0 < amin) (hWm : Measurable (Function.uncurry W))
    (ham : Measurable (Function.uncurry a)) (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar)
    (hab : ∀ x u, amin ≤ a x u) {Wtr atr : ℝ → ℝ → ℝ} (hWtrm : Measurable (Function.uncurry Wtr))
    (hatrm : Measurable (Function.uncurry atr))
    (hWtrb : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ Wtr z u ∧ Wtr z u ≤ Wstar)
    (hatrb : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ, amin ≤ atr z u)
    (hWtr : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ,
      Tendsto (fun y ↦ W (Function.update y (Sum.inr 1) z) u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr z u)))
    (hatr : ∀ z ∈ Ioo (0 : ℝ) ρ, ∀ u ∈ Ioo (0 : ℝ) ρ,
      Tendsto (fun y ↦ a (Function.update y (Sum.inr 1) z) u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr z u))) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r W a t) atTop
      (𝓝 (A * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹ *
        (∫⁻ v : Fin 2 → ℝ, vWeightTD ρ D q κ Q β η (B * ρ ^ (∑ i, κ i))
          (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) Wtr atr v).toReal *
        (volume (facePolytope κ Q δ γ)).toReal)) := by
  set c₀ := B * ρ ^ (∑ i, κ i) with hc₀def
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  have hc : 0 < c₀ := mul_pos hB (Real.rpow_pos_of_pos hρ _)
  have hW : 0 ≤ Wstar := (hWb 0 0).1.trans (hWb 0 0).2
  have hF := volume_facePolytope_ne_top hΔ hκ δ γ
  -- the transverse limit
  have hlim := (tendsto_lintegral_innerKvG_degenerate hρ hD hq hΔ hκ hc₀ hdeg hβ hη hc hδ hamin
    hWm ham hWb hab hWtr hatr).comp Real.tendsto_log_atTop
  rw [lintegral_mul_const _ (measurable_vWeightTD ρ D q κ Q β η c₀ h₀ hWtrm hatrm)] at hlim
  set J := ∫⁻ v : Fin 2 → ℝ, vWeightTD ρ D q κ Q β η c₀ h₀ Wtr atr v with hJ
  have hJne : J ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal Wstar *
      ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 (c₀ * amin) h₀ v) ?_ ?_
    · rw [lintegral_vWeight_zero hβ hη (mul_pos hc hamin)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · rw [hJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono (vWeightTD_le hρ hD hq hc hWtrb hatrb hW)
  have hne : J * volume (facePolytope κ Q δ γ) ≠ ⊤ := ENNReal.mul_ne_top hJne hF
  have hlim2 := ((ENNReal.tendsto_toReal hne).comp hlim).const_mul
    (A * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹)
  rw [ENNReal.toReal_mul, ← mul_assoc] at hlim2
  refine hlim2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hL : 0 < log t := Real.log_pos ht
  simp only [Function.comp]
  have hK : modelKernel ρ A B D γ p q δ Q κ r W a t =
      A * t ^ (-(γ * p)) * (∫⁻ x, ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r W a t x)).toReal := by
    unfold modelKernel
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (modelIntegrand_general_nonneg (fun x u ↦ (hWb x u).1)))
      (measurable_modelIntegrand hWm ham t).aestronglyMeasurable]
  rw [hK, lintegral_modelIntegrand_general W a hρ hD hq ht0]
  have hB' : B * t ^ δ * ρ ^ (∑ i, κ i) = c₀ * exp (δ * log t) := by
    rw [hc₀def, Real.rpow_def_of_pos ht0, mul_comm (log t) δ]
    ring
  rw [hB', lintegral_sum_split (measurable_logIntegrandG _ _ _ _ _ _ _ _ _ hWm ham)]
  simp_rw [lintegral_inner_substG hWm ham hq ht0 (fun i ↦ hr i) hΔ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_innerKvG_swap hΔ _ _ _ _ _ _ _ _
    hWm ham, ← hh₀]
  have hmL : ∫⁻ v : Fin 2 → ℝ, ∫⁻ z' : Fin k → ℝ,
      innerKvG ρ D q κ Q δ γ (log t) β η ((β * δ - η * γ) * log t) c₀ h₀ W a z' v =
      ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))) * ∫⁻ v : Fin 2 → ℝ, ∫⁻ z' : Fin k → ℝ,
        innerKvG ρ D q κ Q δ γ (log t) β η 0 c₀ h₀ W a z' v := by
    simp_rw [innerKvG_eq_mul ρ D q κ Q δ γ (log t) β η ((β * δ - η * γ) * log t) c₀ h₀ W a]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hmL]
  have hJt : ∫⁻ v : Fin 2 → ℝ, (∫⁻ z' : Fin k → ℝ,
      innerKvG ρ D q κ Q δ γ (log t) β η 0 c₀ h₀ W a z' v) / ENNReal.ofReal (log t ^ k) =
      (∫⁻ v : Fin 2 → ℝ, ∫⁻ z' : Fin k → ℝ,
        innerKvG ρ D q κ Q δ γ (log t) β η 0 c₀ h₀ W a z' v) / ENNReal.ofReal (log t ^ k) := by
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const' _ _
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hL k)).ne')
  rw [hJt]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal (pow_pos hL k).le,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), ENNReal.toReal_ofReal (exp_pos _).le,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hρ.le _)]
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
