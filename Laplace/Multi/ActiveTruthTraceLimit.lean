/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthTraceAssembly

/-!
# The transverse limit of the trace model

Steps 4–5 for truth-dependent units. The trace weight is dominated by `W_*` times the constant-unit
weight at the Boltzmann constant `c₀ a_-` (`vWeightT_le`), so the dominated convergence in the
transverse variables goes through unchanged (`tendsto_lintegral_vWeightT_fibre`); the transverse
integral of the trace weight is `Γ(β) ∫_{h > h₀} e^{-ηh} w(u(h)) (c₀ a(u(h)))^{-β} dh`
(`lintegral_vWeightT_zero`, by Fubini on `Fin 2 → ℝ ≃ ℝ × ℝ` with the `s`-integral done first),
and the substitution `u = u(h)` turns the `h`-integral into
`q C^{-qη} ∫_0^ρ u^{qη−1} f(u) du` with `C = D ρ^{-∑Q/q}` (`integral_Ioi_truthOf`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-- For `h > h₀` the truth coordinate lies in `(0, ρ)`. -/
theorem truthOf_mem_Ioo {ρ D q : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    (Q : Fin k ⊕ Fin 2 → ℝ) {h : ℝ} (hh : -(q * log (ρ / D) + (∑ i, Q i) * log ρ) < h) :
    truthOf ρ D q Q h ∈ Ioo 0 ρ := by
  unfold truthOf
  refine ⟨by positivity, ?_⟩
  rw [← Real.log_lt_log_iff (by positivity) hρ, Real.log_mul (by positivity) (exp_pos _).ne',
    Real.log_mul hD.ne' (Real.rpow_pos_of_pos hρ _).ne', Real.log_rpow hρ, Real.log_exp]
  rw [Real.log_div hρ.ne' hD.ne'] at hh
  have e : log D + -(∑ i, Q i) / q * log ρ + -(h / q) =
      (q * log D - (∑ i, Q i) * log ρ - h) / q := by
    field_simp
    ring
  rw [e, div_lt_iff₀ hq]
  linarith

theorem indicator_one_ne_top {α : Type*} (s : Set α) (x : α) :
    s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≠ ⊤ := by
  by_cases h : x ∈ s <;> simp [h]

/-- **Domination**: the trace weight is at most `W_*` times the constant-unit weight at `c₀ a_-`. -/
theorem vWeightT_le {β η c₀ h₀ Wstar amin : ℝ} (hc : 0 < c₀) {wh ah : ℝ → ℝ}
    (hw : ∀ h, h₀ < h → 0 ≤ wh h ∧ wh h ≤ Wstar) (ha : ∀ h, h₀ < h → amin ≤ ah h)
    (v : Fin 2 → ℝ) :
    vWeightT β η 0 c₀ h₀ wh ah v ≤ ENNReal.ofReal Wstar * vWeight β η 0 (c₀ * amin) h₀ v := by
  have hW : 0 ≤ Wstar := (hw (h₀ + 1) (by linarith)).1.trans (hw (h₀ + 1) (by linarith)).2
  unfold vWeightT vWeight
  by_cases hv : v 1 ∈ Ioi h₀
  · rw [Set.indicator_of_mem hv, one_mul, one_mul, ← ENNReal.ofReal_mul hW]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hw (v 1) hv
    have h2 := ha (v 1) hv
    have hE : 0 ≤ exp (-(β * v 0 + η * v 1 + 0)) := (exp_pos _).le
    have h3 : exp (-(c₀ * ah (v 1) * exp (-v 0))) ≤ exp (-(c₀ * amin * exp (-v 0))) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc.le) (exp_pos _).le
    calc wh (v 1) * exp (-(β * v 0 + η * v 1 + 0)) * exp (-(c₀ * ah (v 1) * exp (-v 0)))
        ≤ Wstar * exp (-(β * v 0 + η * v 1 + 0)) * exp (-(c₀ * amin * exp (-v 0))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1.2 hE) h3 (exp_pos _).le (by positivity)
      _ = Wstar * (exp (-(β * v 0 + η * v 1 + 0)) * exp (-(c₀ * amin * exp (-v 0)))) := by ring
  · rw [Set.indicator_of_notMem hv, zero_mul, zero_mul, mul_zero]

theorem vWeightT_ne_top (β η mL c₀ h₀ : ℝ) (wh ah : ℝ → ℝ) (v : Fin 2 → ℝ) :
    vWeightT β η mL c₀ h₀ wh ah v ≠ ⊤ :=
  ENNReal.mul_ne_top (indicator_one_ne_top _ _) ENNReal.ofReal_ne_top

/-- **The transverse limit for the trace model.** -/
theorem tendsto_lintegral_vWeightT_fibre {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {β η c₀ δ γ : ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0) (hβ : 0 < β) (hη : 0 < η) (hc : 0 < c₀)
    (hδ : 0 ≤ δ) (h₀ : ℝ) {Wstar amin : ℝ} (hamin : 0 < amin) {wh ah : ℝ → ℝ}
    (hwm : Measurable wh) (ham : Measurable ah) (hw : ∀ h, h₀ < h → 0 ≤ wh h ∧ wh h ≤ Wstar)
    (ha : ∀ h, h₀ < h → amin ≤ ah h) :
    Tendsto (fun L ↦ ∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 c₀ h₀ wh ah v *
        (volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k))) atTop
      (𝓝 (∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 c₀ h₀ wh ah v * volume (poly2 (fibreCoef κ Q 0)
        (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1)))) := by
  have hP : 0 < ∏ i, κ (Sum.inl i) := Finset.prod_pos fun i _ ↦ hκ _
  have hca : 0 < c₀ * amin := mul_pos hc hamin
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun v ↦ ENNReal.ofReal Wstar * (vWeight β η 0 (c₀ * amin) h₀ v *
      ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i))))
    (Eventually.of_forall fun L ↦ (measurable_vWeightT _ _ _ _ _ hwm ham).mul
      ((measurable_volume_fibreSet hΔ δ γ L).div_const _)) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    refine Eventually.of_forall fun v ↦ ?_
    calc vWeightT β η 0 c₀ h₀ wh ah v * (volume (fibreSet κ Q δ γ L v) / ENNReal.ofReal (L ^ k))
        ≤ ENNReal.ofReal Wstar * vWeight β η 0 (c₀ * amin) h₀ v *
          ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i)) :=
          mul_le_mul' (vWeightT_le hc hw ha v) (volume_fibreSet_div_le hΔ hκ hδ γ hL v)
      _ = _ := by rw [mul_assoc]
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_vWeight_mul_pow hβ hη hca hδ hP]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun v ↦ ?_
    exact ENNReal.Tendsto.const_mul (tendsto_volume_fibreSet_div hΔ hκ hc₀ hc₁ v)
      (Or.inr (vWeightT_ne_top _ _ _ _ _ _ _ _))

/-- The transverse integral of the trace weight, in the `h`-form. -/
theorem lintegral_vWeightT_zero {β η c₀ h₀ : ℝ} (hβ : 0 < β) (hη : 0 < η) (hc : 0 < c₀)
    {Wstar amin : ℝ} (hamin : 0 < amin) {wh ah : ℝ → ℝ} (hwm : Measurable wh)
    (ham : Measurable ah) (hw : ∀ h, h₀ < h → 0 ≤ wh h ∧ wh h ≤ Wstar)
    (ha : ∀ h, h₀ < h → amin ≤ ah h) :
    ∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 c₀ h₀ wh ah v =
      ENNReal.ofReal (∫ h in Ioi h₀, Gamma β * (c₀ * ah h) ^ (-β) * (exp (-(η * h)) * wh h)) := by
  have hW : 0 ≤ Wstar := (hw (h₀ + 1) (by linarith)).1.trans (hw (h₀ + 1) (by linarith)).2
  -- the integrand as a function of `(v 0, v 1)`
  set F : ℝ → ℝ → ℝ≥0∞ := fun s h ↦ (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) h *
    ENNReal.ofReal (wh h * exp (-(β * s + η * h + 0)) * exp (-(c₀ * ah h * exp (-s)))) with hF
  have hFm : Measurable fun p : ℝ × ℝ ↦ F p.1 p.2 := by
    rw [hF]
    refine Measurable.mul ((measurable_const.indicator measurableSet_Ioi).comp measurable_snd) ?_
    refine ENNReal.measurable_ofReal.comp ?_
    refine ((hwm.comp measurable_snd).mul (Real.measurable_exp.comp
      (((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)).add
        measurable_const).neg)).mul (Real.measurable_exp.comp ?_)
    exact ((measurable_const.mul (ham.comp measurable_snd)).mul
      (Real.measurable_exp.comp measurable_fst.neg)).neg
  have e1 : ∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 c₀ h₀ wh ah v = ∫⁻ p : ℝ × ℝ, F p.1 p.2 := by
    rw [← (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (fun p : ℝ × ℝ ↦ F p.1 p.2)]
    rfl
  rw [e1, Measure.volume_eq_prod, lintegral_prod_symm' _ hFm]
  -- the inner `s`-integral
  have hinner : ∀ h, ∫⁻ s, F s h = (Ioi h₀).indicator
      (fun h ↦ ENNReal.ofReal (Gamma β * (c₀ * ah h) ^ (-β) * (exp (-(η * h)) * wh h))) h := by
    intro h
    by_cases hh : h ∈ Ioi h₀
    · have hca : 0 < c₀ * ah h := mul_pos hc (hamin.trans_le (ha h hh))
      have hpt : ∀ s, F s h = ENNReal.ofReal (sWeight β (c₀ * ah h) s) *
          ENNReal.ofReal (exp (-(η * h)) * wh h) := by
        intro s
        rw [hF]
        simp only
        rw [Set.indicator_of_mem hh, one_mul, ← ENNReal.ofReal_mul (sWeight_nonneg _ _ _)]
        congr 1
        unfold sWeight
        rw [add_zero, show exp (-(β * s + η * h)) = exp (-(β * s)) * exp (-(η * h)) by
          rw [← Real.exp_add]; congr 1; ring]
        ring
      simp_rw [hpt]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, Set.indicator_of_mem hh,
        ← ofReal_integral_eq_lintegral_ofReal (integrable_sWeight hβ hca)
          (Eventually.of_forall (sWeight_nonneg _ _)), integral_sWeight hβ hca,
        ← ENNReal.ofReal_mul (by positivity)]
    · have hpt : ∀ s, F s h = 0 := fun s ↦ by
        rw [hF]
        simp only
        rw [Set.indicator_of_notMem hh, zero_mul]
      simp_rw [hpt]
      rw [lintegral_zero, Set.indicator_of_notMem hh]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Ioi]
  -- integrability of the `h`-integrand
  have hint : IntegrableOn (fun h ↦ Gamma β * (c₀ * ah h) ^ (-β) * (exp (-(η * h)) * wh h))
      (Ioi h₀) := by
    have hbd := ((integrableOn_exp_neg_mul_Ioi' hη h₀).const_mul
      (Gamma β * (c₀ * amin) ^ (-β) * Wstar))
    refine hbd.mono' ?_ ?_
    · exact (((measurable_const.mul ((measurable_const.mul ham).pow_const _)).mul
        ((Continuous.measurable (by fun_prop)).mul hwm))).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun h hh ↦ ?_
      have hca : 0 < c₀ * ah h := mul_pos hc (hamin.trans_le (ha h hh))
      have hG := Real.Gamma_pos_of_pos hβ
      have hle : (c₀ * ah h) ^ (-β) ≤ (c₀ * amin) ^ (-β) := by
        rw [Real.rpow_neg hca.le, Real.rpow_neg (mul_pos hc hamin).le]
        exact inv_anti₀ (Real.rpow_pos_of_pos (mul_pos hc hamin) _)
          (Real.rpow_le_rpow (mul_pos hc hamin).le
            (mul_le_mul_of_nonneg_left (ha h hh) hc.le) hβ.le)
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := (hw h hh).1
        have := (Real.rpow_pos_of_pos hca (-β)).le
        positivity)]
      calc Gamma β * (c₀ * ah h) ^ (-β) * (exp (-(η * h)) * wh h)
          ≤ Gamma β * (c₀ * amin) ^ (-β) * (exp (-(η * h)) * Wstar) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hle hG.le)
              (mul_le_mul_of_nonneg_left (hw h hh).2 (exp_pos _).le)
              (mul_nonneg (exp_pos _).le (hw h hh).1)
              (mul_nonneg hG.le (Real.rpow_pos_of_pos (mul_pos hc hamin) _).le)
        _ = Gamma β * (c₀ * amin) ^ (-β) * Wstar * exp (-(η * h)) := by ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun h hh ↦ ?_)
  change (0 : ℝ) ≤ _
  have hca : 0 < c₀ * ah h := mul_pos hc (hamin.trans_le (ha h hh))
  have := (hw h hh).1
  have := (Real.rpow_pos_of_pos hca (-β)).le
  have := (Real.Gamma_pos_of_pos hβ).le
  positivity

/-- **The `h ↔ u` identity**: `∫_{h > h₀} e^{-ηh} f(u(h)) dh = q C^{-qη} ∫_0^ρ u^{qη−1} f(u) du`
with `C = D ρ^{-∑Q/q}`, for any `f`. -/
theorem integral_Ioi_truthOf {ρ D q η : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    (Q : Fin k ⊕ Fin 2 → ℝ) (f : ℝ → ℝ) :
    ∫ h in Ioi (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)), exp (-(η * h)) * f (truthOf ρ D q Q h) =
      q * (D * ρ ^ (-(∑ i, Q i) / q)) ^ (-(q * η)) *
        ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * f u := by
  set C := D * ρ ^ (-(∑ i, Q i) / q) with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  have hlogC : log C - h₀ / q = log ρ := by
    rw [hC, hh₀, Real.log_mul hD.ne' (Real.rpow_pos_of_pos hρ _).ne', Real.log_rpow hρ,
      Real.log_div hρ.ne' hD.ne']
    field_simp
    ring
  -- the integrand on the whole line
  set G : ℝ → ℝ := fun h ↦ (Ioi h₀).indicator (fun h ↦ exp (-(η * h)) * f (truthOf ρ D q Q h)) h
    with hG
  have e1 : ∫ h in Ioi h₀, exp (-(η * h)) * f (truthOf ρ D q Q h) = ∫ h, G h := by
    rw [hG, integral_indicator measurableSet_Ioi]
  -- `h = −q (v − log C)`
  have e2 : ∫ h, G h = q * ∫ v, G (-q * (v - log C)) := by
    rw [integral_sub_right_eq_self (fun v ↦ G (-q * v)) (log C),
      Measure.integral_comp_mul_left G (-q), abs_inv, abs_neg, abs_of_pos hq, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  -- the substituted integrand is `e^v · g(e^v)`
  set g : ℝ → ℝ := fun y ↦ C ^ (-(q * η)) * ((Iio ρ).indicator (fun y ↦ y ^ (q * η - 1) * f y) y)
    with hg
  have e3 : ∀ v, G (-q * (v - log C)) = exp v * g (exp v) := by
    intro v
    rw [hG, hg]
    simp only
    have hu : truthOf ρ D q Q (-q * (v - log C)) = exp v := by
      unfold truthOf
      rw [← hC, show -(-q * (v - log C) / q) = v - log C by field_simp, Real.exp_sub,
        Real.exp_log hC0]
      field_simp
    have hiff : -q * (v - log C) ∈ Ioi h₀ ↔ exp v ∈ Iio ρ := by
      rw [mem_Ioi, mem_Iio, ← Real.lt_log_iff_exp_lt hρ, ← hlogC]
      constructor
      · intro h
        have h1 : (v - log C) * q < -h₀ := by linarith
        have h2 := (lt_div_iff₀ hq).mpr h1
        rw [neg_div] at h2
        linarith
      · intro h
        have h1 : v - log C < -h₀ / q := by
          rw [neg_div]
          linarith
        have h2 := (lt_div_iff₀ hq).mp h1
        linarith
    by_cases hv : -q * (v - log C) ∈ Ioi h₀
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hiff.mp hv), hu]
      have ee : exp (-(η * (-q * (v - log C)))) =
          C ^ (-(q * η)) * (exp v ^ (q * η - 1) * exp v) := by
        rw [Real.rpow_def_of_pos hC0, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [ee]
      ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h ↦ hv (hiff.mpr h)), mul_zero,
        mul_zero]
  rw [e1, e2, integral_congr_ae (Eventually.of_forall e3), integral_comp_exp_univ]
  rw [hg]
  simp only
  rw [integral_const_mul, ← mul_assoc]
  congr 1
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Set.inter_comm, Ioi_inter_Iio]

end Laplace.Multi
