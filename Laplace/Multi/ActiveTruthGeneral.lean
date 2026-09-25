/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthFibreWeighted

/-!
# The transverse active-truth face theorem with general units (trace replacement)

Astra round 9, item 3. Units `W(x, u)`, `a(x, u)` depending on the chart point and the truth
coordinate: jointly measurable, `0 ≤ W ≤ W_*`, `a ≥ a_- > 0`, with traces `W(x, u) → W_tr(u)`,
`a(x, u) → a_tr(u)` as `x → 0` inside the box for every `u ∈ (0, ρ)`. The pipeline is the trace
model's, except that Tonelli no longer factors: over a transverse point `v` the inner integral is
the fibre integral of the amplitude `W(x, u(h)) e^{-c₀ a(x, u(h)) e^{-s}}` at the reconstructed
chart point `x = ρe^{-z(z')}`, and the weighted fibre limit (`tendsto_lintegral_fibre_weighted`)
replaces the fibre volume. The limit is the trace model's:
`A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ∫_0^ρ u^{qη−1} W_tr(u) a_tr(u)^{-β} du`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-! ### The log form with general units -/

/-- The general-unit integrand at `ρe^{-z}`, `z > 0`, with the Jacobian. -/
theorem modelIntegrand_general_negExp {ρ B D γ q δ : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ} {t : ℝ}
    (W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ) (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t)
    {z : Fin k ⊕ Fin 2 → ℝ} (hz : ∀ i, 0 < z i) :
    (∏ i, ρ * exp (-z i)) * modelIntegrand ρ B D γ q δ Q κ r W a t (negExpMap ρ z) =
      (logCut ρ D γ q t Q).indicator (fun z ↦ W (negExpMap ρ z) (logTruth ρ D γ q t Q z) *
        ρ ^ (∑ i, (r i + 1)) * exp (-(∑ i, (r i + 1) * z i)) *
        exp (-(B * t ^ δ * a (negExpMap ρ z) (logTruth ρ D γ q t Q z) * ρ ^ (∑ i, κ i) *
          exp (-(∑ i, κ i * z i))))) z := by
  unfold modelIntegrand modelDomain
  have hbox : negExpMap ρ z ∈ Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ := by
    rw [← image_negExpMap_orthant hρ]
    exact ⟨z, fun i _ ↦ hz i, rfl⟩
  by_cases hcut : z ∈ logCut ρ D γ q t Q
  · rw [Set.indicator_of_mem hcut, Set.indicator_of_mem
      (show negExpMap ρ z ∈ (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ) ∩
        {x | cutVar D γ q Q t x < ρ} from ⟨hbox, (cutVar_negExp_lt_iff hρ hD hq ht Q z).mpr hcut⟩)]
    rw [cutVar_negExp_eq_logTruth hρ]
    have er : ∏ i, (negExpMap ρ z) i ^ r i = ρ ^ (∑ i, r i) * exp (-(∑ i, r i * z i)) := by
      simp only [negExpMap]
      have e : ∀ i, (ρ * exp (-z i)) ^ r i = ρ ^ r i * exp (-(r i * z i)) := fun i ↦ by
        rw [Real.mul_rpow hρ.le (exp_pos _).le, ← Real.exp_mul]
        congr 2
        ring
      simp_rw [e]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos hρ,
        Finset.sum_neg_distrib]
    have eκ : ∏ i, (negExpMap ρ z) i ^ κ i = ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i)) := by
      simp only [negExpMap]
      have e : ∀ i, (ρ * exp (-z i)) ^ κ i = ρ ^ κ i * exp (-(κ i * z i)) := fun i ↦ by
        rw [Real.mul_rpow hρ.le (exp_pos _).le, ← Real.exp_mul]
        congr 2
        ring
      simp_rw [e]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos hρ,
        Finset.sum_neg_distrib]
    have eJ : ∏ i, ρ * exp (-z i) =
        ρ ^ (Fintype.card (Fin k ⊕ Fin 2) : ℝ) * exp (-(∑ i, z i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
        Finset.sum_neg_distrib, Real.rpow_natCast]
    rw [er, eκ, eJ]
    have e1 : ρ ^ (∑ i, (r i + 1)) =
        ρ ^ (∑ i, r i) * ρ ^ (Fintype.card (Fin k ⊕ Fin 2) : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Real.rpow_add hρ]
    have e2 : exp (-(∑ i, (r i + 1) * z i)) = exp (-(∑ i, r i * z i)) * exp (-(∑ i, z i)) := by
      rw [← Real.exp_add]
      congr 1
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
      ring
    rw [e1, e2, show B * t ^ δ * a (negExpMap ρ z) (logTruth ρ D γ q t Q z) *
      (ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i))) =
      B * t ^ δ * a (negExpMap ρ z) (logTruth ρ D γ q t Q z) * ρ ^ (∑ i, κ i) *
        exp (-(∑ i, κ i * z i)) by ring]
    ring
  · rw [Set.indicator_of_notMem hcut, Set.indicator_of_notMem
      (fun h ↦ hcut ((cutVar_negExp_lt_iff hρ hD hq ht Q z).mp h.2)), mul_zero]

/-- The log-form general-unit integrand in `lintegral` form. -/
noncomputable def logIntegrandG (ρ D γ q t : ℝ) (Q c κ : Fin k ⊕ Fin 2 → ℝ) (B' : ℝ)
    (W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ) (z : Fin k ⊕ Fin 2 → ℝ) : ℝ≥0∞ :=
  {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z *
    (logCut ρ D γ q t Q).indicator (fun _ ↦ (1 : ℝ≥0∞)) z *
    ENNReal.ofReal (W (negExpMap ρ z) (logTruth ρ D γ q t Q z) * exp (-(∑ i, c i * z i)) *
      exp (-(B' * a (negExpMap ρ z) (logTruth ρ D γ q t Q z) * exp (-(∑ i, κ i * z i)))))

theorem continuous_negExpMap (ρ : ℝ) : Continuous (negExpMap ρ : (Fin k ⊕ Fin 2 → ℝ) → _) := by
  refine continuous_pi fun i ↦ ?_
  unfold negExpMap
  fun_prop

theorem measurable_logIntegrandG (ρ D γ q t : ℝ) (Q c κ : Fin k ⊕ Fin 2 → ℝ) (B' : ℝ)
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) :
    Measurable (logIntegrandG ρ D γ q t Q c κ B' W a) := by
  unfold logIntegrandG
  have hpair : Measurable fun z : Fin k ⊕ Fin 2 → ℝ ↦ (negExpMap ρ z, logTruth ρ D γ q t Q z) :=
    (continuous_negExpMap ρ).measurable.prodMk (measurable_logTruth _ _ _ _ _ _)
  refine ((measurable_const.indicator measurableSet_orthantSet).mul
    (measurable_const.indicator (measurableSet_logCut _ _ _ _ _ _))).mul ?_
  refine ENNReal.measurable_ofReal.comp ?_
  refine ((hW.comp hpair).mul (Continuous.measurable (by fun_prop))).mul
    (Real.measurable_exp.comp ?_)
  exact ((measurable_const.mul (ha.comp hpair)).mul (Continuous.measurable (by fun_prop))).neg

/-- The `lintegral` of the general-unit integrand is `ρ^{∑(r+1)}` times the `lintegral` of the
log-form integrand. -/
theorem lintegral_modelIntegrand_general {ρ B D γ q δ : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ} {t : ℝ}
    (W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ) (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x) =
      ENNReal.ofReal (ρ ^ (∑ i, (r i + 1))) *
        ∫⁻ z, logIntegrandG ρ D γ q t Q (fun i ↦ r i + 1) κ (B * t ^ δ * ρ ^ (∑ i, κ i)) W a z := by
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hsupp : (fun x ↦ ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x)) =
      (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ).indicator fun x ↦ ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r W a t x) := by
    funext x
    by_cases hx : x ∈ Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      unfold modelIntegrand
      rw [Set.indicator_of_notMem (fun h' ↦ hx h'.1), ENNReal.ofReal_zero]
  rw [hsupp, lintegral_indicator hbox, lintegral_box_eq_orthant hρ]
  have horth : (fun z ↦ logIntegrandG ρ D γ q t Q (fun i ↦ r i + 1) κ
      (B * t ^ δ * ρ ^ (∑ i, κ i)) W a z) =
      (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioi (0 : ℝ)).indicator fun z ↦
        logIntegrandG ρ D γ q t Q (fun i ↦ r i + 1) κ (B * t ^ δ * ρ ^ (∑ i, κ i)) W a z := by
    funext z
    by_cases hz : z ∈ Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      unfold logIntegrandG
      rw [← orthantSet_eq_pi] at hz
      rw [Set.indicator_of_notMem hz, zero_mul, zero_mul]
  rw [horth, lintegral_indicator (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    fun z hz ↦ ?_
  have hz' : ∀ i, 0 < z i := fun i ↦ (Set.mem_univ_pi.mp hz) i
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ ↦ by positivity),
    modelIntegrand_general_negExp W a hρ hD hq ht hz']
  unfold logIntegrandG
  rw [Set.indicator_of_mem (show z ∈ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i} from hz'), one_mul]
  by_cases hcut : z ∈ logCut ρ D γ q t Q
  · rw [Set.indicator_of_mem hcut, Set.indicator_of_mem hcut, one_mul,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
    congr 1
    have e : ∀ x : ℝ, B * t ^ δ * x * ρ ^ (∑ i, κ i) = B * t ^ δ * ρ ^ (∑ i, κ i) * x :=
      fun x ↦ by ring
    rw [e]
    ring
  · rw [Set.indicator_of_notMem hcut, Set.indicator_of_notMem hcut]
    simp

/-! ### The transverse form -/

/-- The transverse integrand with general units: the amplitude is evaluated at the reconstructed
chart point `ρe^{-z(z')}` and the truth coordinate `u(h)`. -/
noncomputable def innerKvG (ρ D q : ℝ) (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L β η mL c₀ h₀ : ℝ)
    (W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ) (z' : Fin k → ℝ) (v : Fin 2 → ℝ) : ℝ≥0∞ :=
  {z' : Fin k → ℝ | ∀ j, 0 < z' j}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z' *
    ((fun y ↦ transMat κ Q *ᵥ y + transShift κ Q δ γ L z') ''
      {y : Fin 2 → ℝ | ∀ j, 0 < y j}).indicator (fun _ ↦ (1 : ℝ≥0∞)) v *
    (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
    ENNReal.ofReal (W (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
      exp (-(β * v 0 + η * v 1 + mL)) *
      exp (-(c₀ * a (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
        exp (-v 0))))

theorem fibreLift_mulVec_add {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (δ γ L : ℝ) (z' : Fin k → ℝ) (y : Fin 2 → ℝ) :
    fibreLift κ Q δ γ L (transMat κ Q *ᵥ y + transShift κ Q δ γ L z') z' = Sum.elim z' y := by
  unfold fibreLift
  rw [add_sub_cancel_right, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hΔ), Matrix.one_mulVec]

theorem measurable_innerKvG_uncurry {ρ D q : ℝ} {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (δ γ L β η mL c₀ h₀ : ℝ)
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) :
    Measurable (Function.uncurry (innerKvG ρ D q κ Q δ γ L β η mL c₀ h₀ W a)) := by
  have hlift : Measurable fun p : (Fin k → ℝ) × (Fin 2 → ℝ) ↦
      negExpMap ρ (fibreLift κ Q δ γ L p.2 p.1) := by
    refine (continuous_negExpMap ρ).measurable.comp ?_
    refine measurable_pi_iff.mpr fun i ↦ ?_
    cases i with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr j =>
      simp only [fibreLift_inr]
      exact (measurable_const.add ((measurable_const.mul
        ((measurable_pi_apply 0).comp measurable_snd)).add (measurable_const.mul
        ((measurable_pi_apply 1).comp measurable_snd)))).sub
        ((measurable_dotProduct_left _).comp measurable_fst)
  have hu : Measurable fun p : (Fin k → ℝ) × (Fin 2 → ℝ) ↦ truthOf ρ D q Q (p.2 1) :=
    (continuous_truthOf ρ D q Q).measurable.comp ((measurable_pi_apply 1).comp measurable_snd)
  have horth : Measurable fun p : (Fin k → ℝ) × (Fin 2 → ℝ) ↦
      {z' : Fin k → ℝ | ∀ j, 0 < z' j}.indicator (fun _ ↦ (1 : ℝ≥0∞)) p.1 :=
    (measurable_const.indicator measurableSet_orthantSet).comp measurable_fst
  have himg : Measurable fun p : (Fin k → ℝ) × (Fin 2 → ℝ) ↦
      ((fun y ↦ transMat κ Q *ᵥ y + transShift κ Q δ γ L p.1) ''
        {y : Fin 2 → ℝ | ∀ j, 0 < y j}).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2 := by
    have e : (fun p : (Fin k → ℝ) × (Fin 2 → ℝ) ↦
        ((fun y ↦ transMat κ Q *ᵥ y + transShift κ Q δ γ L p.1) ''
          {y : Fin 2 → ℝ | ∀ j, 0 < y j}).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2) =
        fun p ↦ {p : (Fin k → ℝ) × (Fin 2 → ℝ) | ∀ j, 0 < ((transMat κ Q)⁻¹ *ᵥ
          (p.2 - transShift κ Q δ γ L p.1)) j}.indicator (fun _ ↦ (1 : ℝ≥0∞)) p := by
      funext p
      rw [image_mulVec_add_orthant hΔ]
      rfl
    rw [e]
    refine measurable_const.indicator ?_
    have : {p : (Fin k → ℝ) × (Fin 2 → ℝ) | ∀ j, 0 < ((transMat κ Q)⁻¹ *ᵥ
        (p.2 - transShift κ Q δ γ L p.1)) j} = ⋂ j, {p : (Fin k → ℝ) × (Fin 2 → ℝ) |
          0 < ((transMat κ Q)⁻¹ *ᵥ (p.2 - transShift κ Q δ γ L p.1)) j} := by
      ext p
      simp
    rw [this]
    refine MeasurableSet.iInter fun j ↦ measurableSet_lt measurable_const ?_
    exact (measurable_pi_apply j).comp
      (((Matrix.toLin' (transMat κ Q)⁻¹).toContinuousLinearMap.continuous.comp
        (continuous_snd.sub ((continuous_transShift κ Q δ γ L).comp continuous_fst))).measurable)
  have hcut : Measurable fun p : (Fin k → ℝ) × (Fin 2 → ℝ) ↦
      (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (p.2 1) :=
    (measurable_const.indicator measurableSet_Ioi).comp
      ((measurable_pi_apply 1).comp measurable_snd)
  refine ((horth.mul himg).mul hcut).mul (ENNReal.measurable_ofReal.comp ?_)
  refine ((hW.comp (hlift.prodMk hu)).mul (Real.measurable_exp.comp (Measurable.neg
    (((measurable_const.mul ((measurable_pi_apply 0).comp measurable_snd)).add
      (measurable_const.mul ((measurable_pi_apply 1).comp measurable_snd))).add
      measurable_const)))).mul (Real.measurable_exp.comp ?_)
  exact ((measurable_const.mul (ha.comp (hlift.prodMk hu))).mul
    (Real.measurable_exp.comp ((measurable_pi_apply 0).comp measurable_snd).neg)).neg

/-- **The inner substitution with general units.** -/
theorem lintegral_inner_substG {ρ D γ q t δ β η c₀ : ℝ} {Q c κ : Fin k ⊕ Fin 2 → ℝ}
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) (hq : 0 < q) (ht : 0 < t)
    (hc : ∀ i, c i = β * κ i - η * Q i) (hΔ : (transMat κ Q).det ≠ 0) (z' : Fin k → ℝ) :
    ∫⁻ y : Fin 2 → ℝ, logIntegrandG ρ D γ q t Q c κ (c₀ * exp (δ * log t)) W a (Sum.elim z' y) =
      ENNReal.ofReal |(transMat κ Q).det|⁻¹ *
        ∫⁻ v, innerKvG ρ D q κ Q δ γ (log t) β η ((β * δ - η * γ) * log t) c₀
          (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) W a z' v := by
  have hmeasK : Measurable (innerKvG ρ D q κ Q δ γ (log t) β η ((β * δ - η * γ) * log t) c₀
      (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) W a z') :=
    (measurable_innerKvG_uncurry hΔ δ γ (log t) β η ((β * δ - η * γ) * log t) c₀
      (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) hW ha).comp
      (measurable_const.prodMk measurable_id)
  rw [← lintegral_comp_mulVec_add (transMat κ Q) hΔ (transShift κ Q δ γ (log t) z') hmeasK]
  refine lintegral_congr fun y ↦ ?_
  have hu := logTruth_sum_elim (ρ := ρ) (D := D) (γ := γ) (δ := δ) (Q := Q) (κ := κ) hq ht z' y
  have hlift := fibreLift_mulVec_add hΔ δ γ (log t) z' y
  unfold innerKvG
  rw [hlift]
  set sh := transShift κ Q δ γ (log t) z' with hsh
  set v := transMat κ Q *ᵥ y + sh with hvdef
  have hv := transMat_mulVec_add_shift κ Q δ γ (log t) z' y
  rw [← hsh, ← hvdef] at hv
  have hs : v 0 = ∑ i, κ i * Sum.elim z' y i - δ * log t := by rw [hv]; rfl
  have hh : v 1 = γ * log t - ∑ i, Q i * Sum.elim z' y i := by rw [hv]; rfl
  have horth : {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}.indicator (fun _ ↦ (1 : ℝ≥0∞))
      (Sum.elim z' y) =
      {z' : Fin k → ℝ | ∀ j, 0 < z' j}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z' *
        ((fun y ↦ transMat κ Q *ᵥ y + sh) '' {y : Fin 2 → ℝ | ∀ j, 0 < y j}).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) v := by
    have hmem : v ∈ (fun y ↦ transMat κ Q *ᵥ y + sh) '' {y : Fin 2 → ℝ | ∀ j, 0 < y j} ↔
        ∀ j, 0 < y j := (injective_mulVec_add hΔ sh).mem_set_image
    by_cases hz : ∀ j, 0 < z' j
    · by_cases hy : ∀ j, 0 < y j
      · rw [Set.indicator_of_mem (show Sum.elim z' y ∈ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}
          from Sum.forall.mpr ⟨hz, hy⟩),
          Set.indicator_of_mem (show z' ∈ {z' : Fin k → ℝ | ∀ j, 0 < z' j} from hz),
          Set.indicator_of_mem (hmem.mpr hy), one_mul]
      · rw [Set.indicator_of_notMem (show Sum.elim z' y ∉ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}
          from fun h ↦ hy (Sum.forall.mp h).2), Set.indicator_of_notMem (fun h ↦ hy (hmem.mp h)),
          mul_zero]
    · rw [Set.indicator_of_notMem (show Sum.elim z' y ∉ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}
        from fun h ↦ hz (Sum.forall.mp h).1),
        Set.indicator_of_notMem (show z' ∉ {z' : Fin k → ℝ | ∀ j, 0 < z' j} from hz), zero_mul]
  have hcut : (logCut ρ D γ q t Q).indicator (fun _ ↦ (1 : ℝ≥0∞)) (Sum.elim z' y) =
      (Ioi (-(q * log (ρ / D) + (∑ i, Q i) * log ρ))).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) := by
    have hiff : Sum.elim z' y ∈ logCut ρ D γ q t Q ↔
        v 1 ∈ Ioi (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) := by
      rw [hh]
      simp only [logCut, Set.mem_ofPred_eq, mem_Ioi]
      constructor <;> intro h <;> linarith
    by_cases hcz : Sum.elim z' y ∈ logCut ρ D γ q t Q
    · rw [Set.indicator_of_mem hcz, Set.indicator_of_mem (hiff.mp hcz)]
    · rw [Set.indicator_of_notMem hcz, Set.indicator_of_notMem (fun h ↦ hcz (hiff.mpr h))]
  have hexp1 : exp (-(∑ i, c i * Sum.elim z' y i)) =
      exp (-(β * v 0 + η * v 1 + (β * δ - η * γ) * log t)) := by
    congr 1
    rw [hs, hh]
    simp only [hc]
    have e : ∑ i, (β * κ i - η * Q i) * Sum.elim z' y i =
        β * ∑ i, κ i * Sum.elim z' y i - η * ∑ i, Q i * Sum.elim z' y i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [e]
    ring
  have hexp2 : ∀ x : ℝ, exp (-(c₀ * exp (δ * log t) * x * exp (-(∑ i, κ i * Sum.elim z' y i)))) =
      exp (-(c₀ * x * exp (-v 0))) := by
    intro x
    congr 1
    rw [hs, neg_sub, Real.exp_sub, Real.exp_neg]
    ring
  unfold logIntegrandG
  rw [horth, hcut, hu, hexp1, hexp2]

/-- **Tonelli** with general units: the transverse variables outside. -/
theorem lintegral_innerKvG_swap {ρ D q : ℝ} {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (δ γ L β η mL c₀ h₀ : ℝ)
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) :
    ∫⁻ z' : Fin k → ℝ, ∫⁻ v : Fin 2 → ℝ, innerKvG ρ D q κ Q δ γ L β η mL c₀ h₀ W a z' v =
      ∫⁻ v : Fin 2 → ℝ, ∫⁻ z' : Fin k → ℝ, innerKvG ρ D q κ Q δ γ L β η mL c₀ h₀ W a z' v :=
  lintegral_lintegral_swap (μ := volume) (ν := volume)
    ((measurable_innerKvG_uncurry hΔ δ γ L β η mL c₀ h₀ hW ha).aemeasurable
      (μ := volume.prod volume))

/-- The transverse weight of the general model at `v`, with the fibre integral of the amplitude
`W(x, u(h)) e^{-c₀ a(x, u(h)) e^{-s}}` in place of the fibre volume. -/
theorem lintegral_innerKvG_eq {ρ D q : ℝ} {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (δ γ L β η mL c₀ h₀ : ℝ)
    (W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ) (v : Fin 2 → ℝ) :
    ∫⁻ z' : Fin k → ℝ, innerKvG ρ D q κ Q δ γ L β η mL c₀ h₀ W a z' v =
      (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
        ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + mL))) *
        ∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal
          (W (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
            exp (-(c₀ * a (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
              exp (-v 0)))) := by
  rw [← lintegral_indicator (measurableSet_fibreSet hΔ δ γ L v),
    ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top (indicator_one_ne_top _ _) ENNReal.ofReal_ne_top)]
  refine lintegral_congr fun z' ↦ ?_
  unfold innerKvG
  by_cases hz : ∀ j, 0 < z' j
  · by_cases hv : v ∈ (fun y ↦ transMat κ Q *ᵥ y + transShift κ Q δ γ L z') ''
        {y : Fin 2 → ℝ | ∀ j, 0 < y j}
    · rw [Set.indicator_of_mem (show z' ∈ {z' : Fin k → ℝ | ∀ j, 0 < z' j} from hz),
        Set.indicator_of_mem hv,
        Set.indicator_of_mem (show z' ∈ fibreSet κ Q δ γ L v from ⟨hz, hv⟩), one_mul, one_mul]
      rw [show W (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
          exp (-(β * v 0 + η * v 1 + mL)) *
          exp (-(c₀ * a (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
            exp (-v 0))) = exp (-(β * v 0 + η * v 1 + mL)) *
          (W (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
            exp (-(c₀ * a (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
              exp (-v 0)))) by ring, ENNReal.ofReal_mul (exp_pos _).le]
      ring
    · rw [Set.indicator_of_notMem hv,
        Set.indicator_of_notMem (show z' ∉ fibreSet κ Q δ γ L v from fun h ↦ hv h.2)]
      ring
  · rw [Set.indicator_of_notMem (show z' ∉ {z' : Fin k → ℝ | ∀ j, 0 < z' j} from hz),
      Set.indicator_of_notMem (show z' ∉ fibreSet κ Q δ γ L v from fun h ↦ hz h.1)]
    ring


/-! ### The amplitude and its trace -/

/-- The amplitude at the transverse point `v`, as a function of the chart point:
`W(x, u(h)) e^{-c₀ a(x, u(h)) e^{-s}}`. -/
noncomputable def ampG (ρ D q c₀ : ℝ) (Q : Fin k ⊕ Fin 2 → ℝ)
    (W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ) (v : Fin 2 → ℝ) (x : Fin k ⊕ Fin 2 → ℝ) : ℝ :=
  W x (truthOf ρ D q Q (v 1)) * exp (-(c₀ * a x (truthOf ρ D q Q (v 1)) * exp (-v 0)))

theorem ampG_nonneg_le {ρ D q c₀ Wstar amin : ℝ} (hc : 0 < c₀)
    {Q : Fin k ⊕ Fin 2 → ℝ} {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) (v : Fin 2 → ℝ)
    (x : Fin k ⊕ Fin 2 → ℝ) :
    0 ≤ ampG ρ D q c₀ Q W a v x ∧
      ampG ρ D q c₀ Q W a v x ≤ Wstar * exp (-(c₀ * amin * exp (-v 0))) := by
  unfold ampG
  have h1 := hWb x (truthOf ρ D q Q (v 1))
  have h2 := hab x (truthOf ρ D q Q (v 1))
  refine ⟨mul_nonneg h1.1 (exp_pos _).le, ?_⟩
  refine mul_le_mul h1.2 ?_ (exp_pos _).le (h1.1.trans h1.2)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc.le) (exp_pos _).le

theorem ampG_le {ρ D q c₀ Wstar amin : ℝ} (hc : 0 < c₀) (hamin : 0 < amin)
    {Q : Fin k ⊕ Fin 2 → ℝ} {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) (v : Fin 2 → ℝ)
    (x : Fin k ⊕ Fin 2 → ℝ) : ampG ρ D q c₀ Q W a v x ≤ Wstar := by
  refine (ampG_nonneg_le hc hWb hab v x).2.trans ?_
  have hW : 0 ≤ Wstar := (hWb x 0).1.trans (hWb x 0).2
  refine mul_le_of_le_one_right hW ?_
  rw [Real.exp_le_one_iff]
  have := hc.le
  have := hamin.le
  have := (exp_pos (-v 0)).le
  nlinarith [mul_nonneg (mul_nonneg hc.le hamin.le) (exp_pos (-v 0)).le]

theorem measurable_ampG (ρ D q c₀ : ℝ) (Q : Fin k ⊕ Fin 2 → ℝ)
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) (v : Fin 2 → ℝ) :
    Measurable (ampG ρ D q c₀ Q W a v) := by
  unfold ampG
  refine (hW.comp (measurable_id.prodMk measurable_const)).mul (Real.measurable_exp.comp ?_)
  exact ((measurable_const.mul (ha.comp (measurable_id.prodMk measurable_const))).mul
    measurable_const).neg

/-- The amplitude converges to its trace as `x → 0` inside the box. -/
theorem ampG_tendsto {ρ D q c₀ : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    {Q : Fin k ⊕ Fin 2 → ℝ} {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} {Wtr atr : ℝ → ℝ}
    (hWtr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ W x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr u)))
    (hatr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ a x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr u)))
    {v : Fin 2 → ℝ} (hv : -(q * log (ρ / D) + (∑ i, Q i) * log ρ) < v 1) :
    Tendsto (ampG ρ D q c₀ Q W a v) (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0)
      (𝓝 (Wtr (truthOf ρ D q Q (v 1)) *
        exp (-(c₀ * atr (truthOf ρ D q Q (v 1)) * exp (-v 0))))) := by
  have hu := truthOf_mem_Ioo hρ hD hq Q hv
  have h2 : Tendsto (fun x ↦ exp (-(c₀ * a x (truthOf ρ D q Q (v 1)) * exp (-v 0))))
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0)
      (𝓝 (exp (-(c₀ * atr (truthOf ρ D q Q (v 1)) * exp (-v 0))))) :=
    (Real.continuous_exp.tendsto _).comp
      (((hatr _ hu).const_mul c₀).mul_const (exp (-v 0))).neg
  exact (hWtr _ hu).mul h2

/-! ### Dominated convergence with the weighted fibre limit -/

theorem innerKvG_eq_mul (ρ D q : ℝ) (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L β η mL c₀ h₀ : ℝ)
    (W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ) (z' : Fin k → ℝ) (v : Fin 2 → ℝ) :
    innerKvG ρ D q κ Q δ γ L β η mL c₀ h₀ W a z' v =
      ENNReal.ofReal (exp (-mL)) * innerKvG ρ D q κ Q δ γ L β η 0 c₀ h₀ W a z' v := by
  unfold innerKvG
  rw [show exp (-(β * v 0 + η * v 1 + mL)) = exp (-mL) * exp (-(β * v 0 + η * v 1 + 0)) by
    rw [← Real.exp_add]; congr 1; ring]
  rw [show W (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
      (exp (-mL) * exp (-(β * v 0 + η * v 1 + 0))) *
      exp (-(c₀ * a (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
        exp (-v 0))) = exp (-mL) *
      (W (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
        exp (-(β * v 0 + η * v 1 + 0)) *
        exp (-(c₀ * a (negExpMap ρ (fibreLift κ Q δ γ L v z')) (truthOf ρ D q Q (v 1)) *
          exp (-v 0)))) by ring, ENNReal.ofReal_mul (exp_pos _).le]
  ring

/-- **The transverse limit with general units.** -/
theorem tendsto_lintegral_innerKvG {ρ D q : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {β η c₀ δ γ : ℝ}
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0) (hβ : 0 < β) (hη : 0 < η) (hc : 0 < c₀)
    (hδ : 0 ≤ δ) {Wstar amin : ℝ} (hamin : 0 < amin) {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    (hWm : Measurable (Function.uncurry W)) (ham : Measurable (Function.uncurry a))
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) {Wtr atr : ℝ → ℝ}
    (hWtr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ W x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr u)))
    (hatr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ a x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr u))) :
    Tendsto (fun L ↦ ∫⁻ v : Fin 2 → ℝ, (∫⁻ z' : Fin k → ℝ, innerKvG ρ D q κ Q δ γ L β η 0 c₀
        (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) W a z' v) / ENNReal.ofReal (L ^ k)) atTop
      (𝓝 (∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 c₀ (-(q * log (ρ / D) + (∑ i, Q i) * log ρ))
        (fun h ↦ Wtr (truthOf ρ D q Q h)) (fun h ↦ atr (truthOf ρ D q Q h)) v *
        volume (facePolytope κ Q δ γ))) := by
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
    · have hlim := tendsto_lintegral_fibre_weighted hΔ hκ hc₀ hc₁ v hρ
        (measurable_ampG ρ D q c₀ Q hWm ham v)
        (fun x ↦ ⟨(ampG_nonneg_le hc hWb hab v x).1, ampG_le hc hamin hWb hab v x⟩)
        (ampG_tendsto hρ hD hq hWtr hatr hv)
      have := ENNReal.Tendsto.const_mul (a := (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
        ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0)))) hlim
        (Or.inr (ENNReal.mul_ne_top (indicator_one_ne_top _ _) ENNReal.ofReal_ne_top))
      have hlimval : (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
          ENNReal.ofReal (exp (-(β * v 0 + η * v 1 + 0))) *
          (ENNReal.ofReal (Wtr (truthOf ρ D q Q (v 1)) *
            exp (-(c₀ * atr (truthOf ρ D q Q (v 1)) * exp (-v 0)))) *
            volume (facePolytope κ Q δ γ)) =
          vWeightT β η 0 c₀ h₀ (fun h ↦ Wtr (truthOf ρ D q Q h))
            (fun h ↦ atr (truthOf ρ D q Q h)) v * volume (facePolytope κ Q δ γ) := by
        unfold vWeightT
        rw [Set.indicator_of_mem hv, one_mul, one_mul, ← mul_assoc,
          ← ENNReal.ofReal_mul (exp_pos _).le]
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
        rw [Set.indicator_of_notMem hv, zero_mul, zero_mul, ENNReal.zero_div]
      simp_rw [hz]
      unfold vWeightT
      rw [Set.indicator_of_notMem hv, zero_mul, zero_mul]
      exact tendsto_const_nhds


/-! ### The theorem -/

theorem modelIntegrand_general_nonneg {ρ B D γ q δ t : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} (hW : ∀ x u, 0 ≤ W x u) (x : Fin k ⊕ Fin 2 → ℝ) :
    0 ≤ modelIntegrand ρ B D γ q δ Q κ r W a t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q Q t
  · rw [Set.indicator_of_mem hx]
    have hx0 : ∀ i, 0 < x i := fun i ↦ ((Set.mem_univ_pi.mp hx.1) i).1
    exact mul_nonneg (mul_nonneg (hW _ _) (Finset.prod_nonneg fun i _ ↦
      Real.rpow_nonneg (hx0 i).le _)) (exp_pos _).le
  · rw [Set.indicator_of_notMem hx]

/-- **The transverse active-truth face theorem with general units (trace replacement).** For
jointly measurable units `W(x, u)`, `a(x, u)` with `0 ≤ W ≤ W_*`, `a ≥ a_- > 0` and traces
`W_tr(u)`, `a_tr(u)` as `x → 0` inside the box (measurable, with the same bounds on `(0, ρ)`):
`t^{γp + βδ − ηγ}/(log t)^k · K(t) → A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ·
∫_0^ρ u^{qη−1} W_tr(u) a_tr(u)^{-β} du`. -/
theorem tendsto_modelKernel_general {ρ A B D γ p q δ β η : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    {Wstar amin : ℝ} (hamin : 0 < amin) (hWm : Measurable (Function.uncurry W))
    (ham : Measurable (Function.uncurry a)) (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar)
    (hab : ∀ x u, amin ≤ a x u) {Wtr atr : ℝ → ℝ} (hWtrm : Measurable Wtr)
    (hatrm : Measurable atr) (hWtrb : ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ Wtr u ∧ Wtr u ≤ Wstar)
    (hatrb : ∀ u ∈ Ioo (0 : ℝ) ρ, amin ≤ atr u)
    (hWtr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ W x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr u)))
    (hatr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ a x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr u))) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r W a t) atTop
      (𝓝 (A * Gamma β * B ^ (-β) * q * D ^ (-(q * η)) *
        (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| *
        ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr u * atr u ^ (-β)))) := by
  set c₀ := B * ρ ^ (∑ i, κ i) with hc₀def
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  set wh : ℝ → ℝ := fun h ↦ Wtr (truthOf ρ D q Q h) with hwhdef
  set ah : ℝ → ℝ := fun h ↦ atr (truthOf ρ D q Q h) with hahdef
  have hc : 0 < c₀ := mul_pos hB (Real.rpow_pos_of_pos hρ _)
  have hwh : Measurable wh := hWtrm.comp (continuous_truthOf ρ D q Q).measurable
  have hah : Measurable ah := hatrm.comp (continuous_truthOf ρ D q Q).measurable
  have hwb : ∀ h, h₀ < h → 0 ≤ wh h ∧ wh h ≤ Wstar := fun h hh ↦
    hWtrb _ (truthOf_mem_Ioo hρ hD hq Q hh)
  have hab' : ∀ h, h₀ < h → amin ≤ ah h := fun h hh ↦ hatrb _ (truthOf_mem_Ioo hρ hD hq Q hh)
  have hF := volume_facePolytope_ne_top hΔ hκ δ γ
  -- the transverse limit
  have hlim := (tendsto_lintegral_innerKvG hρ hD hq hΔ hκ hc₀ hc₁ hβ hη hc hδ hamin hWm ham hWb
    hab hWtr hatr).comp Real.tendsto_log_atTop
  rw [lintegral_mul_const _ (measurable_vWeightT _ _ _ _ _ hwh hah),
    lintegral_vWeightT_zero hβ hη hc hamin hwh hah hwb hab'] at hlim
  have hint : ∫ h in Ioi h₀, Gamma β * (c₀ * ah h) ^ (-β) * (exp (-(η * h)) * wh h) =
      Gamma β * c₀ ^ (-β) * (q * (D * ρ ^ (-(∑ i, Q i) / q)) ^ (-(q * η)) *
        ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr u * atr u ^ (-β))) := by
    rw [← integral_Ioi_truthOf hρ hD hq Q (fun u ↦ Wtr u * atr u ^ (-β)), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun h hh ↦ ?_
    have hu := truthOf_mem_Ioo hρ hD hq Q hh
    have ha0 : 0 ≤ atr (truthOf ρ D q Q h) := hamin.le.trans (hatrb _ hu)
    simp only [hwhdef, hahdef]
    rw [Real.mul_rpow hc.le ha0]
    ring
  rw [hint] at hlim
  set I := ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (Wtr u * atr u ^ (-β)) with hI
  have hI0 : 0 ≤ I := by
    rw [hI]
    refine setIntegral_nonneg measurableSet_Ioo fun u hu ↦ ?_
    exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (mul_nonneg (hWtrb u hu).1 (Real.rpow_nonneg
      (hamin.le.trans (hatrb u hu)) _))
  have hG : 0 ≤ Gamma β * c₀ ^ (-β) * (q * (D * ρ ^ (-(∑ i, Q i) / q)) ^ (-(q * η)) * I) := by
    have := (Real.Gamma_pos_of_pos hβ).le
    have := (Real.rpow_pos_of_pos hc (-β)).le
    have h2 : 0 < D * ρ ^ (-(∑ i, Q i) / q) := by positivity
    have := (Real.rpow_pos_of_pos h2 (-(q * η))).le
    positivity
  have hne : ENNReal.ofReal (Gamma β * c₀ ^ (-β) *
      (q * (D * ρ ^ (-(∑ i, Q i) / q)) ^ (-(q * η)) * I)) * volume (facePolytope κ Q δ γ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF
  have hlim2 := ((ENNReal.tendsto_toReal hne).comp hlim).const_mul
    (A * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hG, ← mul_assoc] at hlim2
  have hconst := trace_const_eq (q := q) (η := η) hρ hD hq hB hr
  rw [← hc₀def] at hconst
  have hval : A * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹ *
      (Gamma β * c₀ ^ (-β) * (q * (D * ρ ^ (-(∑ i, Q i) / q)) ^ (-(q * η)) * I)) *
      (volume (facePolytope κ Q δ γ)).toReal =
      A * Gamma β * B ^ (-β) * q * D ^ (-(q * η)) * (volume (facePolytope κ Q δ γ)).toReal /
        |(transMat κ Q).det| * I := by
    linear_combination (A * Gamma β * q * (volume (facePolytope κ Q δ γ)).toReal *
      |(transMat κ Q).det|⁻¹ * I) * hconst
  rw [hval] at hlim2
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
  have hJ : ∫⁻ v : Fin 2 → ℝ, (∫⁻ z' : Fin k → ℝ,
      innerKvG ρ D q κ Q δ γ (log t) β η 0 c₀ h₀ W a z' v) / ENNReal.ofReal (log t ^ k) =
      (∫⁻ v : Fin 2 → ℝ, ∫⁻ z' : Fin k → ℝ,
        innerKvG ρ D q κ Q δ γ (log t) β η 0 c₀ h₀ W a z' v) / ENNReal.ofReal (log t ^ k) := by
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const' _ _
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hL k)).ne')
  rw [hJ]
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
