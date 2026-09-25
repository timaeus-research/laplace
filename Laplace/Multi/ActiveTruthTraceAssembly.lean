/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthTraceModel

/-!
# The transverse coordinates of the trace model

Steps 2–3 for truth-dependent units: in the transverse coordinates `v = (s, h)` the truth
coordinate is the `t`-free `u(h) = D ρ^{-∑Q/q} e^{-h/q}` (`truthOf`, `logTruth_sum_elim`), so the
inner substitution (`lintegral_inner_substT`) and Tonelli (`lintegral_innerKvT_swap`) go through
with the weight `vWeightT`, which carries `w(u(h))` and the Boltzmann constant `c₀ a(u(h))`; the
fibre set is the same as for constant units.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-- The truth coordinate as a function of the transverse variable `h`: `D ρ^{-∑Q/q} e^{-h/q}`. -/
noncomputable def truthOf (ρ D q : ℝ) (Q : Fin k ⊕ Fin 2 → ℝ) (h : ℝ) : ℝ :=
  D * ρ ^ (-(∑ i, Q i) / q) * exp (-(h / q))

theorem continuous_truthOf (ρ D q : ℝ) (Q : Fin k ⊕ Fin 2 → ℝ) : Continuous (truthOf ρ D q Q) := by
  unfold truthOf
  fun_prop

/-- On the affine change of variables, `u_t(z) = u(h)`. -/
theorem logTruth_sum_elim {ρ D γ q t δ : ℝ} {Q κ : Fin k ⊕ Fin 2 → ℝ} (hq : 0 < q) (ht : 0 < t)
    (z' : Fin k → ℝ) (y : Fin 2 → ℝ) :
    logTruth ρ D γ q t Q (Sum.elim z' y) =
      truthOf ρ D q Q ((transMat κ Q *ᵥ y + transShift κ Q δ γ (log t) z') 1) := by
  have hh : (transMat κ Q *ᵥ y + transShift κ Q δ γ (log t) z') 1 =
      γ * log t - ∑ i, Q i * Sum.elim z' y i := by
    rw [transMat_mulVec_add_shift]
    rfl
  rw [hh]
  unfold logTruth truthOf
  rw [Real.rpow_def_of_pos ht]
  have e : exp (log t * (-(γ / q))) * exp ((∑ i, Q i * Sum.elim z' y i) / q) =
      exp (-((γ * log t - ∑ i, Q i * Sum.elim z' y i) / q)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [← e]
  ring

/-- The transverse integrand of the trace model: as `innerKv`, with `w(u(h))` and the Boltzmann
constant `c₀ a(u(h))`; `wh, ah` are the units composed with `u(·)`. -/
noncomputable def innerKvT (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L β η mL c₀ h₀ : ℝ) (wh ah : ℝ → ℝ)
    (z' : Fin k → ℝ) (v : Fin 2 → ℝ) : ℝ≥0∞ :=
  {z' : Fin k → ℝ | ∀ j, 0 < z' j}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z' *
    ((fun y ↦ transMat κ Q *ᵥ y + transShift κ Q δ γ L z') ''
      {y : Fin 2 → ℝ | ∀ j, 0 < y j}).indicator (fun _ ↦ (1 : ℝ≥0∞)) v *
    (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
    ENNReal.ofReal (wh (v 1) * exp (-(β * v 0 + η * v 1 + mL)) *
      exp (-(c₀ * ah (v 1) * exp (-v 0))))

/-- **The inner substitution for the trace model.** -/
theorem lintegral_inner_substT {ρ D γ q t δ β η c₀ : ℝ} {Q c κ : Fin k ⊕ Fin 2 → ℝ}
    {w a : ℝ → ℝ} (hw : Measurable w) (ha : Measurable a) (hq : 0 < q) (ht : 0 < t)
    (hc : ∀ i, c i = β * κ i - η * Q i) (hΔ : (transMat κ Q).det ≠ 0) (z' : Fin k → ℝ) :
    ∫⁻ y : Fin 2 → ℝ, logIntegrandT ρ D γ q t Q c κ (c₀ * exp (δ * log t)) w a (Sum.elim z' y) =
      ENNReal.ofReal |(transMat κ Q).det|⁻¹ *
        ∫⁻ v, innerKvT κ Q δ γ (log t) β η ((β * δ - η * γ) * log t) c₀
          (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) (fun h ↦ w (truthOf ρ D q Q h))
          (fun h ↦ a (truthOf ρ D q Q h)) z' v := by
  have hmeasK : Measurable (innerKvT κ Q δ γ (log t) β η ((β * δ - η * γ) * log t) c₀
      (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) (fun h ↦ w (truthOf ρ D q Q h))
      (fun h ↦ a (truthOf ρ D q Q h)) z') := by
    unfold innerKvT
    refine ((measurable_const.mul ?_).mul ?_).mul ?_
    · exact measurable_const.indicator (measurableSet_image_mulVec_add_orthant hΔ _)
    · exact (measurable_const.indicator measurableSet_Ioi).comp (measurable_pi_apply 1)
    · refine ENNReal.measurable_ofReal.comp ?_
      have hu : Measurable fun v : Fin 2 → ℝ ↦ truthOf ρ D q Q (v 1) :=
        (continuous_truthOf ρ D q Q).measurable.comp (measurable_pi_apply 1)
      refine ((hw.comp hu).mul (Real.measurable_exp.comp
        (((measurable_const.mul (measurable_pi_apply 0)).add
          (measurable_const.mul (measurable_pi_apply 1))).add measurable_const).neg)).mul
        (Real.measurable_exp.comp ?_)
      exact ((measurable_const.mul (ha.comp hu)).mul
        (Real.measurable_exp.comp (measurable_pi_apply 0).neg)).neg
  rw [← lintegral_comp_mulVec_add (transMat κ Q) hΔ (transShift κ Q δ γ (log t) z') hmeasK]
  refine lintegral_congr fun y ↦ ?_
  have hu := logTruth_sum_elim (ρ := ρ) (D := D) (γ := γ) (δ := δ) (Q := Q) (κ := κ) hq ht z' y
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
  have hexp2 : exp (-(c₀ * exp (δ * log t) * a (truthOf ρ D q Q (v 1)) *
      exp (-(∑ i, κ i * Sum.elim z' y i)))) =
      exp (-(c₀ * a (truthOf ρ D q Q (v 1)) * exp (-v 0))) := by
    congr 1
    rw [hs, neg_sub, Real.exp_sub, Real.exp_neg]
    ring
  unfold logIntegrandT innerKvT
  rw [horth, hcut, hu, hexp1, hexp2]

/-! ### Tonelli -/

/-- The transverse weight of the trace model: `1_{h > h₀} w(u(h)) e^{-βs − ηh − mL}
e^{-c₀ a(u(h)) e^{-s}}`. -/
noncomputable def vWeightT (β η mL c₀ h₀ : ℝ) (wh ah : ℝ → ℝ) (v : Fin 2 → ℝ) : ℝ≥0∞ :=
  (Ioi h₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) (v 1) *
    ENNReal.ofReal (wh (v 1) * exp (-(β * v 0 + η * v 1 + mL)) *
      exp (-(c₀ * ah (v 1) * exp (-v 0))))

theorem innerKvT_eq (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ L β η mL c₀ h₀ : ℝ) (wh ah : ℝ → ℝ)
    (z' : Fin k → ℝ) (v : Fin 2 → ℝ) :
    innerKvT κ Q δ γ L β η mL c₀ h₀ wh ah z' v =
      (fibreSet κ Q δ γ L v).indicator (fun _ ↦ (1 : ℝ≥0∞)) z' * vWeightT β η mL c₀ h₀ wh ah v := by
  unfold innerKvT vWeightT
  by_cases hz : ∀ j, 0 < z' j
  · by_cases hv : v ∈ (fun y ↦ transMat κ Q *ᵥ y + transShift κ Q δ γ L z') ''
        {y : Fin 2 → ℝ | ∀ j, 0 < y j}
    · rw [Set.indicator_of_mem (show z' ∈ {z' : Fin k → ℝ | ∀ j, 0 < z' j} from hz),
        Set.indicator_of_mem hv,
        Set.indicator_of_mem (show z' ∈ fibreSet κ Q δ γ L v from ⟨hz, hv⟩)]
      ring
    · rw [Set.indicator_of_notMem hv,
        Set.indicator_of_notMem (show z' ∉ fibreSet κ Q δ γ L v from fun h ↦ hv h.2)]
      ring
  · rw [Set.indicator_of_notMem (show z' ∉ {z' : Fin k → ℝ | ∀ j, 0 < z' j} from hz),
      Set.indicator_of_notMem (show z' ∉ fibreSet κ Q δ γ L v from fun h ↦ hz h.1)]
    ring

theorem measurable_vWeightT (β η mL c₀ h₀ : ℝ) {wh ah : ℝ → ℝ} (hw : Measurable wh)
    (ha : Measurable ah) : Measurable (vWeightT β η mL c₀ h₀ wh ah) := by
  unfold vWeightT
  refine Measurable.mul ?_ ?_
  · exact (measurable_const.indicator measurableSet_Ioi).comp (measurable_pi_apply 1)
  · refine ENNReal.measurable_ofReal.comp ?_
    refine ((hw.comp (measurable_pi_apply 1)).mul (Real.measurable_exp.comp
      (((measurable_const.mul (measurable_pi_apply 0)).add
        (measurable_const.mul (measurable_pi_apply 1))).add measurable_const).neg)).mul
      (Real.measurable_exp.comp ?_)
    exact ((measurable_const.mul (ha.comp (measurable_pi_apply 1))).mul
      (Real.measurable_exp.comp (measurable_pi_apply 0).neg)).neg

/-- **Tonelli** for the trace model. -/
theorem lintegral_innerKvT_swap {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (δ γ L β η mL c₀ h₀ : ℝ) {wh ah : ℝ → ℝ} (hw : Measurable wh) (ha : Measurable ah) :
    ∫⁻ z' : Fin k → ℝ, ∫⁻ v : Fin 2 → ℝ, innerKvT κ Q δ γ L β η mL c₀ h₀ wh ah z' v =
      ∫⁻ v : Fin 2 → ℝ, vWeightT β η mL c₀ h₀ wh ah v * volume (fibreSet κ Q δ γ L v) := by
  simp_rw [innerKvT_eq]
  have hmeas : Measurable (Function.uncurry fun (z' : Fin k → ℝ) (v : Fin 2 → ℝ) ↦
      (fibreSet κ Q δ γ L v).indicator (fun _ ↦ (1 : ℝ≥0∞)) z' *
        vWeightT β η mL c₀ h₀ wh ah v) := by
    have e : (Function.uncurry fun (z' : Fin k → ℝ) (v : Fin 2 → ℝ) ↦
        (fibreSet κ Q δ γ L v).indicator (fun _ ↦ (1 : ℝ≥0∞)) z' *
          vWeightT β η mL c₀ h₀ wh ah v) =
        fun p : (Fin k → ℝ) × (Fin 2 → ℝ) ↦
          {p : (Fin k → ℝ) × (Fin 2 → ℝ) | p.1 ∈ fibreSet κ Q δ γ L p.2}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) p * vWeightT β η mL c₀ h₀ wh ah p.2 := by
      funext p
      rcases p with ⟨z', v⟩
      simp only [Function.uncurry_apply_pair]
      by_cases h : z' ∈ fibreSet κ Q δ γ L v
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (z', v) ∈
          {p : (Fin k → ℝ) × (Fin 2 → ℝ) | p.1 ∈ fibreSet κ Q δ γ L p.2} from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show (z', v) ∉
          {p : (Fin k → ℝ) × (Fin 2 → ℝ) | p.1 ∈ fibreSet κ Q δ γ L p.2} from h)]
    rw [e]
    exact (measurable_const.indicator (measurableSet_fibreSet_prod hΔ δ γ L)).mul
      ((measurable_vWeightT β η mL c₀ h₀ hw ha).comp measurable_snd)
  rw [lintegral_lintegral_swap (μ := volume) (ν := volume)
    (hmeas.aemeasurable (μ := volume.prod volume))]
  refine lintegral_congr fun v ↦ ?_
  rw [lintegral_mul_const _ (measurable_const.indicator (measurableSet_fibreSet hΔ δ γ L v)),
    lintegral_indicator (measurableSet_fibreSet hΔ δ γ L v), setLIntegral_const, one_mul,
    mul_comm]

end Laplace.Multi
