/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthUniform

/-!
# The trace model in logarithmic coordinates

Astra round 9, item 1: units depending on the truth coordinate only, `W(x, u) = w(u)`,
`a(x, u) = a(u)`. In the log coordinates `x = ρe^{-z}` the truth coordinate is
`u_t(z) = D t^{-γ/q} ρ^{-∑Q/q} e^{Q·z/q}` (`logTruth`), and the model integrand becomes
`1_{logCut} w(u_t) ρ^{∑(r+1)} e^{-c·z} e^{-B t^δ a(u_t) ρ^{∑κ} e^{-κ·z}}`
(`modelIntegrand_trace_negExp`); the `lintegral` form is `lintegral_modelIntegrand_trace`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

section Generic

variable {ι : Type*} [Fintype ι]

/-- The truth coordinate in logarithmic coordinates: `u_t(z) = D t^{-γ/q} ρ^{-∑Q/q} e^{Q·z/q}`. -/
noncomputable def logTruth (ρ D γ q t : ℝ) (Q : ι → ℝ) (z : ι → ℝ) : ℝ :=
  D * t ^ (-(γ / q)) * (ρ ^ (-(∑ i, Q i) / q) * exp ((∑ i, Q i * z i) / q))

theorem cutVar_negExp_eq_logTruth {ρ D γ q t : ℝ} (hρ : 0 < ρ) (Q : ι → ℝ) (z : ι → ℝ) :
    cutVar D γ q Q t (negExpMap ρ z) = logTruth ρ D γ q t Q z :=
  cutVar_negExp hρ Q z

/-- The trace-model integrand at `ρ e^{-z}`, `z > 0`, with the Jacobian. -/
theorem modelIntegrand_trace_negExp {ρ B D γ q δ : ℝ} {Q κ r : ι → ℝ} {t : ℝ} (w a : ℝ → ℝ)
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t) {z : ι → ℝ} (hz : ∀ i, 0 < z i) :
    (∏ i, ρ * exp (-z i)) *
        modelIntegrand ρ B D γ q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ a u) t (negExpMap ρ z) =
      (logCut ρ D γ q t Q).indicator (fun z ↦ w (logTruth ρ D γ q t Q z) *
        ρ ^ (∑ i, (r i + 1)) * exp (-(∑ i, (r i + 1) * z i)) *
        exp (-(B * t ^ δ * a (logTruth ρ D γ q t Q z) * ρ ^ (∑ i, κ i) *
          exp (-(∑ i, κ i * z i))))) z := by
  unfold modelIntegrand modelDomain
  have hbox : negExpMap ρ z ∈ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ := by
    rw [← image_negExpMap_orthant hρ]
    exact ⟨z, fun i _ ↦ hz i, rfl⟩
  by_cases hcut : z ∈ logCut ρ D γ q t Q
  · rw [Set.indicator_of_mem hcut, Set.indicator_of_mem
      (show negExpMap ρ z ∈ (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ) ∩
        {x | cutVar D γ q Q t x < ρ} from ⟨hbox, (cutVar_negExp_lt_iff hρ hD hq ht Q z).mpr hcut⟩)]
    beta_reduce
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
    have eJ : ∏ i, ρ * exp (-z i) = ρ ^ (Fintype.card ι : ℝ) * exp (-(∑ i, z i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
        Finset.sum_neg_distrib, Real.rpow_natCast]
    rw [er, eκ, eJ]
    have e1 : ρ ^ (∑ i, (r i + 1)) = ρ ^ (∑ i, r i) * ρ ^ (Fintype.card ι : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Real.rpow_add hρ]
    have e2 : exp (-(∑ i, (r i + 1) * z i)) = exp (-(∑ i, r i * z i)) * exp (-(∑ i, z i)) := by
      rw [← Real.exp_add]
      congr 1
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
      ring
    rw [e1, e2, show B * t ^ δ * a (logTruth ρ D γ q t Q z) *
      (ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i))) =
      B * t ^ δ * a (logTruth ρ D γ q t Q z) * ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i)) by ring]
    ring
  · rw [Set.indicator_of_notMem hcut, Set.indicator_of_notMem
      (fun h ↦ hcut ((cutVar_negExp_lt_iff hρ hD hq ht Q z).mp h.2)), mul_zero]

end Generic

variable {k : ℕ}

/-- The log-form trace integrand on `Fin k ⊕ Fin 2`, in `lintegral` form. -/
noncomputable def logIntegrandT (ρ D γ q t : ℝ) (Q c κ : Fin k ⊕ Fin 2 → ℝ) (B' : ℝ)
    (w a : ℝ → ℝ) (z : Fin k ⊕ Fin 2 → ℝ) : ℝ≥0∞ :=
  {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z *
    (logCut ρ D γ q t Q).indicator (fun _ ↦ (1 : ℝ≥0∞)) z *
    ENNReal.ofReal (w (logTruth ρ D γ q t Q z) * exp (-(∑ i, c i * z i)) *
      exp (-(B' * a (logTruth ρ D γ q t Q z) * exp (-(∑ i, κ i * z i)))))

theorem measurable_logTruth (ρ D γ q t : ℝ) (Q : Fin k ⊕ Fin 2 → ℝ) :
    Measurable (logTruth ρ D γ q t Q) := by
  unfold logTruth
  fun_prop

theorem measurable_logIntegrandT (ρ D γ q t : ℝ) (Q c κ : Fin k ⊕ Fin 2 → ℝ) (B' : ℝ)
    {w a : ℝ → ℝ} (hw : Measurable w) (ha : Measurable a) :
    Measurable (logIntegrandT ρ D γ q t Q c κ B' w a) := by
  unfold logIntegrandT
  refine ((measurable_const.indicator measurableSet_orthantSet).mul
    (measurable_const.indicator (measurableSet_logCut _ _ _ _ _ _))).mul ?_
  refine ENNReal.measurable_ofReal.comp ?_
  refine ((hw.comp (measurable_logTruth _ _ _ _ _ _)).mul (Continuous.measurable (by fun_prop))).mul
    (Real.measurable_exp.comp ?_)
  exact ((measurable_const.mul (ha.comp (measurable_logTruth _ _ _ _ _ _))).mul
    (Continuous.measurable (by fun_prop))).neg

/-- The `lintegral` of the trace-model integrand (nonnegative `w`) is `ρ^{∑(r+1)}` times the
`lintegral` of the log-form trace integrand. -/
theorem lintegral_modelIntegrand_trace {ρ B D γ q δ : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ} {t : ℝ}
    (w a : ℝ → ℝ) (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ a u) t x) =
      ENNReal.ofReal (ρ ^ (∑ i, (r i + 1))) *
        ∫⁻ z, logIntegrandT ρ D γ q t Q (fun i ↦ r i + 1) κ (B * t ^ δ * ρ ^ (∑ i, κ i)) w a z := by
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hsupp : (fun x ↦ ENNReal.ofReal
      (modelIntegrand ρ B D γ q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ a u) t x)) =
      (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ).indicator fun x ↦ ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ a u) t x) := by
    funext x
    by_cases hx : x ∈ Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      unfold modelIntegrand
      rw [Set.indicator_of_notMem (fun h' ↦ hx h'.1), ENNReal.ofReal_zero]
  rw [hsupp, lintegral_indicator hbox, lintegral_box_eq_orthant hρ]
  have horth : (fun z ↦ logIntegrandT ρ D γ q t Q (fun i ↦ r i + 1) κ
      (B * t ^ δ * ρ ^ (∑ i, κ i)) w a z) =
      (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioi (0 : ℝ)).indicator fun z ↦
        logIntegrandT ρ D γ q t Q (fun i ↦ r i + 1) κ (B * t ^ δ * ρ ^ (∑ i, κ i)) w a z := by
    funext z
    by_cases hz : z ∈ Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      unfold logIntegrandT
      rw [← orthantSet_eq_pi] at hz
      rw [Set.indicator_of_notMem hz, zero_mul, zero_mul]
  rw [horth, lintegral_indicator (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    fun z hz ↦ ?_
  have hz' : ∀ i, 0 < z i := fun i ↦ (Set.mem_univ_pi.mp hz) i
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ ↦ by positivity),
    modelIntegrand_trace_negExp w a hρ hD hq ht hz']
  unfold logIntegrandT
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

end Laplace.Multi
