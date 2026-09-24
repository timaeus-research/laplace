/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthLimit

/-!
# The transverse active-truth face theorem (constant units)

The assembly of steps 1–5 (`notes/active_truth_handoff.md`). For the constant-unit model kernel
`K(t) = A t^{-γp} ∫_{(0,ρ)^n, cut} w₀ ∏ x^r e^{-B t^δ a₀ ∏ x^κ} dx` on `n = k + 2` coordinates
with `r + 1 = βκ − ηQ` (the dual certificate), `κ > 0`, the transverse matrix
`M = [[κ_a, κ_b], [−Q_a, −Q_b]]` invertible and the two fibre constraints nondegenerate:

`t^{γp + βδ − ηγ} / (log t)^k · K(t) →
  A w₀ ρ^{∑(r+1)} / |det M| · Γ(β) c₀^{-β} e^{-ηh₀}/η · vol(F')`

with `c₀ = B a₀ ρ^{∑κ}`, `h₀ = −(q log(ρ/D) + (∑Q) log ρ)` and `F'` the projected face
(`tendsto_modelKernel_activeTruth`); the constant simplifies to
`A w₀ Γ(β) (B a₀)^{-β} (ρ/D)^{qη}/η · vol(F')/|det M|` (`tendsto_modelKernel_activeTruth'`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

theorem orthantSet_eq_pi {ι : Type*} :
    {z : ι → ℝ | ∀ i, 0 < z i} = Set.pi univ fun _ ↦ Ioi (0 : ℝ) := by
  ext z
  simp only [Set.mem_univ_pi, mem_Ioi, Set.mem_ofPred_eq]

theorem measurableSet_orthantSet {ι : Type*} [Countable ι] :
    MeasurableSet {z : ι → ℝ | ∀ i, 0 < z i} := by
  rw [orthantSet_eq_pi]
  exact MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi

theorem measurableSet_logCut {ι : Type*} [Fintype ι] (ρ D γ q t : ℝ) (Q : ι → ℝ) :
    MeasurableSet (logCut ρ D γ q t Q) :=
  measurableSet_lt (Finset.measurable_sum _ fun i _ ↦ measurable_const.mul (measurable_pi_apply i))
    measurable_const

theorem measurable_logIntegrand (ρ D γ q t : ℝ) (Q c κ : Fin k ⊕ Fin 2 → ℝ) (B' : ℝ) :
    Measurable (logIntegrand ρ D γ q t Q c κ B') := by
  unfold logIntegrand
  refine ((measurable_const.indicator measurableSet_orthantSet).mul
    (measurable_const.indicator (measurableSet_logCut _ _ _ _ _ _))).mul ?_
  exact ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))

/-- The constant-unit kernel as `A t^{-γp} w₀ ρ^{∑(r+1)}` times the `lintegral` of the log-form
integrand. -/
theorem modelKernel_const_eq_lintegral {ρ A B D γ p q δ : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    {w₀ a₀ t : ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t) :
    modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t =
      A * t ^ (-(γ * p)) * (w₀ * ρ ^ (∑ i, (r i + 1)) *
        (∫⁻ z, logIntegrand ρ D γ q t Q (fun i ↦ r i + 1) κ
          (B * t ^ δ * a₀ * ρ ^ (∑ i, κ i)) z).toReal) := by
  rw [modelKernel_const_eq_log hρ hD hq ht]
  congr 2
  have hmeas : Measurable ((logCut ρ D γ q t Q).indicator
      (fun z : Fin k ⊕ Fin 2 → ℝ ↦ exp (-(∑ i, (r i + 1) * z i)) *
        exp (-(B * t ^ δ * a₀ * ρ ^ (∑ i, κ i) * exp (-(∑ i, κ i * z i)))))) :=
    (Continuous.measurable (by fun_prop)).indicator (measurableSet_logCut _ _ _ _ _ _)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦
      Set.indicator_nonneg (fun z _ ↦ by positivity) z) hmeas.aestronglyMeasurable]
  congr 1
  rw [← orthantSet_eq_pi, ← lintegral_indicator measurableSet_orthantSet]
  refine lintegral_congr fun z ↦ ?_
  unfold logIntegrand
  by_cases hz : z ∈ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i}
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
    by_cases hc : z ∈ logCut ρ D γ q t Q
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc, one_mul]
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc, zero_mul, ENNReal.ofReal_zero]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul, zero_mul]

/-- Steps 2–3 combined: the `lintegral` of the log-form integrand is `|det M|⁻¹ e^{-mL}` times the
transverse integral of the `L`-free weight against the fibre volume. -/
theorem lintegral_logIntegrand_eq {ρ D γ q t δ β η c₀ : ℝ} {Q c κ : Fin k ⊕ Fin 2 → ℝ}
    (hc : ∀ i, c i = β * κ i - η * Q i) (hΔ : (transMat κ Q).det ≠ 0) :
    ∫⁻ z, logIntegrand ρ D γ q t Q c κ (c₀ * exp (δ * log t)) z =
      ENNReal.ofReal |(transMat κ Q).det|⁻¹ *
        ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))) *
        ∫⁻ v, vWeight β η 0 c₀ (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) v *
          volume (fibreSet κ Q δ γ (log t) v) := by
  rw [lintegral_sum_split (measurable_logIntegrand _ _ _ _ _ _ _ _ _)]
  simp_rw [lintegral_inner_subst hc hΔ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_innerKv_swap hΔ, mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun v ↦ ?_
  rw [vWeight_eq_mul β η ((β * δ - η * γ) * log t), mul_assoc]

/-- The limiting polytope: the face projected to the free coordinates. -/
noncomputable def facePolytope (κ Q : Fin k ⊕ Fin 2 → ℝ) (δ γ : ℝ) : Set (Fin k → ℝ) :=
  poly2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1)

theorem volume_facePolytope_ne_top {κ Q : Fin k ⊕ Fin 2 → ℝ} (hΔ : (transMat κ Q).det ≠ 0)
    (hκ : ∀ i, 0 < κ i) (δ γ : ℝ) : volume (facePolytope κ Q δ γ) ≠ ⊤ :=
  ((measure_mono (poly2_mono (le_add_of_nonneg_right zero_le_one)
    (le_add_of_nonneg_right zero_le_one))).trans_lt
    (isBounded_poly2_fibre hΔ hκ δ γ).measure_lt_top).ne

/-- **The transverse active-truth face theorem** (constant units, raw constant). -/
theorem tendsto_modelKernel_activeTruth {ρ A B D γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat κ Q).det ≠ 0) (hc₀ : fibreCoef κ Q 0 ≠ 0) (hc₁ : fibreCoef κ Q 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A * w₀ * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹ *
        (Gamma β * (B * a₀ * ρ ^ (∑ i, κ i)) ^ (-β) *
          (exp (-(η * -(q * log (ρ / D) + (∑ i, Q i) * log ρ))) / η)) *
        (volume (facePolytope κ Q δ γ)).toReal)) := by
  set c₀ := B * a₀ * ρ ^ (∑ i, κ i) with hc₀def
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  have hc : 0 < c₀ := mul_pos (mul_pos hB ha₀) (Real.rpow_pos_of_pos hρ _)
  have hF := volume_facePolytope_ne_top hΔ hκ δ γ
  have hG : 0 ≤ Gamma β * c₀ ^ (-β) * (exp (-(η * h₀)) / η) :=
    (mul_pos (mul_pos (Real.Gamma_pos_of_pos hβ) (Real.rpow_pos_of_pos hc _))
      (div_pos (exp_pos _) hη)).le
  have hI : ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v * volume (facePolytope κ Q δ γ) =
      ENNReal.ofReal (Gamma β * c₀ ^ (-β) * (exp (-(η * h₀)) / η)) *
        volume (facePolytope κ Q δ γ) := by
    rw [lintegral_mul_const _ (measurable_vWeight _ _ _ _ _), lintegral_vWeight_zero hβ hη hc]
  have hlim := (tendsto_lintegral_vWeight_fibre hΔ hκ hc₀ hc₁ hβ hη hc hδ γ h₀).comp
    Real.tendsto_log_atTop
  rw [show poly2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1) =
    facePolytope κ Q δ γ from rfl, hI] at hlim
  have hne : ENNReal.ofReal (Gamma β * c₀ ^ (-β) * (exp (-(η * h₀)) / η)) *
      volume (facePolytope κ Q δ γ) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF
  have hlim2 := ((ENNReal.tendsto_toReal hne).comp hlim).const_mul
    (A * w₀ * ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hG, ← mul_assoc] at hlim2
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
  have hJ : ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v *
      (volume (fibreSet κ Q δ γ (log t) v) / ENNReal.ofReal (log t ^ k)) =
      (∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v * volume (fibreSet κ Q δ γ (log t) v)) /
        ENNReal.ofReal (log t ^ k) := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    exact lintegral_mul_const' _ _
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hL k)).ne')
  rw [hJ]
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

/-- The constant of the face theorem in closed form:
`ρ^{∑(r+1)} c₀^{-β} e^{-ηh₀} = (B a₀)^{-β} (ρ/D)^{qη}` when `r + 1 = βκ − ηQ`. -/
theorem activeTruth_const_eq {ρ B D q β η a₀ : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ)
    (hD : 0 < D) (hB : 0 < B) (ha₀ : 0 < a₀) (hr : ∀ i, r i + 1 = β * κ i - η * Q i) :
    ρ ^ (∑ i, (r i + 1)) * ((B * a₀ * ρ ^ (∑ i, κ i)) ^ (-β) *
      exp (-(η * -(q * log (ρ / D) + (∑ i, Q i) * log ρ)))) =
      (B * a₀) ^ (-β) * (ρ / D) ^ (q * η) := by
  have hsum : ∑ i, (r i + 1) = β * ∑ i, κ i - η * ∑ i, Q i := by
    simp only [hr, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum, Real.mul_rpow (mul_pos hB ha₀).le (Real.rpow_pos_of_pos hρ _).le,
    ← Real.rpow_mul hρ.le]
  have hexp : exp (-(η * -(q * log (ρ / D) + (∑ i, Q i) * log ρ))) =
      (ρ / D) ^ (q * η) * ρ ^ (η * ∑ i, Q i) := by
    rw [Real.rpow_def_of_pos (div_pos hρ hD), Real.rpow_def_of_pos hρ, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hρ1 : ρ ^ (β * ∑ i, κ i - η * ∑ i, Q i) * ρ ^ ((∑ i, κ i) * -β) *
      ρ ^ (η * ∑ i, Q i) = 1 := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_zero ρ]
    congr 1
    ring
  calc ρ ^ (β * ∑ i, κ i - η * ∑ i, Q i) * ((B * a₀) ^ (-β) * ρ ^ ((∑ i, κ i) * -β) *
        ((ρ / D) ^ (q * η) * ρ ^ (η * ∑ i, Q i)))
      = (B * a₀) ^ (-β) * (ρ / D) ^ (q * η) * (ρ ^ (β * ∑ i, κ i - η * ∑ i, Q i) *
          ρ ^ ((∑ i, κ i) * -β) * ρ ^ (η * ∑ i, Q i)) := by ring
    _ = (B * a₀) ^ (-β) * (ρ / D) ^ (q * η) := by rw [hρ1, mul_one]

/-- **The transverse active-truth face theorem** (constant units, closed-form constant):
`t^{γp + βδ − ηγ}/(log t)^k · K(t) → A w₀ Γ(β) (B a₀)^{-β} (ρ/D)^{qη}/η · vol(F')/|det M|`. -/
theorem tendsto_modelKernel_activeTruth' {ρ A B D γ p q δ β η w₀ a₀ : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B)
    (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i)
    (hΔ : (transMat κ Q).det ≠ 0) (hc₀ : fibreCoef κ Q 0 ≠ 0) (hc₁ : fibreCoef κ Q 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t) atTop
      (𝓝 (A * w₀ * Gamma β * (B * a₀) ^ (-β) * (ρ / D) ^ (q * η) / η *
        (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det|)) := by
  have h := tendsto_modelKernel_activeTruth (A := A) (γ := γ) (p := p) (w₀ := w₀) hρ hD hq hB
    ha₀ hβ hη hδ hκ hΔ hc₀ hc₁ hr
  have e := activeTruth_const_eq (q := q) hρ hD hB ha₀ hr
  convert h using 2
  linear_combination (-(A * w₀ * Gamma β * η⁻¹ * (volume (facePolytope κ Q δ γ)).toReal *
    |(transMat κ Q).det|⁻¹)) * e

end Laplace.Multi
