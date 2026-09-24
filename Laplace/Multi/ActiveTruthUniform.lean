/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthTheorem

/-!
# The face theorem in Lebesgue-integral form, with a uniform bound

Preparation for spectator coordinates (Astra round 8, item 2): the constant-unit face theorem is
restated for the `lintegral` of the model integrand (`lintegral_modelIntegrand_const`,
`normalised_lintegral_eq`, `tendsto_normalised_lintegral`), and the normalised integral is bounded
uniformly for `t ≥ e` by an explicit function of the Boltzmann constant `c₀` and the truth cut
`h₀` (`normalised_lintegral_le`, `integral_sWeight_mul_pow_le`:
`∫ e^{-βs} e^{-c e^{-s}} (|s|+δ)^k ≤ c^{-β} (1 + δ + |log c|)^k C_k`), which is what the outer
dominated convergence in the spectators needs.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-! ### The logarithmic substitution in `lintegral` form -/

theorem lintegral_box_eq_orthant {ρ : ℝ} (hρ : 0 < ρ) (F : (Fin k ⊕ Fin 2 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in Set.pi univ (fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ), F x =
      ∫⁻ z in Set.pi univ (fun _ : Fin k ⊕ Fin 2 ↦ Ioi (0 : ℝ)),
        ENNReal.ofReal (∏ i, ρ * exp (-z i)) * F (negExpMap ρ z) := by
  rw [← image_negExpMap_orthant hρ, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    (fun z _ ↦ (hasFDerivAt_negExpMap ρ z).hasFDerivWithinAt) (negExpMap_injective hρ).injOn F]
  refine setLIntegral_congr_fun (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    fun z _ ↦ ?_
  rw [abs_det_negExpDeriv hρ]

/-- The `lintegral` of the unit-weight model integrand is `ρ^{∑(r+1)}` times the `lintegral` of
the log-form integrand. -/
theorem lintegral_modelIntegrand_const {ρ B D γ q δ : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ} {a₀ t : ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (ht : 0 < t) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x) =
      ENNReal.ofReal (ρ ^ (∑ i, (r i + 1))) *
        ∫⁻ z, logIntegrand ρ D γ q t Q (fun i ↦ r i + 1) κ (B * t ^ δ * a₀ * ρ ^ (∑ i, κ i)) z := by
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hsupp : (fun x ↦ ENNReal.ofReal
      (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x)) =
      (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ).indicator fun x ↦ ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x) := by
    funext x
    by_cases hx : x ∈ Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      unfold modelIntegrand
      rw [Set.indicator_of_notMem (fun h' ↦ hx h'.1), ENNReal.ofReal_zero]
  rw [hsupp, lintegral_indicator hbox, lintegral_box_eq_orthant hρ]
  have horth : (fun z ↦ logIntegrand ρ D γ q t Q (fun i ↦ r i + 1) κ
      (B * t ^ δ * a₀ * ρ ^ (∑ i, κ i)) z) =
      (Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioi (0 : ℝ)).indicator fun z ↦
        logIntegrand ρ D γ q t Q (fun i ↦ r i + 1) κ (B * t ^ δ * a₀ * ρ ^ (∑ i, κ i)) z := by
    funext z
    by_cases hz : z ∈ Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      unfold logIntegrand
      rw [← orthantSet_eq_pi] at hz
      rw [Set.indicator_of_notMem hz, zero_mul, zero_mul]
  rw [horth, lintegral_indicator (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    fun z hz ↦ ?_
  have hz' : ∀ i, 0 < z i := fun i ↦ (Set.mem_univ_pi.mp hz) i
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ ↦ by positivity),
    modelIntegrand_const_negExp hρ hD hq ht hz']
  unfold logIntegrand
  rw [Set.indicator_of_mem (show z ∈ {z : Fin k ⊕ Fin 2 → ℝ | ∀ i, 0 < z i} from hz'), one_mul]
  by_cases hcut : z ∈ logCut ρ D γ q t Q
  · rw [Set.indicator_of_mem hcut, Set.indicator_of_mem hcut, one_mul, one_mul,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
    congr 1
    ring
  · rw [Set.indicator_of_notMem hcut, Set.indicator_of_notMem hcut]
    simp

/-! ### The normalised integral -/

/-- The normalised model integral in the transverse form. -/
theorem normalised_lintegral_eq {ρ B D γ q δ β η a₀ t : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hΔ : (transMat κ Q).det ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) (ht : 1 < t) :
    ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        ∫⁻ x, ENNReal.ofReal
          (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x) =
      ENNReal.ofReal (ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹) *
        ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 (B * a₀ * ρ ^ (∑ i, κ i))
          (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) v *
          (volume (fibreSet κ Q δ γ (log t) v) / ENNReal.ofReal (log t ^ k)) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hL : 0 < log t := Real.log_pos ht
  set c₀ := B * a₀ * ρ ^ (∑ i, κ i) with hc₀def
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  have hB' : B * t ^ δ * a₀ * ρ ^ (∑ i, κ i) = c₀ * exp (δ * log t) := by
    rw [hc₀def, Real.rpow_def_of_pos ht0, mul_comm (log t) δ]
    ring
  rw [lintegral_modelIntegrand_const hρ hD hq ht0, hB', lintegral_logIntegrand_eq (fun i ↦ hr i) hΔ,
    ← hh₀]
  have hJ : ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v *
      (volume (fibreSet κ Q δ γ (log t) v) / ENNReal.ofReal (log t ^ k)) =
      (∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v * volume (fibreSet κ Q δ γ (log t) v)) *
        (ENNReal.ofReal (log t ^ k))⁻¹ := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    exact lintegral_mul_const' _ _
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hL k)).ne')
  rw [hJ]
  set J := ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v * volume (fibreSet κ Q δ γ (log t) v)
  have hkey : ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
      ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))) = (ENNReal.ofReal (log t ^ k))⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_inv_of_pos (pow_pos hL k)]
    congr 1
    rw [Real.rpow_def_of_pos ht0, mul_comm (log t), Real.exp_neg]
    field_simp
  calc ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        (ENNReal.ofReal (ρ ^ (∑ i, (r i + 1))) *
          (ENNReal.ofReal |(transMat κ Q).det|⁻¹ *
            ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))) * J))
      = (ENNReal.ofReal (ρ ^ (∑ i, (r i + 1))) * ENNReal.ofReal |(transMat κ Q).det|⁻¹) *
          (J * (ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
            ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))))) := by ring
    _ = _ := by
      rw [hkey, ← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]

/-- The transverse limit for the normalised model integral (in `ℝ≥0∞`). -/
theorem tendsto_normalised_lintegral {ρ B D γ q δ β η a₀ : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η)
    (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) :
    Tendsto (fun t ↦ ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        ∫⁻ x, ENNReal.ofReal
          (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x)) atTop
      (𝓝 (ENNReal.ofReal (ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹) *
        (ENNReal.ofReal (Gamma β * (B * a₀ * ρ ^ (∑ i, κ i)) ^ (-β) *
          (exp (-(η * -(q * log (ρ / D) + (∑ i, Q i) * log ρ))) / η)) *
          volume (facePolytope κ Q δ γ)))) := by
  have hc : 0 < B * a₀ * ρ ^ (∑ i, κ i) := mul_pos (mul_pos hB ha₀) (Real.rpow_pos_of_pos hρ _)
  have hlim := (tendsto_lintegral_vWeight_fibre hΔ hκ hc₀ hc₁ hβ hη hc hδ
    (-(q * log (ρ / D) + (∑ i, Q i) * log ρ))).comp Real.tendsto_log_atTop
  rw [show poly2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1) =
    facePolytope κ Q δ γ from rfl, lintegral_mul_const _ (measurable_vWeight _ _ _ _ _),
    lintegral_vWeight_zero hβ hη hc] at hlim
  refine (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [normalised_lintegral_eq hρ hD hq hΔ hr ht]
  rfl

/-! ### The uniform bound -/

theorem sWeight_add_log {β c : ℝ} (hc : 0 < c) (s : ℝ) :
    sWeight β c (s + log c) = c ^ (-β) * sWeight β 1 s := by
  simp only [sWeight, one_mul]
  have e1 : exp (-(β * (s + log c))) = c ^ (-β) * exp (-(β * s)) := by
    rw [Real.rpow_def_of_pos hc, ← Real.exp_add]
    congr 1
    ring
  have e2 : c * exp (-(s + log c)) = exp (-s) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (log c), Real.exp_log hc]
    field_simp
  rw [e1, e2]
  ring

/-- `∫ e^{-βs} e^{-c e^{-s}} (|s|+δ)^k ≤ c^{-β} (1 + δ + |log c|)^k · C_k` with
`C_k = ∫ e^{-βs} e^{-e^{-s}} (|s|+1)^k`. -/
theorem integral_sWeight_mul_pow_le {β c δ : ℝ} (hβ : 0 < β) (hc : 0 < c) (hδ : 0 ≤ δ) (k : ℕ) :
    ∫ s, sWeight β c s * (|s| + δ) ^ k ≤
      c ^ (-β) * (1 + δ + |log c|) ^ k * ∫ s, sWeight β 1 s * (|s| + 1) ^ k := by
  rw [← integral_add_right_eq_self (fun s ↦ sWeight β c s * (|s| + δ) ^ k) (log c)]
  simp only [sWeight_add_log hc]
  rw [← integral_const_mul]
  have hM : 0 ≤ 1 + δ + |log c| := by positivity
  have hpt : ∀ s, c ^ (-β) * sWeight β 1 s * (|s + log c| + δ) ^ k ≤
      c ^ (-β) * (1 + δ + |log c|) ^ k * (sWeight β 1 s * (|s| + 1) ^ k) := by
    intro s
    have h1 : |s + log c| + δ ≤ (|s| + 1) * (1 + δ + |log c|) := by
      have := abs_add_le s (log c)
      nlinarith [abs_nonneg s, abs_nonneg (log c)]
    have h2 : (|s + log c| + δ) ^ k ≤ (|s| + 1) ^ k * (1 + δ + |log c|) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 k
    have hw := sWeight_nonneg β 1 s
    have hcβ : 0 ≤ c ^ (-β) := (Real.rpow_pos_of_pos hc _).le
    calc c ^ (-β) * sWeight β 1 s * (|s + log c| + δ) ^ k
        ≤ c ^ (-β) * sWeight β 1 s * ((|s| + 1) ^ k * (1 + δ + |log c|) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hcβ hw)
      _ = c ^ (-β) * (1 + δ + |log c|) ^ k * (sWeight β 1 s * (|s| + 1) ^ k) := by ring
  have hint : Integrable fun s ↦ c ^ (-β) * (1 + δ + |log c|) ^ k *
      (sWeight β 1 s * (|s| + 1) ^ k) :=
    (integrable_sWeight_mul_pow hβ one_pos zero_le_one k).const_mul _
  refine integral_mono ?_ hint hpt
  refine hint.mono' ?_ (Eventually.of_forall fun s ↦ ?_)
  · exact (((continuous_sWeight β 1).const_mul _).mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hc _).le
      (sWeight_nonneg _ _ _)) (by positivity))]
    exact hpt s

/-- The transverse integral of the dominating weight, evaluated. -/
theorem lintegral_vWeight_mul_pow {β η c₀ δ P : ℝ} (hβ : 0 < β) (hη : 0 < η) (hc : 0 < c₀)
    (hδ : 0 ≤ δ) (hP : 0 < P) (h₀ : ℝ) (k : ℕ) :
    ∫⁻ v : Fin 2 → ℝ, vWeight β η 0 c₀ h₀ v * ENNReal.ofReal ((|v 0| + δ) ^ k / P) =
      ENNReal.ofReal ((∫ s, sWeight β c₀ s * (|s| + δ) ^ k) / P * (exp (-(η * h₀)) / η)) := by
  have e : (fun v : Fin 2 → ℝ ↦ vWeight β η 0 c₀ h₀ v * ENNReal.ofReal ((|v 0| + δ) ^ k / P)) =
      fun v ↦ ENNReal.ofReal ((sWeight β c₀ (v 0) * (|v 0| + δ) ^ k / P) * hWeight η h₀ (v 1)) := by
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
      (hWeight_nonneg _ _ _)),
    integral_fin_two_mul (fun s ↦ sWeight β c₀ s * (|s| + δ) ^ k / P) (hWeight η h₀),
    integral_div, integral_hWeight hη]

/-- **The uniform bound**: for `t ≥ e`, the normalised model integral is at most
`ρ^{∑(r+1)}/|det M| · (∫ e^{-βs} e^{-c₀ e^{-s}} (|s|+δ)^k)/∏κ' · e^{-ηh₀}/η`. -/
theorem normalised_lintegral_le {ρ B D γ q δ β η a₀ t : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (ha₀ : 0 < a₀) (hβ : 0 < β) (hη : 0 < η)
    (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) (ht : exp 1 ≤ t) :
    ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        ∫⁻ x, ENNReal.ofReal
          (modelIntegrand ρ B D γ q δ Q κ r (fun _ _ ↦ 1) (fun _ _ ↦ a₀) t x) ≤
      ENNReal.ofReal (ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹ *
        ((∫ s, sWeight β (B * a₀ * ρ ^ (∑ i, κ i)) s * (|s| + δ) ^ k) / (∏ i, κ (Sum.inl i)) *
          (exp (-(η * -(q * log (ρ / D) + (∑ i, Q i) * log ρ))) / η))) := by
  have ht1 : 1 < t := lt_of_lt_of_le (by linarith [Real.add_one_le_exp 1]) ht
  have hL : 1 ≤ log t := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (exp_pos 1) ht
  have hc : 0 < B * a₀ * ρ ^ (∑ i, κ i) := mul_pos (mul_pos hB ha₀) (Real.rpow_pos_of_pos hρ _)
  have hP : 0 < ∏ i, κ (Sum.inl i) := Finset.prod_pos fun i _ ↦ hκ _
  rw [normalised_lintegral_eq hρ hD hq hΔ hr ht1,
    ENNReal.ofReal_mul (p := ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹) (by positivity)]
  refine (mul_le_mul_of_nonneg_left (lintegral_mono fun v ↦
    mul_le_mul_of_nonneg_left (volume_fibreSet_div_le hΔ hκ hδ γ hL v) zero_le) zero_le).trans ?_
  rw [lintegral_vWeight_mul_pow hβ hη hc hδ hP]

end Laplace.Multi
