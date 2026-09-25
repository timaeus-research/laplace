/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthGeneral

/-!
# The general-unit face theorem in Lebesgue-integral form, with a uniform bound

The analogue of `ActiveTruthUniform` for general units `W(x, u)`, `a(x, u)`: the normalised
`lintegral` of the model integrand in transverse form (`normalised_lintegral_eqG`), its limit in
`ℝ≥0∞` (`tendsto_normalised_lintegralG`), and the bound uniform for `t ≥ e`
(`lintegral_innerKvG_div_le`, `normalised_lintegral_leG`): `W_*` times the constant-unit bound at
the Boltzmann constant `c₀ a_-`. This is what the outer dominated convergence in the spectators
needs for general units.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

/-- The normalised general-unit model integral in the transverse form. -/
theorem normalised_lintegral_eqG {ρ B D γ q δ β η t : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} (hWm : Measurable (Function.uncurry W))
    (ham : Measurable (Function.uncurry a)) (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q)
    (hΔ : (transMat κ Q).det ≠ 0) (hr : ∀ i, r i + 1 = β * κ i - η * Q i) (ht : 1 < t) :
    ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x) =
      ENNReal.ofReal (ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹) *
        ∫⁻ v : Fin 2 → ℝ, (∫⁻ z' : Fin k → ℝ, innerKvG ρ D q κ Q δ γ (log t) β η 0
          (B * ρ ^ (∑ i, κ i)) (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) W a z' v) /
          ENNReal.ofReal (log t ^ k) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hL : 0 < log t := Real.log_pos ht
  set c₀ := B * ρ ^ (∑ i, κ i) with hc₀def
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  have hB' : B * t ^ δ * ρ ^ (∑ i, κ i) = c₀ * exp (δ * log t) := by
    rw [hc₀def, Real.rpow_def_of_pos ht0, mul_comm (log t) δ]
    ring
  rw [lintegral_modelIntegrand_general W a hρ hD hq ht0, hB',
    lintegral_sum_split (measurable_logIntegrandG _ _ _ _ _ _ _ _ _ hWm ham)]
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
  set J := ∫⁻ v : Fin 2 → ℝ, ∫⁻ z' : Fin k → ℝ,
    innerKvG ρ D q κ Q δ γ (log t) β η 0 c₀ h₀ W a z' v
  have hkey : ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
      ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))) = (ENNReal.ofReal (log t ^ k))⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_inv_of_pos (pow_pos hL k)]
    congr 1
    rw [Real.rpow_def_of_pos ht0, mul_comm (log t), Real.exp_neg]
    field_simp
  calc ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        (ENNReal.ofReal (ρ ^ (∑ i, (r i + 1))) *
          (ENNReal.ofReal |(transMat κ Q).det|⁻¹ *
            (ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))) * J)))
      = (ENNReal.ofReal (ρ ^ (∑ i, (r i + 1))) * ENNReal.ofReal |(transMat κ Q).det|⁻¹) *
          (J * (ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
            ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))))) := by ring
    _ = _ := by
      rw [hkey, ← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _), div_eq_mul_inv]

/-- The transverse limit of the normalised general-unit integral (in `ℝ≥0∞`). -/
theorem tendsto_normalised_lintegralG {ρ B D γ q δ β η : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    {Wstar amin : ℝ} (hamin : 0 < amin) (hWm : Measurable (Function.uncurry W))
    (ham : Measurable (Function.uncurry a)) (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar)
    (hab : ∀ x u, amin ≤ a x u) {Wtr atr : ℝ → ℝ}
    (hWtr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ W x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (Wtr u)))
    (hatr : ∀ u ∈ Ioo (0 : ℝ) ρ, Tendsto (fun x ↦ a x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) ρ] 0) (𝓝 (atr u))) :
    Tendsto (fun t ↦ ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x)) atTop
      (𝓝 (ENNReal.ofReal (ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹) *
        ∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 (B * ρ ^ (∑ i, κ i))
          (-(q * log (ρ / D) + (∑ i, Q i) * log ρ)) (fun h ↦ Wtr (truthOf ρ D q Q h))
          (fun h ↦ atr (truthOf ρ D q Q h)) v * volume (facePolytope κ Q δ γ))) := by
  have hc : 0 < B * ρ ^ (∑ i, κ i) := mul_pos hB (Real.rpow_pos_of_pos hρ _)
  have hlim := (tendsto_lintegral_innerKvG hρ hD hq hΔ hκ hc₀ hc₁ hβ hη hc hδ hamin hWm ham hWb
    hab hWtr hatr).comp Real.tendsto_log_atTop
  refine (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [normalised_lintegral_eqG hWm ham hρ hD hq hΔ hr ht]
  rfl

/-- The pointwise bound on the transverse integrand of the general model, for `L ≥ 1`. -/
theorem lintegral_innerKvG_div_le {ρ D q c₀ : ℝ} {κ Q : Fin k ⊕ Fin 2 → ℝ}
    (hΔ : (transMat κ Q).det ≠ 0) (hκ : ∀ i, 0 < κ i) {β η δ γ : ℝ} (hc : 0 < c₀) (hδ : 0 ≤ δ)
    (h₀ : ℝ) {Wstar amin : ℝ} {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ}
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) {L : ℝ} (hL : 1 ≤ L)
    (v : Fin 2 → ℝ) :
    (∫⁻ z' : Fin k → ℝ, innerKvG ρ D q κ Q δ γ L β η 0 c₀ h₀ W a z' v) / ENNReal.ofReal (L ^ k) ≤
      ENNReal.ofReal Wstar * (vWeight β η 0 (c₀ * amin) h₀ v *
        ENNReal.ofReal ((|v 0| + δ) ^ k / ∏ i, κ (Sum.inl i))) := by
  have hW : 0 ≤ Wstar := (hWb 0 0).1.trans (hWb 0 0).2
  rw [lintegral_innerKvG_eq hΔ]
  have hbd : ∫⁻ z' in fibreSet κ Q δ γ L v, ENNReal.ofReal (ampG ρ D q c₀ Q W a v
      (negExpMap ρ (fibreLift κ Q δ γ L v z'))) ≤
      ENNReal.ofReal (Wstar * exp (-(c₀ * amin * exp (-v 0)))) * volume (fibreSet κ Q δ γ L v) := by
    rw [← setLIntegral_const]
    exact lintegral_mono fun z' ↦ ENNReal.ofReal_le_ofReal (ampG_nonneg_le hc hWb hab v _).2
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

/-- **The uniform bound for general units**: for `t ≥ e`, the normalised model integral is at most
`W_*` times the constant-unit bound at the Boltzmann constant `c₀ a_-`. -/
theorem normalised_lintegral_leG {ρ B D γ q δ β η t : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0) (hr : ∀ i, r i + 1 = β * κ i - η * Q i)
    {W a : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ} {Wstar amin : ℝ} (hamin : 0 < amin)
    (hWm : Measurable (Function.uncurry W)) (ham : Measurable (Function.uncurry a))
    (hWb : ∀ x u, 0 ≤ W x u ∧ W x u ≤ Wstar) (hab : ∀ x u, amin ≤ a x u) (ht : exp 1 ≤ t) :
    ENNReal.ofReal (t ^ (β * δ - η * γ) / log t ^ k) *
        ∫⁻ x, ENNReal.ofReal (modelIntegrand ρ B D γ q δ Q κ r W a t x) ≤
      ENNReal.ofReal (ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹ * (Wstar *
        ((∫ s, sWeight β (B * ρ ^ (∑ i, κ i) * amin) s * (|s| + δ) ^ k) / (∏ i, κ (Sum.inl i)) *
          (exp (-(η * -(q * log (ρ / D) + (∑ i, Q i) * log ρ))) / η)))) := by
  have ht1 : 1 < t := lt_of_lt_of_le (by linarith [Real.add_one_le_exp 1]) ht
  have hL : 1 ≤ log t := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (exp_pos 1) ht
  have hc : 0 < B * ρ ^ (∑ i, κ i) := mul_pos hB (Real.rpow_pos_of_pos hρ _)
  have hca : 0 < B * ρ ^ (∑ i, κ i) * amin := mul_pos hc hamin
  have hP : 0 < ∏ i, κ (Sum.inl i) := Finset.prod_pos fun i _ ↦ hκ _
  have hW : 0 ≤ Wstar := (hWb 0 0).1.trans (hWb 0 0).2
  rw [normalised_lintegral_eqG hWm ham hρ hD hq hΔ hr ht1,
    ENNReal.ofReal_mul (p := ρ ^ (∑ i, (r i + 1)) * |(transMat κ Q).det|⁻¹) (by positivity),
    ENNReal.ofReal_mul hW]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  refine (lintegral_mono fun v ↦ lintegral_innerKvG_div_le hΔ hκ hc hδ _ hWb hab hL v).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_vWeight_mul_pow hβ hη hca hδ hP]

end Laplace.Multi
