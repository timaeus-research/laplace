/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthTraceLimit

/-!
# The transverse active-truth face theorem for the trace model

Astra round 9, item 1: units depending on the truth coordinate, `W(x, u) = w(u)`,
`a(x, u) = a(u)`, with `w` measurable, `0 ≤ w ≤ W_*` and `a` measurable, `a ≥ a_- > 0` on
`(0, ρ)`. Then
`t^{γp + βδ − ηγ}/(log t)^k · K(t) → A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| ·
∫_0^ρ u^{qη−1} w(u) a(u)^{-β} du` (`tendsto_modelKernel_trace`): the leading measure of an
active-truth chart is Dirac in the active coordinates, with the truth coordinate integrated
against `u^{qη−1} du` inside the constant.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

variable {k : ℕ}

theorem vWeightT_eq_mul (β η mL c₀ h₀ : ℝ) (wh ah : ℝ → ℝ) (v : Fin 2 → ℝ) :
    vWeightT β η mL c₀ h₀ wh ah v = ENNReal.ofReal (exp (-mL)) * vWeightT β η 0 c₀ h₀ wh ah v := by
  unfold vWeightT
  have e : wh (v 1) * exp (-(β * v 0 + η * v 1 + mL)) * exp (-(c₀ * ah (v 1) * exp (-v 0))) =
      exp (-mL) * (wh (v 1) * exp (-(β * v 0 + η * v 1 + 0)) *
        exp (-(c₀ * ah (v 1) * exp (-v 0)))) := by
    rw [show exp (-(β * v 0 + η * v 1 + mL)) = exp (-mL) * exp (-(β * v 0 + η * v 1 + 0)) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  rw [e, ENNReal.ofReal_mul (exp_pos _).le, mul_left_comm]

/-- Steps 2–3 combined for the trace model. -/
theorem lintegral_logIntegrandT_eq {ρ D γ q t δ β η c₀ : ℝ} {Q c κ : Fin k ⊕ Fin 2 → ℝ}
    {w a : ℝ → ℝ} (hwm : Measurable w) (ham : Measurable a) (hq : 0 < q) (ht : 0 < t)
    (hc : ∀ i, c i = β * κ i - η * Q i) (hΔ : (transMat κ Q).det ≠ 0) :
    ∫⁻ z, logIntegrandT ρ D γ q t Q c κ (c₀ * exp (δ * log t)) w a z =
      ENNReal.ofReal |(transMat κ Q).det|⁻¹ *
        ENNReal.ofReal (exp (-((β * δ - η * γ) * log t))) *
        ∫⁻ v, vWeightT β η 0 c₀ (-(q * log (ρ / D) + (∑ i, Q i) * log ρ))
          (fun h ↦ w (truthOf ρ D q Q h)) (fun h ↦ a (truthOf ρ D q Q h)) v *
          volume (fibreSet κ Q δ γ (log t) v) := by
  have hwh : Measurable fun h ↦ w (truthOf ρ D q Q h) :=
    hwm.comp (continuous_truthOf ρ D q Q).measurable
  have hah : Measurable fun h ↦ a (truthOf ρ D q Q h) :=
    ham.comp (continuous_truthOf ρ D q Q).measurable
  rw [lintegral_sum_split (measurable_logIntegrandT _ _ _ _ _ _ _ _ _ hwm ham)]
  simp_rw [lintegral_inner_substT hwm ham hq ht hc hΔ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_innerKvT_swap hΔ _ _ _ _ _ _ _ _
    hwh hah, mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun v ↦ ?_
  rw [vWeightT_eq_mul β η ((β * δ - η * γ) * log t), mul_assoc]

/-- The trace-model integrand is nonnegative when `w ≥ 0` on `(0, ρ)`. -/
theorem modelIntegrand_trace_nonneg {ρ B D γ q δ t : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    {w a : ℝ → ℝ} (hw : ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ w u) (hD : 0 < D) (ht : 0 < t)
    (x : Fin k ⊕ Fin 2 → ℝ) :
    0 ≤ modelIntegrand ρ B D γ q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ a u) t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q Q t
  · rw [Set.indicator_of_mem hx]
    have hx0 : ∀ i, 0 < x i := fun i ↦ ((Set.mem_univ_pi.mp hx.1) i).1
    have hu : cutVar D γ q Q t x ∈ Ioo 0 ρ := by
      refine ⟨?_, hx.2⟩
      unfold cutVar
      exact mul_pos (mul_pos hD (Real.rpow_pos_of_pos ht _))
        (Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hx0 i) _)
    exact mul_nonneg (mul_nonneg (hw _ hu) (Finset.prod_nonneg fun i _ ↦
      Real.rpow_nonneg (hx0 i).le _)) (exp_pos _).le
  · rw [Set.indicator_of_notMem hx]

/-- The `ρ`-powers of the trace constant cancel: `ρ^{∑(r+1)} (Bρ^{∑κ})^{-β} (Dρ^{-∑Q/q})^{-qη} =
B^{-β} D^{-qη}` under the certificate. -/
theorem trace_const_eq {ρ B D q β η : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ)
    (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hr : ∀ i, r i + 1 = β * κ i - η * Q i) :
    ρ ^ (∑ i, (r i + 1)) * ((B * ρ ^ (∑ i, κ i)) ^ (-β) *
      (D * ρ ^ (-(∑ i, Q i) / q)) ^ (-(q * η))) = B ^ (-β) * D ^ (-(q * η)) := by
  have hsum : ∑ i, (r i + 1) = β * ∑ i, κ i - η * ∑ i, Q i := by
    simp only [hr, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum, Real.mul_rpow hB.le (Real.rpow_pos_of_pos hρ _).le,
    Real.mul_rpow hD.le (Real.rpow_pos_of_pos hρ _).le, ← Real.rpow_mul hρ.le,
    ← Real.rpow_mul hρ.le]
  have hρ1 : ρ ^ (β * ∑ i, κ i - η * ∑ i, Q i) * ρ ^ ((∑ i, κ i) * -β) *
      ρ ^ (-(∑ i, Q i) / q * -(q * η)) = 1 := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_zero ρ]
    congr 1
    field_simp
    ring
  calc ρ ^ (β * ∑ i, κ i - η * ∑ i, Q i) * (B ^ (-β) * ρ ^ ((∑ i, κ i) * -β) *
        (D ^ (-(q * η)) * ρ ^ (-(∑ i, Q i) / q * -(q * η))))
      = B ^ (-β) * D ^ (-(q * η)) * (ρ ^ (β * ∑ i, κ i - η * ∑ i, Q i) *
          ρ ^ ((∑ i, κ i) * -β) * ρ ^ (-(∑ i, Q i) / q * -(q * η))) := by ring
    _ = B ^ (-β) * D ^ (-(q * η)) := by rw [hρ1, mul_one]

/-- **The transverse active-truth face theorem for the trace model** (nonnegative `w`). -/
theorem tendsto_modelKernel_trace {ρ A B D γ p q δ β η : ℝ} {Q κ r : Fin k ⊕ Fin 2 → ℝ}
    (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) {w a : ℝ → ℝ} {Wstar amin : ℝ} (hamin : 0 < amin)
    (hwm : Measurable w) (ham : Measurable a) (hw : ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ w u ∧ w u ≤ Wstar)
    (ha : ∀ u ∈ Ioo (0 : ℝ) ρ, amin ≤ a u) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ a u) t) atTop
      (𝓝 (A * Gamma β * B ^ (-β) * q * D ^ (-(q * η)) *
        (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| *
        ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (w u * a u ^ (-β)))) := by
  set c₀ := B * ρ ^ (∑ i, κ i) with hc₀def
  set h₀ := -(q * log (ρ / D) + (∑ i, Q i) * log ρ) with hh₀
  set wh : ℝ → ℝ := fun h ↦ w (truthOf ρ D q Q h) with hwhdef
  set ah : ℝ → ℝ := fun h ↦ a (truthOf ρ D q Q h) with hahdef
  have hc : 0 < c₀ := mul_pos hB (Real.rpow_pos_of_pos hρ _)
  have hwh : Measurable wh := hwm.comp (continuous_truthOf ρ D q Q).measurable
  have hah : Measurable ah := ham.comp (continuous_truthOf ρ D q Q).measurable
  have hwb : ∀ h, h₀ < h → 0 ≤ wh h ∧ wh h ≤ Wstar := fun h hh ↦
    hw _ (truthOf_mem_Ioo hρ hD hq Q hh)
  have hab : ∀ h, h₀ < h → amin ≤ ah h := fun h hh ↦ ha _ (truthOf_mem_Ioo hρ hD hq Q hh)
  have hF := volume_facePolytope_ne_top hΔ hκ δ γ
  -- the transverse limit
  have hlim := (tendsto_lintegral_vWeightT_fibre hΔ hκ hc₀ hc₁ hβ hη hc hδ h₀ hamin hwh hah hwb
    hab).comp Real.tendsto_log_atTop
  rw [show poly2 (fibreCoef κ Q 0) (fibreCoef κ Q 1) (fibreA κ Q δ γ 0) (fibreA κ Q δ γ 1) =
    facePolytope κ Q δ γ from rfl, lintegral_mul_const _ (measurable_vWeightT _ _ _ _ _ hwh hah),
    lintegral_vWeightT_zero hβ hη hc hamin hwh hah hwb hab] at hlim
  -- the `h`-integral in the `u`-form
  have hint : ∫ h in Ioi h₀, Gamma β * (c₀ * ah h) ^ (-β) * (exp (-(η * h)) * wh h) =
      Gamma β * c₀ ^ (-β) * (q * (D * ρ ^ (-(∑ i, Q i) / q)) ^ (-(q * η)) *
        ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (w u * a u ^ (-β))) := by
    rw [← integral_Ioi_truthOf hρ hD hq Q (fun u ↦ w u * a u ^ (-β)), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun h hh ↦ ?_
    have hu := truthOf_mem_Ioo hρ hD hq Q hh
    have ha0 : 0 ≤ a (truthOf ρ D q Q h) := hamin.le.trans (ha _ hu)
    simp only [hwhdef, hahdef]
    rw [Real.mul_rpow hc.le ha0]
    ring
  rw [hint] at hlim
  set I := ∫ u in Ioo (0 : ℝ) ρ, u ^ (q * η - 1) * (w u * a u ^ (-β)) with hI
  have hI0 : 0 ≤ I := by
    rw [hI]
    refine setIntegral_nonneg measurableSet_Ioo fun u hu ↦ ?_
    exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (mul_nonneg (hw u hu).1 (Real.rpow_nonneg
      (hamin.le.trans (ha u hu)) _))
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
  -- the constant
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
  -- the kernel as a `lintegral`
  have hK : modelKernel ρ A B D γ p q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ a u) t =
      A * t ^ (-(γ * p)) * (∫⁻ x, ENNReal.ofReal
        (modelIntegrand ρ B D γ q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ a u) t x)).toReal := by
    unfold modelKernel
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (modelIntegrand_trace_nonneg (fun u hu ↦ (hw u hu).1) hD ht0))
      (measurable_modelIntegrand
        (show Measurable (Function.uncurry fun (_ : Fin k ⊕ Fin 2 → ℝ) (u : ℝ) ↦ w u) from
          hwm.comp measurable_snd)
        (show Measurable (Function.uncurry fun (_ : Fin k ⊕ Fin 2 → ℝ) (u : ℝ) ↦ a u) from
          ham.comp measurable_snd) t).aestronglyMeasurable]
  rw [hK, lintegral_modelIntegrand_trace w a hρ hD hq ht0]
  have hB' : B * t ^ δ * ρ ^ (∑ i, κ i) = c₀ * exp (δ * log t) := by
    rw [hc₀def, Real.rpow_def_of_pos ht0, mul_comm (log t) δ]
    ring
  rw [hB', lintegral_logIntegrandT_eq hwm ham hq ht0 (fun i ↦ hr i) hΔ, ← hh₀, ← hwhdef, ← hahdef]
  have hJ : ∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 c₀ h₀ wh ah v *
      (volume (fibreSet κ Q δ γ (log t) v) / ENNReal.ofReal (log t ^ k)) =
      (∫⁻ v : Fin 2 → ℝ, vWeightT β η 0 c₀ h₀ wh ah v * volume (fibreSet κ Q δ γ (log t) v)) /
        ENNReal.ofReal (log t ^ k) := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
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
