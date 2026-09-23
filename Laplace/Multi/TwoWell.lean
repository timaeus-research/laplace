/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RescaledData
import Laplace.Multi.ChartAssembly

/-!
# Two wells with an energy offset: the analytic theorem

Along a schedule of truths `p t`, the loss `F(·, p t)` has the tracked well at `0` (`F(0,s) = 0`)
and a second well at `x₁(p t)` of depth `f₁(p t) = F(x₁(p t), p t)`, with `t f₁(p t) → z`. The
prior splits as `χ = ψ₀ + ψ₁ + ρ`, with `ψ_j` localising the wells and `ρ` supported where
`F ≥ g > 0` (the gap). Each well is an instance of the dominated rescaling lemma at the Gaussian
scale `x = t^{-1/2}u` (`TwoWellData.well₀`, `TwoWellData.well₁`, the second with the moving centre
and the offset removed). Then the energy statistic converges to the Boltzmann-weighted mixture of
the two well energies, the lifted well carrying the extra energy `z` and the mass factor `e^{-z}`
(`TwoWellData.tendsto_energy`). For two wells of the same type and mass this is the hump
`1/2 + z/(1+e^z)` of `WellCompetition.lean` (`TwoWellData.tendsto_energy_hump`). This is Astra's
Test A of germbij_slop S13 and item D of S14: the first competition theorem, built from
`RescaledData` and `ChartAssembly` plus the gap estimate.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

/-- `y e^{-y} ≤ 2 e^{-y/2}`. -/
theorem mul_exp_neg_le_two_mul_exp_neg_half (y : ℝ) :
    y * Real.exp (-y) ≤ 2 * Real.exp (-(y / 2)) := by
  have h := mul_exp_neg_le_one (y / 2)
  have e : Real.exp (-y) = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(y / 2))).le
  nlinarith [Real.exp_pos (-(y / 2))]

/-- Standing hypotheses of the two-well theorem. -/
structure TwoWellData (F : ℝ → ℝ → ℝ) (p x₁ f₁ : ℝ → ℝ) (χ ψ₀ ψ₁ ρ : ℝ → ℝ)
    (Φ₀ Φ₁ w₀ w₁ W₀ W₁ : ℝ → ℝ) (c₀ c₁ z g : ℝ) : Prop where
  F_cont : Continuous (Function.uncurry F)
  F_nonneg : ∀ x s, 0 ≤ F x s
  f₁_def : ∀ s, f₁ s = F (x₁ s) s
  hz : Tendsto (fun t ↦ t * f₁ (p t)) atTop (𝓝 z)
  partition : ∀ x, χ x = ψ₀ x + ψ₁ x + ρ x
  ψ₀_int : Integrable ψ₀
  ψ₁_int : Integrable ψ₁
  ρ_int : Integrable ρ
  hg : 0 < g
  gap : ∀ᶠ t in atTop, ∀ x, ρ x ≠ 0 → g ≤ F x (p t)
  well₀ : RescaledData volume (fun t u ↦ t * F (t ^ (-(1 / 2 : ℝ)) * u) (p t))
    (fun t u ↦ ψ₀ (t ^ (-(1 / 2 : ℝ)) * u)) Φ₀ w₀ W₀ c₀
  well₁ : RescaledData volume
    (fun t u ↦ t * (F (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) (p t) - f₁ (p t)))
    (fun t u ↦ ψ₁ (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u)) Φ₁ w₁ W₁ c₁
  Z₀_pos : 0 < ∫ u, w₀ u * Real.exp (-Φ₀ u)
  Z₁_pos : 0 < ∫ u, w₁ u * Real.exp (-Φ₁ u)

namespace TwoWellData

variable {F : ℝ → ℝ → ℝ} {p x₁ f₁ χ ψ₀ ψ₁ ρ Φ₀ Φ₁ w₀ w₁ W₀ W₁ : ℝ → ℝ} {c₀ c₁ z g : ℝ}

/-- Limits of the well data. -/
noncomputable def C₀ (_hd : TwoWellData F p x₁ f₁ χ ψ₀ ψ₁ ρ Φ₀ Φ₁ w₀ w₁ W₀ W₁ c₀ c₁ z g) : ℝ :=
  ∫ u, w₀ u * Real.exp (-Φ₀ u)
noncomputable def C₁ (_hd : TwoWellData F p x₁ f₁ χ ψ₀ ψ₁ ρ Φ₀ Φ₁ w₀ w₁ W₀ W₁ c₀ c₁ z g) : ℝ :=
  ∫ u, w₁ u * Real.exp (-Φ₁ u)
noncomputable def J₀ (_hd : TwoWellData F p x₁ f₁ χ ψ₀ ψ₁ ρ Φ₀ Φ₁ w₀ w₁ W₀ W₁ c₀ c₁ z g) : ℝ :=
  ∫ u, w₀ u * (Φ₀ u * Real.exp (-Φ₀ u))
noncomputable def J₁ (_hd : TwoWellData F p x₁ f₁ χ ψ₀ ψ₁ ρ Φ₀ Φ₁ w₀ w₁ W₀ W₁ c₀ c₁ z g) : ℝ :=
  ∫ u, w₁ u * (Φ₁ u * Real.exp (-Φ₁ u))

section

variable (hd : TwoWellData F p x₁ f₁ χ ψ₀ ψ₁ ρ Φ₀ Φ₁ w₀ w₁ W₀ W₁ c₀ c₁ z g)
include hd

omit hd in
/-- The Gaussian substitution `x = t^{-1/2} u` for the tracked well. -/
theorem well₀_subst {t : ℝ} (ht : 0 < t) (Ψ : ℝ → ℝ) :
    (∫ x, ψ₀ x * Ψ (t * F x (p t))) / t ^ (-(1 / 2 : ℝ)) =
      ∫ u, ψ₀ (t ^ (-(1 / 2 : ℝ)) * u) * Ψ (t * F (t ^ (-(1 / 2 : ℝ)) * u) (p t)) := by
  have hc : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have h := Measure.integral_comp_mul_left (fun x ↦ ψ₀ x * Ψ (t * F x (p t))) (t ^ (-(1 / 2 : ℝ)))
  rw [abs_inv, abs_of_pos hc, smul_eq_mul] at h
  rw [div_eq_inv_mul, ← h]

omit hd in
/-- The substitution `x = x₁(p t) + t^{-1/2} u` for the moving well. -/
theorem well₁_subst {t : ℝ} (ht : 0 < t) (Ψ : ℝ → ℝ) :
    (∫ x, ψ₁ x * Ψ (t * F x (p t))) / t ^ (-(1 / 2 : ℝ)) =
      ∫ u, ψ₁ (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) *
        Ψ (t * F (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) (p t)) := by
  have hc : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have h := Measure.integral_comp_mul_left (fun y ↦ ψ₁ (x₁ (p t) + y) *
    Ψ (t * F (x₁ (p t) + y) (p t))) (t ^ (-(1 / 2 : ℝ)))
  rw [abs_inv, abs_of_pos hc, smul_eq_mul,
    integral_add_left_eq_self (fun x ↦ ψ₁ x * Ψ (t * F x (p t))) (x₁ (p t))] at h
  rw [div_eq_inv_mul, ← h]

omit hd in
theorem exp_offset (t a b : ℝ) :
    Real.exp (-(t * a)) = Real.exp (-(t * b)) * Real.exp (-(t * (a - b))) := by
  rw [← Real.exp_add]; ring_nf

/-- Rescaled partition mass of the tracked well. -/
theorem tendsto_Z₀ :
    Tendsto (fun t ↦ (∫ x, ψ₀ x * Real.exp (-(t * F x (p t)))) / t ^ (-(1 / 2 : ℝ))) atTop
      (𝓝 hd.C₀) := by
  have h := hd.well₀.tendsto_den (g := fun _ ↦ (1 : ℝ)) measurable_const (Mg := 1) (fun _ ↦ by simp)
    zero_le_one
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [well₀_subst ht (fun y ↦ Real.exp (-y))]

/-- Rescaled energy numerator of the tracked well. -/
theorem tendsto_Q₀ :
    Tendsto (fun t ↦ (∫ x, ψ₀ x * (t * F x (p t) * Real.exp (-(t * F x (p t))))) /
      t ^ (-(1 / 2 : ℝ))) atTop (𝓝 hd.J₀) := by
  have h := hd.well₀.tendsto_num (g := fun _ ↦ (1 : ℝ)) measurable_const (Mg := 1) (fun _ ↦ by simp)
    zero_le_one
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [well₀_subst ht (fun y ↦ y * Real.exp (-y))]

/-- Rescaled partition mass of the lifted well, offset removed. -/
theorem tendsto_Z₁ : Tendsto (fun t ↦ (∫ x, ψ₁ x * Real.exp (-(t * F x (p t)))) /
    (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * f₁ (p t))))) atTop (𝓝 hd.C₁) := by
  have h := hd.well₁.tendsto_den (g := fun _ ↦ (1 : ℝ)) measurable_const (Mg := 1) (fun _ ↦ by simp)
    zero_le_one
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have he : Real.exp (-(t * f₁ (p t))) ≠ 0 := (Real.exp_pos _).ne'
  rw [← div_div, eq_div_iff he, ← integral_mul_const, well₁_subst (x₁ := x₁) ht (fun y ↦ Real.exp (-y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Rescaled energy numerator of the lifted well: the offset contributes `z · C₁`. -/
theorem tendsto_Q₁ : Tendsto (fun t ↦ (∫ x, ψ₁ x * (t * F x (p t) * Real.exp (-(t * F x (p t))))) /
    (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * f₁ (p t))))) atTop (𝓝 (z * hd.C₁ + hd.J₁)) := by
  have hN := hd.well₁.tendsto_num (g := fun _ ↦ (1 : ℝ)) measurable_const (Mg := 1)
    (fun _ ↦ by simp) zero_le_one
  have hD := hd.well₁.tendsto_den (g := fun _ ↦ (1 : ℝ)) measurable_const (Mg := 1)
    (fun _ ↦ by simp) zero_le_one
  simp only [one_mul] at hN hD
  have h := (hd.hz.mul hD).add hN
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hd.well₁.lower, hd.well₁.G_nonneg] with t ht hl hG
  have he : Real.exp (-(t * f₁ (p t))) ≠ 0 := (Real.exp_pos _).ne'
  have hint1 := hd.well₁.integrable_den hl
  have hint2 := hd.well₁.integrable_num hl hG
  rw [← div_div, eq_div_iff he, well₁_subst (x₁ := x₁) ht (fun y ↦ y * Real.exp (-y)), ← integral_const_mul,
    ← integral_add (hint1.const_mul _) hint2, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only
  rw [exp_offset t (F (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) (p t)) (f₁ (p t))]
  ring

/-- The gap remainder for the partition function. -/
theorem abs_RZ_le {t : ℝ} (ht : 0 ≤ t) (hgap : ∀ x, ρ x ≠ 0 → g ≤ F x (p t)) :
    |∫ x, ρ x * Real.exp (-(t * F x (p t)))| ≤ Real.exp (-(t * g)) * ∫ x, |ρ x| := by
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hd.ρ_int.abs.const_mul _)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, mul_comm]
  by_cases hx : ρ x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
      have := hgap x hx; nlinarith)) (abs_nonneg _)

/-- The gap remainder for the energy numerator. -/
theorem abs_RQ_le {t : ℝ} (ht : 0 ≤ t) (hgap : ∀ x, ρ x ≠ 0 → g ≤ F x (p t)) :
    |∫ x, ρ x * (t * F x (p t) * Real.exp (-(t * F x (p t))))| ≤
      2 * Real.exp (-(t * g / 2)) * ∫ x, |ρ x| := by
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hd.ρ_int.abs.const_mul _)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have hy : 0 ≤ t * F x (p t) := mul_nonneg ht (hd.F_nonneg _ _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hy (Real.exp_pos _).le), mul_comm]
  by_cases hx : ρ x = 0
  · simp [hx]
  · refine mul_le_mul_of_nonneg_right ((mul_exp_neg_le_two_mul_exp_neg_half _).trans ?_)
      (abs_nonneg _)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have := hgap x hx
    nlinarith

/-- Integrability of the localised pieces. -/
theorem integrable_piece {ψ : ℝ → ℝ} (hψ : Integrable ψ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable fun x ↦ ψ x * Real.exp (-(t * F x (p t))) := by
  have hF := hd.F_cont
  refine hψ.mul_bdd (c := 1) (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, Real.abs_exp]
  exact Real.exp_le_one_iff.mpr (by nlinarith [hd.F_nonneg x (p t)])

theorem integrable_piece_energy {ψ : ℝ → ℝ} (hψ : Integrable ψ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable fun x ↦ ψ x * (t * F x (p t) * Real.exp (-(t * F x (p t)))) := by
  have hF := hd.F_cont
  refine hψ.mul_bdd (c := 1) (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg ht (hd.F_nonneg _ _))
    (Real.exp_pos _).le)]
  exact mul_exp_neg_le_one _

/-- The chart-assembly data of the two wells. -/
theorem chartAssembly : ChartAssembly
    ![fun t ↦ t ^ (-(1 / 2 : ℝ)), fun t ↦ t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * f₁ (p t)))]
    ![fun t ↦ ∫ x, ψ₀ x * Real.exp (-(t * F x (p t))),
      fun t ↦ ∫ x, ψ₁ x * Real.exp (-(t * F x (p t)))]
    ![fun t ↦ ∫ x, ψ₀ x * (t * F x (p t) * Real.exp (-(t * F x (p t)))),
      fun t ↦ ∫ x, ψ₁ x * (t * F x (p t) * Real.exp (-(t * F x (p t))))]
    ![hd.C₀, hd.C₁] ![hd.J₀, z * hd.C₁ + hd.J₁]
    (fun t ↦ ∫ x, ρ x * Real.exp (-(t * F x (p t))))
    (fun t ↦ ∫ x, ρ x * (t * F x (p t) * Real.exp (-(t * F x (p t)))))
    (min hd.C₀ hd.C₁) (max |hd.J₀| |z * hd.C₁ + hd.J₁|) where
  hc₀ := lt_min hd.Z₀_pos hd.Z₁_pos
  L_pos := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact Fin.forall_fin_two.mpr ⟨Real.rpow_pos_of_pos ht _,
      mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)⟩
  C_lb := Fin.forall_fin_two.mpr ⟨min_le_left _ _, min_le_right _ _⟩
  J_bd := Fin.forall_fin_two.mpr ⟨le_max_left _ _, le_max_right _ _⟩
  Z_lim := fun i ↦ by
    fin_cases i
    · simpa using hd.tendsto_Z₀
    · simpa using hd.tendsto_Z₁
  Q_lim := fun i ↦ by
    fin_cases i
    · simpa using hd.tendsto_Q₀
    · simpa using hd.tendsto_Q₁
  RZ_lim := by
    have hlim : Tendsto (fun t : ℝ ↦ t ^ (1 / 2 : ℝ) * Real.exp (-g * t) * ∫ x, |ρ x|) atTop
        (𝓝 0) := by
      simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) g hd.hg).mul_const
        (∫ x, |ρ x|)
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun t ↦ abs_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop 0, hd.gap] with t ht hgap
    simp only [Function.comp_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hL : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
    have hS : t ^ (-(1 / 2 : ℝ)) ≤ t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * f₁ (p t))) := by
      have := mul_pos hL (Real.exp_pos (-(t * f₁ (p t))))
      linarith
    have hpow : (t ^ (-(1 / 2 : ℝ)))⁻¹ = t ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg ht.le, inv_inv]
    rw [abs_div, abs_of_pos (lt_of_lt_of_le hL hS)]
    calc |∫ x, ρ x * Real.exp (-(t * F x (p t)))| / (t ^ (-(1 / 2 : ℝ)) + _)
        ≤ |∫ x, ρ x * Real.exp (-(t * F x (p t)))| / t ^ (-(1 / 2 : ℝ)) :=
          div_le_div_of_nonneg_left (abs_nonneg _) hL hS
      _ ≤ (Real.exp (-(t * g)) * ∫ x, |ρ x|) / t ^ (-(1 / 2 : ℝ)) :=
          div_le_div_of_nonneg_right (hd.abs_RZ_le ht.le hgap) hL.le
      _ = t ^ (1 / 2 : ℝ) * Real.exp (-g * t) * ∫ x, |ρ x| := by
          rw [div_eq_mul_inv, hpow]; ring_nf
  RQ_lim := by
    have hlim : Tendsto (fun t : ℝ ↦ 2 * (t ^ (1 / 2 : ℝ) * Real.exp (-(g / 2) * t)) *
        ∫ x, |ρ x|) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (g / 2)
        (half_pos hd.hg)).const_mul 2).mul_const (∫ x, |ρ x|)
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun t ↦ abs_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop 0, hd.gap] with t ht hgap
    simp only [Function.comp_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hL : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
    have hS : t ^ (-(1 / 2 : ℝ)) ≤ t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * f₁ (p t))) := by
      have := mul_pos hL (Real.exp_pos (-(t * f₁ (p t))))
      linarith
    have hpow : (t ^ (-(1 / 2 : ℝ)))⁻¹ = t ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg ht.le, inv_inv]
    rw [abs_div, abs_of_pos (lt_of_lt_of_le hL hS)]
    calc |∫ x, ρ x * (t * F x (p t) * Real.exp (-(t * F x (p t))))| / (t ^ (-(1 / 2 : ℝ)) + _)
        ≤ |∫ x, ρ x * (t * F x (p t) * Real.exp (-(t * F x (p t))))| / t ^ (-(1 / 2 : ℝ)) :=
          div_le_div_of_nonneg_left (abs_nonneg _) hL hS
      _ ≤ (2 * Real.exp (-(t * g / 2)) * ∫ x, |ρ x|) / t ^ (-(1 / 2 : ℝ)) :=
          div_le_div_of_nonneg_right (hd.abs_RQ_le ht.le hgap) hL.le
      _ = 2 * (t ^ (1 / 2 : ℝ) * Real.exp (-(g / 2) * t)) * ∫ x, |ρ x| := by
          rw [div_eq_mul_inv, hpow]; ring_nf

/-- **The two-well theorem.** The energy statistic converges to the Boltzmann-weighted mixture of the
two well energies, the lifted well carrying the extra energy `z` and the mass factor `e^{-z}`. -/
theorem tendsto_energy :
    Tendsto (fun t ↦ edgeEnergy χ F (p t) t) atTop
      (𝓝 ((hd.J₀ + Real.exp (-z) * (z * hd.C₁ + hd.J₁)) / (hd.C₀ + Real.exp (-z) * hd.C₁))) := by
  have hrat : Tendsto (fun t ↦ (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * f₁ (p t)))) /
      t ^ (-(1 / 2 : ℝ))) atTop (𝓝 (Real.exp (-z))) := by
    have h := (Real.continuous_exp.tendsto _).comp hd.hz.neg
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hL : t ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    simp only [Function.comp]
    rw [mul_div_cancel_left₀ _ hL]
  have h := two_chart_limit hd.chartAssembly (Real.exp_pos _).le (by simpa using hrat)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hint0 := hd.integrable_piece hd.ψ₀_int ht.le
  have hint1 := hd.integrable_piece hd.ψ₁_int ht.le
  have hintρ := hd.integrable_piece hd.ρ_int ht.le
  have hint0' := hd.integrable_piece_energy hd.ψ₀_int ht.le
  have hint1' := hd.integrable_piece_energy hd.ψ₁_int ht.le
  have hintρ' := hd.integrable_piece_energy hd.ρ_int ht.le
  have h01 : Integrable fun x ↦ ψ₀ x * Real.exp (-(t * F x (p t))) +
      ψ₁ x * Real.exp (-(t * F x (p t))) := hint0.add hint1
  have h01' : Integrable fun x ↦ ψ₀ x * (t * F x (p t) * Real.exp (-(t * F x (p t)))) +
      ψ₁ x * (t * F x (p t) * Real.exp (-(t * F x (p t)))) := hint0'.add hint1'
  simp only [edgeEnergy]
  rw [← integral_add hint0 hint1, ← integral_add h01 hintρ, ← integral_add hint0' hint1',
    ← integral_add h01' hintρ', mul_div_assoc', ← integral_const_mul]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [hd.partition x]
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [hd.partition x]
    ring

/-- **The hump.** Two wells of the same type and mass constant (`C₀ = C₁ = C`, well energies
`J₀ = J₁ = C/2`) give `1/2 + z/(1 + e^z)`. -/
theorem tendsto_energy_hump (hC : hd.C₁ = hd.C₀) (hJ₀ : hd.J₀ = 1 / 2 * hd.C₀)
    (hJ₁ : hd.J₁ = 1 / 2 * hd.C₀) :
    Tendsto (fun t ↦ edgeEnergy χ F (p t) t) atTop (𝓝 (humpProfile z)) := by
  have h := hd.tendsto_energy
  rw [hC, hJ₀, hJ₁] at h
  have heq : (1 / 2 * hd.C₀ + Real.exp (-z) * (z * hd.C₀ + 1 / 2 * hd.C₀)) /
      (hd.C₀ + Real.exp (-z) * hd.C₀) = humpProfile z := by
    rw [← twoWell_energy_eq_hump (A := hd.C₀) hd.Z₀_pos]
    congr 1 <;> ring
  rw [← heq]
  exact h

end

end TwoWellData

end Laplace.Multi
