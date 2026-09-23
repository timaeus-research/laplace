/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NewtonEdge

/-!
# The residual on the divisor determines the profile (one fibre variable, general form)

The chart-level statement behind the Newton-edge theorem, freed from the decomposition
`F = E + R` with a nonnegative remainder: along the ray `s = σ t^{-γ}` and at the fibre scale
`x = t^{-α} u`, the rescaled loss `t F(t^{-α} u, σ t^{-γ})` (the residual of `F` on the divisor
`v = 1/t` of the weighted blow-up, `EdgeResidual.lean`) is assumed to converge pointwise to a limit
`Φ₀(u)` and to dominate a fixed multiple `c Φ₀` of it (`DivisorData`). Units `a(x,s) > 0` on the
chart, higher-order terms of either sign, and a monomial density `|x|^h` are all covered.
Conclusions: the rescaled partition function, any rescaled bounded observable `g(t^α x)`
(`DivisorData.tendsto_den`), the energy numerator (`DivisorData.tendsto_num`) and the energy
statistic (`DivisorData.tendsto_energy`) converge to the Boltzmann quantities of `Φ₀` under the
density `|u|^h`. `EdgeData.toDivisorData` recovers the Newton-edge theorem as the special case
`Φ₀ = E(·,σ)`, `c = 1`, `h = 0` (germbij_slop S14).
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

/-- Chart-level hypotheses: `F ≥ 0` continuous; along the ray `s = σ t^{-γ}` the rescaled loss
`t F(t^{-α}u, σ t^{-γ})` converges pointwise to `Φ₀ u ≥ 0` and eventually dominates `c Φ₀ u`
(`0 < c ≤ 1`); the density `|u|^h` against `e^{-cΦ₀}` and `Φ₀ e^{-cΦ₀}` is integrable. -/
structure DivisorData (F : ℝ → ℝ → ℝ) (Φ₀ : ℝ → ℝ) (α γ σ c : ℝ) (h : ℕ) : Prop where
  hα : 0 < α
  hc : 0 < c
  hc1 : c ≤ 1
  F_cont : Continuous (Function.uncurry F)
  F_nonneg : ∀ x s, 0 ≤ F x s
  Φ₀_nonneg : ∀ u, 0 ≤ Φ₀ u
  lim : ∀ u, Tendsto (fun t ↦ t * F (t ^ (-α) * u) (σ * t ^ (-γ))) atTop (𝓝 (Φ₀ u))
  lower : ∀ᶠ t in atTop, ∀ u, c * Φ₀ u ≤ t * F (t ^ (-α) * u) (σ * t ^ (-γ))
  int : Integrable fun u ↦ |u| ^ h * Real.exp (-(c * Φ₀ u))
  Φint : Integrable fun u ↦ |u| ^ h * (Φ₀ u * Real.exp (-(c * Φ₀ u)))

/-- The fibre substitution `x = t^{-α} u` with a monomial density and a rescaled test function. -/
theorem rpow_mul_integral_divisor_eq {F : ℝ → ℝ → ℝ} {α : ℝ} (χ g : ℝ → ℝ) (h : ℕ) {t : ℝ}
    (ht : 0 < t) (s : ℝ) (Ψ : ℝ → ℝ) :
    t ^ (α * (h + 1)) * ∫ x, χ x * (|x| ^ h * (g (t ^ α * x) * Ψ (t * F x s))) =
      ∫ u, χ (t ^ (-α) * u) * (|u| ^ h * (g u * Ψ (t * F (t ^ (-α) * u) s))) := by
  set c : ℝ := t ^ (-α) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hcomp := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ χ x * (|x| ^ h * (g (t ^ α * x) * Ψ (t * F x s)))) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hcomp
  have hcu : ∀ u : ℝ, t ^ α * (c * u) = u := by
    intro u
    rw [hc, ← mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_mul]
  have hpt : ∀ u : ℝ, χ (c * u) * (|c * u| ^ h * (g (t ^ α * (c * u)) * Ψ (t * F (c * u) s))) =
      c ^ h * (χ (c * u) * (|u| ^ h * (g u * Ψ (t * F (c * u) s)))) := by
    intro u
    rw [hcu, abs_mul, abs_of_pos hcpos, mul_pow]
    ring
  simp only [hpt] at hcomp
  rw [integral_const_mul, eq_comm, inv_mul_eq_iff_eq_mul₀ hcpos.ne'] at hcomp
  have hpow : t ^ (α * (h + 1)) * c ^ (h + 1) = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    push_cast
    rw [show α * (h + 1) + -α * (h + 1) = 0 by ring, Real.rpow_zero]
  rw [hcomp, show t ^ (α * (h + 1)) * (c * (c ^ h * ∫ u, χ (c * u) *
    (|u| ^ h * (g u * Ψ (t * F (c * u) s))))) = (t ^ (α * (h + 1)) * c ^ (h + 1)) *
    ∫ u, χ (c * u) * (|u| ^ h * (g u * Ψ (t * F (c * u) s))) by ring, hpow, one_mul]

/-- `y e^{-y} ≤ z e^{-z} + e^{-z}` for `0 ≤ z ≤ y`. -/
theorem mul_exp_neg_le_of_le {y z : ℝ} (hz : 0 ≤ z) (hzy : z ≤ y) :
    y * Real.exp (-y) ≤ z * Real.exp (-z) + Real.exp (-z) := by
  have hsplit : y * Real.exp (-y) =
      z * Real.exp (-z) * Real.exp (-(y - z)) +
        ((y - z) * Real.exp (-(y - z))) * Real.exp (-z) := by
    rw [show -y = -z + -(y - z) by ring, Real.exp_add]
    ring
  rw [hsplit]
  have h1 : z * Real.exp (-z) * Real.exp (-(y - z)) ≤ z * Real.exp (-z) :=
    mul_le_of_le_one_right (mul_nonneg hz (Real.exp_pos _).le)
      (Real.exp_le_one_iff.mpr (by linarith))
  have h2 : ((y - z) * Real.exp (-(y - z))) * Real.exp (-z) ≤ 1 * Real.exp (-z) :=
    mul_le_mul_of_nonneg_right (mul_exp_neg_le_one _) (Real.exp_pos _).le
  linarith

namespace DivisorData

variable {F : ℝ → ℝ → ℝ} {Φ₀ : ℝ → ℝ} {α γ σ c : ℝ} {h : ℕ}

theorem continuous_rescaled (hd : DivisorData F Φ₀ α γ σ c h) (t : ℝ) :
    Continuous fun u : ℝ ↦ t * F (t ^ (-α) * u) (σ * t ^ (-γ)) :=
  continuous_const.mul
    (hd.F_cont.comp ((continuous_const.mul continuous_id).prodMk continuous_const))

theorem tendsto_scaled_cutoff (hd : DivisorData F Φ₀ α γ σ c h) {χ : ℝ → ℝ} (hχ : Cutoff χ)
    (u : ℝ) :
    Tendsto (fun t : ℝ ↦ χ (t ^ (-α) * u)) atTop (𝓝 (χ 0)) := by
  have hq : Tendsto (fun t : ℝ ↦ t ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hd.hα
  have h0 : Tendsto (fun t : ℝ ↦ t ^ (-α) * u) atTop (𝓝 0) := by simpa using hq.mul_const u
  exact (hχ.cont.tendsto 0).comp h0

/-- Rescaled partition function / rescaled bounded observable:
`t^{α(h+1)} ∫ χ |x|^h g(t^α x) e^{-tF}` converges to `χ(0) ∫ |u|^h g(u) e^{-Φ₀(u)} du`. -/
theorem tendsto_den (hd : DivisorData F Φ₀ α γ σ c h) {χ : ℝ → ℝ} (hχ : Cutoff χ) {g : ℝ → ℝ}
    (hg : Continuous g) {Mg : ℝ} (hMg : ∀ u, |g u| ≤ Mg) :
    Tendsto (fun t ↦ t ^ (α * (h + 1)) *
      ∫ x, χ x * (|x| ^ h * (g (t ^ α * x) * Real.exp (-(t * F x (σ * t ^ (-γ)))))))
      atTop (𝓝 (χ 0 * ∫ u, |u| ^ h * (g u * Real.exp (-Φ₀ u)))) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hχc := hχ.cont
  rw [← integral_const_mul]
  have key : Tendsto (fun t ↦ ∫ u, χ (t ^ (-α) * u) *
      (|u| ^ h * (g u * Real.exp (-(t * F (t ^ (-α) * u) (σ * t ^ (-γ))))))) atTop
      (𝓝 (∫ u, χ 0 * (|u| ^ h * (g u * Real.exp (-Φ₀ u))))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u ↦ M * Mg * (|u| ^ h * Real.exp (-(c * Φ₀ u))))
      (Filter.Eventually.of_forall fun t ↦ ?_) ?_ (hd.int.const_mul (M * Mg))
      (Filter.Eventually.of_forall fun u ↦ ?_)
    · have := hd.continuous_rescaled t
      exact (by fun_prop : Continuous fun u : ℝ ↦ χ (t ^ (-α) * u) *
        (|u| ^ h * (g u * Real.exp (-(t * F (t ^ (-α) * u) (σ * t ^ (-γ))))))).aestronglyMeasurable
    · filter_upwards [hd.lower] with t hlow
      refine Filter.Eventually.of_forall fun u ↦ ?_
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, Real.abs_exp,
        abs_of_nonneg (pow_nonneg (abs_nonneg u) h)]
      calc |χ (t ^ (-α) * u)| *
            (|u| ^ h * (|g u| * Real.exp (-(t * F (t ^ (-α) * u) (σ * t ^ (-γ))))))
          ≤ M * (|u| ^ h * (Mg * Real.exp (-(c * Φ₀ u)))) := by
            refine mul_le_mul (hM _) (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (by positivity) hM0
            exact mul_le_mul (hMg u) (Real.exp_le_exp.mpr (by linarith [hlow u]))
              (Real.exp_pos _).le hMg0
        _ = M * Mg * (|u| ^ h * Real.exp (-(c * Φ₀ u))) := by ring
    · have hlim : Tendsto (fun t ↦ Real.exp (-(t * F (t ^ (-α) * u) (σ * t ^ (-γ))))) atTop
          (𝓝 (Real.exp (-Φ₀ u))) := (Real.continuous_exp.tendsto _).comp (hd.lim u).neg
      exact (hd.tendsto_scaled_cutoff hχ u).mul
        (tendsto_const_nhds.mul (tendsto_const_nhds.mul hlim))
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [rpow_mul_integral_divisor_eq χ g h ht (σ * t ^ (-γ)) (fun y ↦ Real.exp (-y))]

/-- Rescaled energy numerator: `t^{α(h+1)} ∫ χ |x|^h g(t^α x) (tF) e^{-tF}` converges to
`χ(0) ∫ |u|^h g(u) Φ₀(u) e^{-Φ₀(u)} du`. -/
theorem tendsto_num (hd : DivisorData F Φ₀ α γ σ c h) {χ : ℝ → ℝ} (hχ : Cutoff χ) {g : ℝ → ℝ}
    (hg : Continuous g) {Mg : ℝ} (hMg : ∀ u, |g u| ≤ Mg) :
    Tendsto (fun t ↦ t ^ (α * (h + 1)) *
      ∫ x, χ x * (|x| ^ h * (g (t ^ α * x) *
        (t * F x (σ * t ^ (-γ)) * Real.exp (-(t * F x (σ * t ^ (-γ))))))))
      atTop (𝓝 (χ 0 * ∫ u, |u| ^ h * (g u * (Φ₀ u * Real.exp (-Φ₀ u))))) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hχc := hχ.cont
  rw [← integral_const_mul]
  have hdom : Integrable fun u ↦ M * Mg * (|u| ^ h * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) +
      Real.exp (-(c * Φ₀ u)))) := by
    refine (((hd.Φint.const_mul c).add hd.int).const_mul (M * Mg)).congr
      (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have key : Tendsto (fun t ↦ ∫ u, χ (t ^ (-α) * u) *
      (|u| ^ h * (g u * (t * F (t ^ (-α) * u) (σ * t ^ (-γ)) *
        Real.exp (-(t * F (t ^ (-α) * u) (σ * t ^ (-γ)))))))) atTop
      (𝓝 (∫ u, χ 0 * (|u| ^ h * (g u * (Φ₀ u * Real.exp (-Φ₀ u)))))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u ↦ M * Mg * (|u| ^ h * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) + Real.exp (-(c * Φ₀ u)))))
      (Filter.Eventually.of_forall fun t ↦ ?_) ?_ hdom (Filter.Eventually.of_forall fun u ↦ ?_)
    · have := hd.continuous_rescaled t
      exact (by fun_prop : Continuous fun u : ℝ ↦ χ (t ^ (-α) * u) *
        (|u| ^ h * (g u * (t * F (t ^ (-α) * u) (σ * t ^ (-γ)) *
          Real.exp (-(t * F (t ^ (-α) * u) (σ * t ^ (-γ)))))))).aestronglyMeasurable
    · filter_upwards [hd.lower, eventually_gt_atTop 0] with t hlow ht
      refine Filter.Eventually.of_forall fun u ↦ ?_
      set y := t * F (t ^ (-α) * u) (σ * t ^ (-γ)) with hy
      have hy0 : 0 ≤ y := mul_nonneg ht.le (hd.F_nonneg _ _)
      have hz0 : 0 ≤ c * Φ₀ u := mul_nonneg hd.hc.le (hd.Φ₀_nonneg u)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (mul_nonneg hy0 (Real.exp_pos _).le),
        abs_of_nonneg (pow_nonneg (abs_nonneg u) h)]
      calc |χ (t ^ (-α) * u)| * (|u| ^ h * (|g u| * (y * Real.exp (-y))))
          ≤ M * (|u| ^ h *
              (Mg * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) + Real.exp (-(c * Φ₀ u))))) := by
            refine mul_le_mul (hM _) (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (by positivity) hM0
            exact mul_le_mul (hMg u) (mul_exp_neg_le_of_le hz0 (hlow u))
              (mul_nonneg hy0 (Real.exp_pos _).le) hMg0
        _ = M * Mg * (|u| ^ h * (c * Φ₀ u * Real.exp (-(c * Φ₀ u)) + Real.exp (-(c * Φ₀ u)))) := by
            ring
    · have hin := hd.lim u
      exact (hd.tendsto_scaled_cutoff hχ u).mul (tendsto_const_nhds.mul (tendsto_const_nhds.mul
        (hin.mul ((Real.continuous_exp.tendsto _).comp hin.neg))))
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [rpow_mul_integral_divisor_eq χ g h ht (σ * t ^ (-γ)) (fun y ↦ y * Real.exp (-y))]

theorem integrable_limit_den (hd : DivisorData F Φ₀ α γ σ c h) :
    Integrable fun u ↦ |u| ^ h * Real.exp (-Φ₀ u) := by
  refine hd.int.mono' (by
    have : Measurable Φ₀ := by
      refine measurable_of_tendsto_metrizable' atTop (fun t ↦ (hd.continuous_rescaled t).measurable)
        (tendsto_pi_nhds.mpr hd.lim)
    exact Measurable.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  have := hd.Φ₀_nonneg u
  nlinarith [hd.hc1]

theorem integral_limit_den_pos (hd : DivisorData F Φ₀ α γ σ c h) :
    0 < ∫ u, |u| ^ h * Real.exp (-Φ₀ u) := by
  refine (integral_pos_iff_support_of_nonneg (fun u ↦ by positivity) hd.integrable_limit_den).mpr ?_
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support fun u ↦ |u| ^ h * Real.exp (-Φ₀ u) := by
    intro u hu
    have hu' : 0 < u := hu
    simp only [Function.mem_support]
    positivity
  calc (0 : ENNReal) < volume (Set.Ioi (0 : ℝ)) := by rw [Real.volume_Ioi]; exact ENNReal.coe_lt_top
    _ ≤ _ := measure_mono hsub

end DivisorData

/-- The energy statistic with a monomial density `|x|^h` on the fibre. -/
noncomputable def divisorEnergy (χ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (h : ℕ) (s t : ℝ) : ℝ :=
  t * ((∫ x, χ x * (|x| ^ h * (F x s * Real.exp (-(t * F x s))))) /
    ∫ x, χ x * (|x| ^ h * Real.exp (-(t * F x s))))

/-- **The profile is the Boltzmann energy of the residual on the divisor.** -/
theorem DivisorData.tendsto_energy {F : ℝ → ℝ → ℝ} {Φ₀ : ℝ → ℝ} {α γ σ c : ℝ} {h : ℕ}
    (hd : DivisorData F Φ₀ α γ σ c h) {χ : ℝ → ℝ} (hχ : Cutoff χ) :
    Tendsto (fun t ↦ divisorEnergy χ F h (σ * t ^ (-γ)) t) atTop
      (𝓝 ((∫ u, |u| ^ h * (Φ₀ u * Real.exp (-Φ₀ u))) / ∫ u, |u| ^ h * Real.exp (-Φ₀ u))) := by
  have hN := hd.tendsto_num hχ (g := fun _ ↦ (1 : ℝ)) continuous_const (Mg := 1)
    (fun _ ↦ by simp)
  have hD := hd.tendsto_den hχ (g := fun _ ↦ (1 : ℝ)) continuous_const (Mg := 1)
    (fun _ ↦ by simp)
  simp only [one_mul] at hN hD
  have hD0 : χ 0 * ∫ u, |u| ^ h * Real.exp (-Φ₀ u) ≠ 0 :=
    (mul_pos hχ.pos hd.integral_limit_den_pos).ne'
  have := hN.div hD hD0
  rw [mul_div_mul_left _ _ hχ.pos.ne'] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Pi.div_apply, divisorEnergy]
  have hpow : (t ^ (α * (h + 1)) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  rw [mul_div_mul_left _ _ hpow, mul_div_assoc', ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  ring

/-- **Rescaled observables.** `⟨g(t^α x)⟩_{t, σ t^{-γ}}` (density `|x|^h`) converges to the
Boltzmann expectation of `g` under `|u|^h e^{-Φ₀(u)}`. -/
theorem DivisorData.tendsto_rescaled_expectation {F : ℝ → ℝ → ℝ} {Φ₀ : ℝ → ℝ} {α γ σ c : ℝ}
    {h : ℕ} (hd : DivisorData F Φ₀ α γ σ c h) {χ : ℝ → ℝ} (hχ : Cutoff χ) {g : ℝ → ℝ}
    (hg : Continuous g) {Mg : ℝ} (hMg : ∀ u, |g u| ≤ Mg) :
    Tendsto (fun t ↦ (∫ x, χ x * (|x| ^ h * (g (t ^ α * x) *
        Real.exp (-(t * F x (σ * t ^ (-γ))))))) /
      ∫ x, χ x * (|x| ^ h * Real.exp (-(t * F x (σ * t ^ (-γ)))))) atTop
      (𝓝 ((∫ u, |u| ^ h * (g u * Real.exp (-Φ₀ u))) / ∫ u, |u| ^ h * Real.exp (-Φ₀ u))) := by
  have hN := hd.tendsto_den hχ hg hMg
  have hD := hd.tendsto_den hχ (g := fun _ ↦ (1 : ℝ)) continuous_const (Mg := 1)
    (fun _ ↦ by simp)
  simp only [one_mul] at hD
  have hD0 : χ 0 * ∫ u, |u| ^ h * Real.exp (-Φ₀ u) ≠ 0 :=
    (mul_pos hχ.pos hd.integral_limit_den_pos).ne'
  have := hN.div hD hD0
  rw [mul_div_mul_left _ _ hχ.pos.ne'] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Pi.div_apply]
  have hpow : (t ^ (α * (h + 1)) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  rw [mul_div_mul_left _ _ hpow]

/-- The Newton-edge hypotheses are a special case: `Φ₀ = E(·,σ)`, `c = 1`, no density. -/
theorem EdgeData.toDivisorData {E R : ℝ → ℝ → ℝ} {α γ σ : ℝ} (hd : EdgeData E R α γ σ) :
    DivisorData (fun x s ↦ E x s + R x s) (fun u ↦ E u σ) α γ σ 1 0 where
  hα := hd.hα
  hc := one_pos
  hc1 := le_rfl
  F_cont := by
    have h1 := hd.E_cont
    have h2 := hd.R_cont
    exact (by fun_prop : Continuous fun p : ℝ × ℝ ↦ E p.1 p.2 + R p.1 p.2)
  F_nonneg := fun x s ↦ add_nonneg (hd.E_nonneg x s) (hd.R_nonneg x s)
  Φ₀_nonneg := fun u ↦ hd.E_nonneg u σ
  lim := fun u ↦ by
    have h := (hd.R_lim u).const_add (E u σ)
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hσ : t ^ γ * (σ * t ^ (-γ)) = σ := by
      rw [mul_comm σ, ← mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_mul]
    rw [mul_add, hd.quasi.mul_apply_rescaled ht, hσ]
  lower := by
    filter_upwards [eventually_gt_atTop 0] with t ht u
    have hσ : t ^ γ * (σ * t ^ (-γ)) = σ := by
      rw [mul_comm σ, ← mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_mul]
    rw [mul_add, hd.quasi.mul_apply_rescaled ht, hσ, one_mul]
    have := mul_nonneg ht.le (hd.R_nonneg (t ^ (-α) * u) (σ * t ^ (-γ)))
    linarith
  int := by simpa using hd.E_int
  Φint := by simpa using hd.EE_int

end Laplace.Multi
