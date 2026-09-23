/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TwoWell
import Laplace.Multi.GaussianMomentsPosDef

/-!
# The Gaussian well: from a quadratic Taylor bound to the rescaling hypotheses

A `C²`-type well along a schedule: the shifted loss `F(x₁(p t) + y, p t) − f₁(p t)` satisfies a
uniform quadratic Taylor bound with curvature `A(p t) → Al > 0` and a uniform lower bound `κ y²` on
`|y| ≤ δ`, the centre converges, and the localiser `ψ` is continuous, bounded and supported in
`|x − x₁l| < δ/2` (`GaussianWellData`). Then the well satisfies the dominated rescaling hypotheses
at the Gaussian scale with `Φ₀ = Al u²/2` (`GaussianWellData.toRescaledData`), so the two-well
theorem applies to two such wells (`TwoWellData.of_gaussian`). The Gaussian well constants are
`C = ψ(x₁l) √(2π/Al)` and `J = C/2` (`gaussian_Z`, `gaussian_energy_half`), so two Gaussian wells
of equal mass constant give the hump (`TwoWellData.of_gaussian_hump`). Closes the gap left by
`TwoWell.lean` (germbij_slop S14, item D).
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

/-- `∫ e^{-(A/2)u²} = √(2π/A)`. -/
theorem gaussian_Z {A : ℝ} (hA : 0 < A) :
    ∫ u : ℝ, Real.exp (-(A / 2 * u ^ 2)) = Real.sqrt (2 * π / A) := by
  have h := integral_gaussian (A / 2)
  simp only [neg_mul] at h
  rw [h]
  congr 1
  field_simp

/-- The Gaussian energy is one half: `∫ (A/2)u² e^{-(A/2)u²} = ½ ∫ e^{-(A/2)u²}`. -/
theorem gaussian_energy_half {A : ℝ} (hA : 0 < A) :
    ∫ u : ℝ, A / 2 * u ^ 2 * Real.exp (-(A / 2 * u ^ 2)) =
      1 / 2 * ∫ u : ℝ, Real.exp (-(A / 2 * u ^ 2)) := by
  set s := Real.sqrt A with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hA
  have hs2 : s ^ 2 = A := Real.sq_sqrt hA.le
  have e1 : ∀ x : ℝ, A / 2 * (s⁻¹ * x) ^ 2 = x ^ 2 / 2 := by
    intro x
    rw [mul_pow, inv_pow, hs2]
    field_simp
  have h1 := Measure.integral_comp_mul_left
    (fun u : ℝ ↦ A / 2 * u ^ 2 * Real.exp (-(A / 2 * u ^ 2))) s⁻¹
  have h2 := Measure.integral_comp_mul_left (fun u : ℝ ↦ Real.exp (-(A / 2 * u ^ 2))) s⁻¹
  simp only [e1, inv_inv, abs_of_pos hs0, smul_eq_mul] at h1 h2
  have hm : ∫ x : ℝ, x ^ 2 / 2 * Real.exp (-(x ^ 2 / 2)) = 1 / 2 * Real.sqrt (2 * π) := by
    rw [← integral_sq_mul_exp_neg_sq_div_two, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [neg_div]
    ring
  have h0 : ∫ x : ℝ, Real.exp (-(x ^ 2 / 2)) = Real.sqrt (2 * π) := by
    have := integral_gaussian (1 / 2 : ℝ)
    rw [show (2 * π : ℝ) = π / (1 / 2) by ring, ← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    congr 1
    ring
  rw [hm] at h1
  rw [h0] at h2
  apply mul_left_cancel₀ hs0.ne'
  linear_combination -h1 + (1 / 2 : ℝ) * h2

/-- A well with a uniform quadratic Taylor bound and a uniform lower bound along the schedule. -/
structure GaussianWellData (F : ℝ → ℝ → ℝ) (p x₁ f₁ ψ A : ℝ → ℝ) (Al x₁l δ κ K Mψ : ℝ) :
    Prop where
  F_cont : Continuous (Function.uncurry F)
  hδ : 0 < δ
  hκ : 0 < κ
  hA : 0 < Al
  A_lim : Tendsto (fun t ↦ A (p t)) atTop (𝓝 Al)
  x₁_lim : Tendsto (fun t ↦ x₁ (p t)) atTop (𝓝 x₁l)
  taylor : ∀ᶠ t in atTop, ∀ y, |y| ≤ δ →
    |F (x₁ (p t) + y) (p t) - f₁ (p t) - A (p t) / 2 * y ^ 2| ≤ K * |y| ^ 3
  lower : ∀ᶠ t in atTop, ∀ y, |y| ≤ δ → κ * y ^ 2 ≤ F (x₁ (p t) + y) (p t) - f₁ (p t)
  ψ_cont : Continuous ψ
  ψ_bd : ∀ x, |ψ x| ≤ Mψ
  ψ_supp : ∀ x, ψ x ≠ 0 → |x - x₁l| < δ / 2

namespace GaussianWellData

variable {F : ℝ → ℝ → ℝ} {p x₁ f₁ ψ A : ℝ → ℝ} {Al x₁l δ κ K Mψ : ℝ}
  (hd : GaussianWellData F p x₁ f₁ ψ A Al x₁l δ κ K Mψ)
include hd

/-- Where the localiser is nonzero, the rescaled displacement is within the Taylor radius. -/
theorem eventually_small : ∀ᶠ t in atTop, 0 < t ∧
    ∀ u, ψ (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) ≠ 0 → |t ^ (-(1 / 2 : ℝ)) * u| ≤ δ := by
  have hx := hd.x₁_lim.eventually (Metric.ball_mem_nhds x₁l (half_pos hd.hδ))
  filter_upwards [eventually_gt_atTop 0, hx] with t ht hxt
  refine ⟨ht, fun u hu ↦ ?_⟩
  have h1 := hd.ψ_supp _ hu
  rw [Real.dist_eq] at hxt
  have : |t ^ (-(1 / 2 : ℝ)) * u| ≤ |x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u - x₁l| + |x₁ (p t) - x₁l| := by
    have := abs_sub (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u - x₁l) (x₁ (p t) - x₁l)
    rw [show x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u - x₁l - (x₁ (p t) - x₁l) =
      t ^ (-(1 / 2 : ℝ)) * u by ring] at this
    exact this
  linarith

omit hd in
theorem sq_rescale {t : ℝ} (ht : 0 < t) (u : ℝ) : t * (t ^ (-(1 / 2 : ℝ)) * u) ^ 2 = u ^ 2 := by
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

omit hd in
theorem cube_rescale {t : ℝ} (ht : 0 < t) (u : ℝ) :
    t * |t ^ (-(1 / 2 : ℝ)) * u| ^ 3 = t ^ (-(1 / 2 : ℝ)) * |u| ^ 3 := by
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _), mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul ht.le, ← mul_assoc]
  congr 1
  have := Real.rpow_add ht 1 (-(1 / 2 : ℝ) * (3 : ℕ))
  rw [Real.rpow_one] at this
  rw [← this]
  norm_num

/-- The Gaussian well satisfies the dominated rescaling hypotheses at the scale `t^{-1/2}`. -/
theorem toRescaledData :
    RescaledData volume (fun t u ↦ t * (F (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) (p t) - f₁ (p t)))
      (fun t u ↦ ψ (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u)) (fun u ↦ Al / 2 * u ^ 2)
      (fun _ ↦ ψ x₁l) (fun _ ↦ Mψ) (min 1 (2 * κ / Al)) where
  hc := lt_min one_pos (div_pos (mul_pos two_pos hd.hκ) hd.hA)
  hc1 := min_le_left _ _
  G_meas := fun t ↦ by
    have := hd.F_cont
    exact Continuous.measurable (by fun_prop)
  w_meas := fun t ↦ by
    have := hd.ψ_cont
    exact Continuous.measurable (by fun_prop)
  G_nonneg := by
    filter_upwards [hd.eventually_small, hd.lower] with t ht hl u hu
    have h := hl _ (ht.2 u hu)
    have : 0 ≤ κ * (t ^ (-(1 / 2 : ℝ)) * u) ^ 2 := mul_nonneg hd.hκ.le (sq_nonneg _)
    exact mul_nonneg ht.1.le (by linarith)
  Φ₀_nonneg := fun u ↦ mul_nonneg (div_nonneg hd.hA.le two_pos.le) (sq_nonneg u)
  G_lim := fun u ↦ by
    have hsmall : ∀ᶠ t : ℝ in atTop, |t ^ (-(1 / 2 : ℝ)) * u| ≤ δ := by
      have h0 : Tendsto (fun t : ℝ ↦ t ^ (-(1 / 2 : ℝ)) * u) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).mul_const u
      have := h0.eventually (Metric.closedBall_mem_nhds (0 : ℝ) hd.hδ)
      filter_upwards [this] with t ht
      rwa [Real.dist_eq, sub_zero] at ht
    have hA : Tendsto (fun t ↦ A (p t) / 2 * u ^ 2) atTop (𝓝 (Al / 2 * u ^ 2)) :=
      (hd.A_lim.div_const 2).mul_const _
    have hR : Tendsto (fun t : ℝ ↦ t * (F (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) (p t) - f₁ (p t)) -
        A (p t) / 2 * u ^ 2) atTop (𝓝 0) := by
      have hb : Tendsto (fun t : ℝ ↦ K * (t ^ (-(1 / 2 : ℝ)) * |u| ^ 3)) atTop (𝓝 0) := by
        simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).mul_const
          (|u| ^ 3)).const_mul K
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Filter.Eventually.of_forall fun t ↦ abs_nonneg _) ?_ hb
      filter_upwards [hd.taylor, hsmall, eventually_gt_atTop 0] with t htay hs ht
      have := htay _ hs
      simp only [Function.comp_apply]
      have e : t * (F (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) (p t) - f₁ (p t)) -
          A (p t) / 2 * u ^ 2 =
          t * (F (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) (p t) - f₁ (p t) -
            A (p t) / 2 * (t ^ (-(1 / 2 : ℝ)) * u) ^ 2) := by
        rw [← sq_rescale ht u]
        ring
      rw [e, abs_mul, abs_of_pos ht, ← cube_rescale ht u, ← mul_assoc, mul_comm K t, mul_assoc]
      exact mul_le_mul_of_nonneg_left this ht.le
    have := hR.add hA
    rw [zero_add] at this
    exact this.congr' (Filter.Eventually.of_forall fun t ↦ by ring)
  w_lim := fun u ↦ by
    have h0 : Tendsto (fun t : ℝ ↦ x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) atTop (𝓝 x₁l) := by
      have := hd.x₁_lim.add
        ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).mul_const u)
      simpa using this
    exact (hd.ψ_cont.tendsto x₁l).comp h0
  w_bd := fun t u ↦ hd.ψ_bd _
  lower := by
    filter_upwards [hd.eventually_small, hd.lower] with t ht hl u hu
    have h := hl _ (ht.2 u hu)
    have hκ' : min 1 (2 * κ / Al) * (Al / 2 * u ^ 2) ≤ κ * u ^ 2 := by
      have h1 : min 1 (2 * κ / Al) ≤ 2 * κ / Al := min_le_right _ _
      have h2 : 0 ≤ Al / 2 * u ^ 2 := mul_nonneg (div_nonneg hd.hA.le two_pos.le) (sq_nonneg u)
      have hAne : Al ≠ 0 := hd.hA.ne'
      calc min 1 (2 * κ / Al) * (Al / 2 * u ^ 2) ≤ 2 * κ / Al * (Al / 2 * u ^ 2) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = κ * u ^ 2 := by field_simp
    calc min 1 (2 * κ / Al) * (Al / 2 * u ^ 2) ≤ κ * u ^ 2 := hκ'
      _ = t * (κ * (t ^ (-(1 / 2 : ℝ)) * u) ^ 2) := by rw [mul_left_comm, sq_rescale ht.1 u]
      _ ≤ t * (F (x₁ (p t) + t ^ (-(1 / 2 : ℝ)) * u) (p t) - f₁ (p t)) :=
          mul_le_mul_of_nonneg_left h ht.1.le
  int := by
    have hb : 0 < min 1 (2 * κ / Al) * (Al / 2) :=
      mul_pos (lt_min one_pos (div_pos (mul_pos two_pos hd.hκ) hd.hA)) (half_pos hd.hA)
    refine ((integrable_exp_neg_mul_sq hb).const_mul Mψ).congr
      (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only
    ring_nf
  Φint := by
    have hb : 0 < min 1 (2 * κ / Al) * (Al / 2) :=
      mul_pos (lt_min one_pos (div_pos (mul_pos two_pos hd.hκ) hd.hA)) (half_pos hd.hA)
    have := (integrable_abs_pow_mul_exp_neg_mul_pow hb 1 le_rfl 2).const_mul (Mψ * (Al / 2))
    refine this.congr (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only
    rw [show |u| ^ 2 = u ^ 2 from sq_abs u]
    ring_nf

end GaussianWellData

/-- **Two Gaussian wells.** The tracked well at `0` (`x₁ = 0`, `f₁ = 0`) and a moving well, both
with quadratic Taylor bounds, a partition of the prior and a gap, give `TwoWellData`. -/
theorem TwoWellData.of_gaussian {F : ℝ → ℝ → ℝ} {p x₁ f₁ χ ψ₀ ψ₁ ρ A₀ A₁ : ℝ → ℝ}
    {A₀l A₁l x₁l δ₀ δ₁ κ₀ κ₁ K₀ K₁ M₀ M₁ z g : ℝ}
    (h₀ : GaussianWellData F p (fun _ ↦ 0) (fun _ ↦ 0) ψ₀ A₀ A₀l 0 δ₀ κ₀ K₀ M₀)
    (h₁ : GaussianWellData F p x₁ f₁ ψ₁ A₁ A₁l x₁l δ₁ κ₁ K₁ M₁)
    (F_nonneg : ∀ x s, 0 ≤ F x s) (f₁_def : ∀ s, f₁ s = F (x₁ s) s)
    (hz : Tendsto (fun t ↦ t * f₁ (p t)) atTop (𝓝 z))
    (partition : ∀ x, χ x = ψ₀ x + ψ₁ x + ρ x) (ψ₀_int : Integrable ψ₀) (ψ₁_int : Integrable ψ₁)
    (ρ_int : Integrable ρ) (hg : 0 < g) (gap : ∀ᶠ t in atTop, ∀ x, ρ x ≠ 0 → g ≤ F x (p t))
    (hψ₀ : 0 < ψ₀ 0) (hψ₁ : 0 < ψ₁ x₁l) :
    TwoWellData F p x₁ f₁ χ ψ₀ ψ₁ ρ (fun u ↦ A₀l / 2 * u ^ 2) (fun u ↦ A₁l / 2 * u ^ 2)
      (fun _ ↦ ψ₀ 0) (fun _ ↦ ψ₁ x₁l) (fun _ ↦ M₀) (fun _ ↦ M₁) (min 1 (2 * κ₀ / A₀l))
      (min 1 (2 * κ₁ / A₁l)) z g where
  F_cont := h₁.F_cont
  F_nonneg := F_nonneg
  f₁_def := f₁_def
  hz := hz
  partition := partition
  ψ₀_int := ψ₀_int
  ψ₁_int := ψ₁_int
  ρ_int := ρ_int
  hg := hg
  gap := gap
  well₀ := by simpa using h₀.toRescaledData
  well₁ := h₁.toRescaledData
  Z₀_pos := by
    rw [integral_const_mul]
    exact mul_pos hψ₀ (integral_exp_pos (integrable_exp_neg_mul_sq (half_pos h₀.hA) |>.congr
      (Filter.Eventually.of_forall fun u ↦ by simp only [neg_mul])))
  Z₁_pos := by
    rw [integral_const_mul]
    exact mul_pos hψ₁ (integral_exp_pos (integrable_exp_neg_mul_sq (half_pos h₁.hA) |>.congr
      (Filter.Eventually.of_forall fun u ↦ by simp only [neg_mul])))

/-- **Two Gaussian wells of equal mass constant give the hump.** `ψ₀(0)/√A₀ = ψ₁(x₁l)/√A₁`. -/
theorem TwoWellData.of_gaussian_hump {F : ℝ → ℝ → ℝ} {p x₁ f₁ χ ψ₀ ψ₁ ρ A₀ A₁ : ℝ → ℝ}
    {A₀l A₁l x₁l δ₀ δ₁ κ₀ κ₁ K₀ K₁ M₀ M₁ z g : ℝ}
    (h₀ : GaussianWellData F p (fun _ ↦ 0) (fun _ ↦ 0) ψ₀ A₀ A₀l 0 δ₀ κ₀ K₀ M₀)
    (h₁ : GaussianWellData F p x₁ f₁ ψ₁ A₁ A₁l x₁l δ₁ κ₁ K₁ M₁)
    (F_nonneg : ∀ x s, 0 ≤ F x s) (f₁_def : ∀ s, f₁ s = F (x₁ s) s)
    (hz : Tendsto (fun t ↦ t * f₁ (p t)) atTop (𝓝 z))
    (partition : ∀ x, χ x = ψ₀ x + ψ₁ x + ρ x) (ψ₀_int : Integrable ψ₀) (ψ₁_int : Integrable ψ₁)
    (ρ_int : Integrable ρ) (hg : 0 < g) (gap : ∀ᶠ t in atTop, ∀ x, ρ x ≠ 0 → g ≤ F x (p t))
    (hψ₀ : 0 < ψ₀ 0) (hψ₁ : 0 < ψ₁ x₁l)
    (hmass : ψ₁ x₁l * Real.sqrt (2 * π / A₁l) = ψ₀ 0 * Real.sqrt (2 * π / A₀l)) :
    Tendsto (fun t ↦ edgeEnergy χ F (p t) t) atTop (𝓝 (humpProfile z)) := by
  have hd := TwoWellData.of_gaussian h₀ h₁ F_nonneg f₁_def hz partition ψ₀_int ψ₁_int ρ_int hg gap
    hψ₀ hψ₁
  refine hd.tendsto_energy_hump ?_ ?_ ?_
  · simp only [TwoWellData.C₀, TwoWellData.C₁, integral_const_mul, gaussian_Z h₀.hA,
      gaussian_Z h₁.hA]
    exact hmass
  · simp only [TwoWellData.J₀, TwoWellData.C₀, integral_const_mul]
    rw [gaussian_energy_half h₀.hA]
    ring
  · simp only [TwoWellData.J₁, TwoWellData.C₀, integral_const_mul]
    rw [gaussian_energy_half h₁.hA, gaussian_Z h₁.hA, gaussian_Z h₀.hA, ← hmass]
    ring

end Laplace.Multi
