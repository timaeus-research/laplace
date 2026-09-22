/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.WallCrossover

/-!
# The low-resolution picture of a wall: continuity at finite temperature and the response

For the wall chart `L_ε(x) = (ε + x^{2m}) x^{2k}` the energy statistic is `G(ε t^{m/(k+m)})`
(`wallEnergy_eq_wallCross`). Here:

* `G` is continuous on `[0, ∞)` (`wallCross_continuousOn`), so at fixed temperature the map
  `ε ↦ t E_{ε,t}[L_ε]` is continuous across the wall (`wallEnergy_continuousOn`): the jump of the
  local type is never seen as a discontinuity at finite temperature;
* the wall is detected by the energy statistic: its two chamber values differ
  (`wallCross_zero_lt_chamber`);
* `G` is differentiable on `(0, ∞)` with
  `G'(σ) = E_σ[u^{2k}] − Cov_σ(σ u^{2k} + u^{2(k+m)}, u^{2k})` (`hasDerivAt_wallCross`), the Level-1
  response formula on the rescaled variable, and the response of the chart energy to the wall
  parameter collapses: `∂_ε (t E_{ε,t}[L_ε]) = t^{m/(k+m)} G'(ε t^{m/(k+m)})`
  (`hasDerivAt_wallEnergy`) — one shape, amplitude `t^{m/(k+m)}`, width `t^{-m/(k+m)}` in `ε`.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The wall is visible to the energy statistic: the wall type is below the chamber type. -/
theorem wallCross_zero_lt_chamber (k m h : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ((h : ℝ) + 1) / (2 * (k + m)) < ((h : ℝ) + 1) / (2 * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  linarith

/-! ### Continuity on `[0, ∞)` -/

theorem integrable_wall_dom (k m h j : ℕ) (hn : 1 ≤ k + m) (S : ℝ) :
    Integrable fun u : ℝ ↦ (S * u ^ (2 * k) + u ^ (2 * (k + m))) * |u| ^ j *
      (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))) := by
  have h1 := (integrable_abs_pow_mul_exp_neg_mul_pow one_pos (k + m) hn (h + j + 2 * k)).const_mul S
  have h2 := integrable_abs_pow_mul_exp_neg_mul_pow one_pos (k + m) hn (h + j + 2 * (k + m))
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [Pi.add_apply]
  have e1 : |u| ^ (h + j + 2 * k) = |u| ^ h * |u| ^ j * u ^ (2 * k) := by
    rw [pow_add, pow_add, abs_pow_even]
  have e2 : |u| ^ (h + j + 2 * (k + m)) = |u| ^ h * |u| ^ j * u ^ (2 * (k + m)) := by
    rw [pow_add, pow_add, abs_pow_even]
  rw [e1, e2]
  ring

theorem abs_wall_num_le {k m h : ℕ} {s S u : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S) :
    |(s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u| ≤
      (S * u ^ (2 * k) + u ^ (2 * (k + m))) * |u| ^ 0 *
        (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))) := by
  have h2k := even_pow_nonneg u k
  have h2n := even_pow_nonneg u (k + m)
  rw [abs_mul, abs_of_nonneg (add_nonneg (mul_nonneg hs h2k) h2n),
    abs_of_nonneg (wallW_nonneg _ _ _ _ _), pow_zero, mul_one]
  refine mul_le_mul ?_ (wallW_le hs u) (wallW_nonneg _ _ _ _ _)
    (add_nonneg (mul_nonneg (hs.trans hsS) h2k) h2n)
  have := mul_le_mul_of_nonneg_right hsS h2k
  linarith

/-- `G` is continuous on `[0, ∞)`. -/
theorem wallCross_continuousOn (k m h : ℕ) (hn : 1 ≤ k + m) :
    ContinuousOn (wallCross k m h) (Ici 0) := by
  intro s₀ hs₀
  have hs₀' : (0 : ℝ) ≤ s₀ := hs₀
  have hnhds : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] s₀, 0 ≤ s ∧ s ≤ s₀ + 1 := by
    have h1 : Ici (0 : ℝ) ∈ 𝓝[Ici (0 : ℝ)] s₀ := self_mem_nhdsWithin
    have h2 : Iio (s₀ + 1) ∈ 𝓝[Ici (0 : ℝ)] s₀ :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs1, le_of_lt hs2⟩
  have hnum : ContinuousWithinAt (fun s : ℝ ↦ ∫ u, (s * u ^ (2 * k) + u ^ (2 * (k + m))) *
      wallW k m h s u) (Ici 0) s₀ := by
    refine continuousWithinAt_of_dominated
      (bound := fun u ↦ ((s₀ + 1) * u ^ (2 * k) + u ^ (2 * (k + m))) * |u| ^ 0 *
        (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))))
      (Filter.Eventually.of_forall fun s ↦ by unfold wallW; fun_prop) ?_
      (integrable_wall_dom k m h 0 hn (s₀ + 1))
      (Filter.Eventually.of_forall fun u ↦ by unfold wallW; fun_prop)
    filter_upwards [hnhds] with s hs
    exact Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]
      exact abs_wall_num_le hs.1 hs.2
  have hden : ContinuousWithinAt (fun s : ℝ ↦ ∫ u, wallW k m h s u) (Ici 0) s₀ := by
    have h0 := integrable_abs_pow_mul_exp_neg_mul_pow one_pos (k + m) hn h
    refine continuousWithinAt_of_dominated
      (bound := fun u ↦ |u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m)))))
      (Filter.Eventually.of_forall fun s ↦ by unfold wallW; fun_prop) ?_ h0
      (Filter.Eventually.of_forall fun u ↦ by unfold wallW; fun_prop)
    filter_upwards [hnhds] with s hs
    exact Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (wallW_nonneg _ _ _ _ _)]
      exact wallW_le hs.1 u
  exact hnum.div hden (integral_wallW_pos k m h hn hs₀').ne'

/-- At fixed temperature the chart energy is continuous across the wall. -/
theorem wallEnergy_continuousOn (k m h : ℕ) (hn : 1 ≤ k + m) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun ε ↦ wallEnergy k m h ε t) (Ici 0) := by
  have hpos : 0 < t ^ ((m : ℝ) / (k + m)) := Real.rpow_pos_of_pos ht _
  have hmaps : MapsTo (fun ε : ℝ ↦ ε * t ^ ((m : ℝ) / (k + m))) (Ici 0) (Ici 0) :=
    fun ε hε ↦ mul_nonneg hε hpos.le
  have hcomp := (wallCross_continuousOn k m h hn).comp
    (continuous_id.mul continuous_const).continuousOn hmaps
  refine hcomp.congr fun ε _ ↦ ?_
  exact wallEnergy_eq_wallCross k m h hn ε ht

/-! ### The response for `σ > 0` -/

/-- Expectation under the wall density. -/
noncomputable def wallExp (k m h : ℕ) (s : ℝ) (g : ℝ → ℝ) : ℝ :=
  (∫ u, g u * wallW k m h s u) / ∫ u, wallW k m h s u

noncomputable def wallCov (k m h : ℕ) (s : ℝ) (f g : ℝ → ℝ) : ℝ :=
  wallExp k m h s (fun u ↦ f u * g u) - wallExp k m h s f * wallExp k m h s g

theorem hasDerivAt_wallW (k m h : ℕ) (s u : ℝ) :
    HasDerivAt (fun v ↦ wallW k m h v u) (-(u ^ (2 * k)) * wallW k m h s u) s := by
  have h1 : HasDerivAt (fun v ↦ -(v * u ^ (2 * k) + u ^ (2 * (k + m)))) (-(u ^ (2 * k))) s := by
    refine ((((hasDerivAt_id s).mul_const (u ^ (2 * k))).add_const
      (u ^ (2 * (k + m)))).neg).congr_deriv ?_
    simp
  have h2 := h1.exp.const_mul (|u| ^ h)
  refine h2.congr_deriv ?_
  simp only [wallW]
  ring

/-- Integrability of `|u|^j · (energy) · wallW` and of `|u|^j · wallW` for `s ≥ 0`. -/
theorem integrable_energy_mul_wallW (k m h j : ℕ) (hn : 1 ≤ k + m) {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun u ↦ (s * u ^ (2 * k) + u ^ (2 * (k + m))) * |u| ^ j * wallW k m h s u := by
  refine (integrable_wall_dom k m h j hn s).mono' (by unfold wallW; fun_prop)
    (Filter.Eventually.of_forall fun u ↦ ?_)
  have h2k := even_pow_nonneg u k
  have h2n := even_pow_nonneg u (k + m)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg hs h2k) h2n)
    (pow_nonneg (abs_nonneg _) _)) (wallW_nonneg _ _ _ _ _))]
  exact mul_le_mul_of_nonneg_left (wallW_le hs u)
    (mul_nonneg (add_nonneg (mul_nonneg hs h2k) h2n) (pow_nonneg (abs_nonneg _) _))

theorem integrable_pow_mul_wallW' (k m h : ℕ) (hn : 1 ≤ k + m) {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    Integrable fun u ↦ u ^ (2 * j) * wallW k m h s u := by
  have := integrable_abs_pow_mul_wallW k m h (2 * j) hn hs
  refine this.congr (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only
  rw [abs_pow_even]

/-- `G'(σ) = E_σ[u^{2k}] − Cov_σ(σ u^{2k} + u^{2(k+m)}, u^{2k})` for `σ > 0`. -/
theorem hasDerivAt_wallCross (k m h : ℕ) (hn : 1 ≤ k + m) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (wallCross k m h)
      (wallExp k m h s (fun u ↦ u ^ (2 * k)) -
        wallCov k m h s (fun u ↦ s * u ^ (2 * k) + u ^ (2 * (k + m))) (fun u ↦ u ^ (2 * k))) s := by
  have hball : Metric.ball s (s / 2) ∈ 𝓝 s := Metric.ball_mem_nhds s (half_pos hs)
  have hin : ∀ s' ∈ Metric.ball s (s / 2), 0 ≤ s' ∧ s' ≤ 2 * s := by
    intro s' hs'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs'
    constructor <;> linarith [hs'.1, hs'.2]
  have hi0 := integrable_abs_pow_mul_wallW k m h 0 hn hs.le
  simp only [pow_zero, one_mul] at hi0
  have hi2k := integrable_pow_mul_wallW' k m h hn hs.le k
  have hiE := integrable_energy_mul_wallW k m h 0 hn hs.le
  simp only [pow_zero, mul_one] at hiE
  have hiE2k : Integrable fun u ↦ (s * u ^ (2 * k) + u ^ (2 * (k + m))) * u ^ (2 * k) *
      wallW k m h s u := by
    have := integrable_energy_mul_wallW k m h (2 * k) hn hs.le
    refine this.congr (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only
    rw [abs_pow_even]
  -- the denominator
  have hD : HasDerivAt (fun s ↦ ∫ u, wallW k m h s u) (-∫ u, u ^ (2 * k) * wallW k m h s u) s := by
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
      (F := fun s u ↦ wallW k m h s u) (F' := fun s u ↦ -(u ^ (2 * k)) * wallW k m h s u)
      (x₀ := s) (bound := fun u ↦ (1 * u ^ (2 * k) + u ^ (2 * (k + m))) * |u| ^ 0 *
        (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))))
      hball (Filter.Eventually.of_forall fun s ↦ by unfold wallW; fun_prop) hi0
      (by unfold wallW; fun_prop)
      (Filter.Eventually.of_forall fun u s' hs' ↦ by
        obtain ⟨h0, -⟩ := hin s' hs'
        have h2k := even_pow_nonneg u k
        have h2n := even_pow_nonneg u (k + m)
        rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg h2k,
          abs_of_nonneg (wallW_nonneg _ _ _ _ _), pow_zero, mul_one, one_mul]
        exact mul_le_mul (by linarith) (wallW_le h0 u) (wallW_nonneg _ _ _ _ _) (by linarith))
      (integrable_wall_dom k m h 0 hn 1)
      (Filter.Eventually.of_forall fun u s' _ ↦ hasDerivAt_wallW k m h s' u)
    have := key.2
    rw [← integral_neg]
    refine this.congr_deriv ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    beta_reduce
    ring
  -- the numerator
  have hN : HasDerivAt (fun s ↦ ∫ u, (s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u)
      ((∫ u, u ^ (2 * k) * wallW k m h s u) -
        ∫ u, (s * u ^ (2 * k) + u ^ (2 * (k + m))) * u ^ (2 * k) * wallW k m h s u) s := by
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
      (F := fun s u ↦ (s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u)
      (F' := fun s u ↦ u ^ (2 * k) * wallW k m h s u -
        (s * u ^ (2 * k) + u ^ (2 * (k + m))) * u ^ (2 * k) * wallW k m h s u)
      (x₀ := s) (bound := fun u ↦ (1 * u ^ (2 * k) + u ^ (2 * (k + m))) * |u| ^ 0 *
          (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))) +
        (2 * s * u ^ (2 * k) + u ^ (2 * (k + m))) * |u| ^ (2 * k) *
          (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))))
      hball (Filter.Eventually.of_forall fun s ↦ by unfold wallW; fun_prop) hiE
      (by unfold wallW; fun_prop)
      (Filter.Eventually.of_forall fun u s' hs' ↦ by
        obtain ⟨h0, h2⟩ := hin s' hs'
        have h2k := even_pow_nonneg u k
        have h2n := even_pow_nonneg u (k + m)
        have hW := wallW_le (k := k) (m := m) (h := h) h0 u
        have hW0 := wallW_nonneg k m h s' u
        have hE : 0 ≤ s' * u ^ (2 * k) + u ^ (2 * (k + m)) := add_nonneg (mul_nonneg h0 h2k) h2n
        have hE2 : s' * u ^ (2 * k) + u ^ (2 * (k + m)) ≤
            2 * s * u ^ (2 * k) + u ^ (2 * (k + m)) := by
          have := mul_le_mul_of_nonneg_right h2 h2k
          linarith
        rw [Real.norm_eq_abs]
        have hb1 : |u ^ (2 * k) * wallW k m h s' u| ≤ (1 * u ^ (2 * k) + u ^ (2 * (k + m))) *
            |u| ^ 0 * (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))) := by
          rw [abs_of_nonneg (mul_nonneg h2k hW0), pow_zero, mul_one, one_mul]
          exact mul_le_mul (by linarith) hW hW0 (by linarith)
        have hb2 : |(s' * u ^ (2 * k) + u ^ (2 * (k + m))) * u ^ (2 * k) * wallW k m h s' u| ≤
            (2 * s * u ^ (2 * k) + u ^ (2 * (k + m))) * |u| ^ (2 * k) *
              (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))) := by
          rw [abs_of_nonneg (mul_nonneg (mul_nonneg hE h2k) hW0), abs_pow_even]
          exact mul_le_mul (mul_le_mul hE2 le_rfl h2k (by linarith)) hW hW0
            (mul_nonneg (by linarith) h2k)
        exact (abs_sub _ _).trans (add_le_add hb1 hb2))
      ((integrable_wall_dom k m h 0 hn 1).add (integrable_wall_dom k m h (2 * k) hn (2 * s)))
      (Filter.Eventually.of_forall fun u s' _ ↦ by
        have h1 : HasDerivAt (fun v ↦ v * u ^ (2 * k) + u ^ (2 * (k + m))) (u ^ (2 * k)) s' := by
          have := ((hasDerivAt_id s').mul_const (u ^ (2 * k))).add_const (u ^ (2 * (k + m)))
          simpa using this
        have := h1.mul (hasDerivAt_wallW k m h s' u)
        refine this.congr_deriv ?_
        ring)
    have := key.2
    rw [← integral_sub hi2k hiE2k]
    exact this
  have hD0 := (integral_wallW_pos k m h hn hs.le).ne'
  have hq : HasDerivAt (fun s ↦ (∫ u, (s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u) /
      ∫ u, wallW k m h s u) _ s := hN.div hD hD0
  have hfun : (fun s ↦ (∫ u, (s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u) /
      ∫ u, wallW k m h s u) = wallCross k m h := by
    funext s
    rfl
  rw [hfun] at hq
  refine hq.congr_deriv ?_
  unfold wallCov wallExp
  field_simp
  ring

/-- **The response of the chart energy to the wall parameter collapses**:
`∂_ε (t E_{ε,t}[L_ε]) = t^{m/(k+m)} · G'(ε t^{m/(k+m)})` for `ε > 0`. -/
theorem hasDerivAt_wallEnergy (k m h : ℕ) (hn : 1 ≤ k + m) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    HasDerivAt (fun ε ↦ wallEnergy k m h ε t)
      (t ^ ((m : ℝ) / (k + m)) *
        (wallExp k m h (ε * t ^ ((m : ℝ) / (k + m))) (fun u ↦ u ^ (2 * k)) -
          wallCov k m h (ε * t ^ ((m : ℝ) / (k + m)))
            (fun u ↦ ε * t ^ ((m : ℝ) / (k + m)) * u ^ (2 * k) + u ^ (2 * (k + m)))
            (fun u ↦ u ^ (2 * k)))) ε := by
  have hpos : 0 < t ^ ((m : ℝ) / (k + m)) := Real.rpow_pos_of_pos ht _
  have hfun : (fun ε ↦ wallEnergy k m h ε t) =
      fun ε ↦ wallCross k m h (ε * t ^ ((m : ℝ) / (k + m))) := by
    funext ε
    exact wallEnergy_eq_wallCross k m h hn ε ht
  rw [hfun]
  have hin : HasDerivAt (fun ε : ℝ ↦ ε * t ^ ((m : ℝ) / (k + m))) (t ^ ((m : ℝ) / (k + m))) ε := by
    simpa using (hasDerivAt_id ε).mul_const (t ^ ((m : ℝ) / (k + m)))
  have := (hasDerivAt_wallCross k m h hn (mul_pos hε hpos)).comp ε hin
  refine this.congr_deriv ?_
  ring

end Laplace.Multi
