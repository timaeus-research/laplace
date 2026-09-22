/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.WallCutoff
import Laplace.Multi.TruthVariation

/-!
# What empirical, rescaled observables see across a wall

Take the wall chart `L_ε(x) = (ε + x^{2m}) x^{2k}` with Jacobian weight `|x|^h`, a compact prior
`χ`, and a bounded continuous test read at the resolution of the wall, `x ↦ g(t^{1/2(k+m)} x)`.

* Along the wall path `ε(t) = σ t^{-m/(k+m)}` the population expectation of the rescaled test
  converges to its wall-density expectation `E_σ[g] = ∫ g · wallW σ / ∫ wallW σ`
  (`tendsto_wallExpCutoff`): the crossover of a rescaled observable is `σ ↦ E_σ[g]`.
* The empirical posterior, formed with `L_ε + R` for a residual `|R| ≤ M`, differs from the
  population one by at most `2 t M ‖g‖` on bounded tests (`abs_empirical_sub_population_le`, from
  the tilt interpolation of S3).
* Hence along a schedule `t_n → ∞` with `t_n M_n → 0` the EMPIRICAL rescaled expectation converges
  to `E_σ[g]` (`tendsto_empirical_wall`): the wall is seen at finite `n`, with its crossover shape,
  exactly on the schedules of S6, and it is invisible to a rescaled test whose wall-density
  expectation is constant in `σ`.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The substitution `x = t^{-1/2(k+m)} u` along the wall path, with a rescaled test factor. -/
theorem rpow_mul_wall_integral_eq' (χ g : ℝ → ℝ) (k m h : ℕ) (hn : 1 ≤ k + m) (σ : ℝ) {t : ℝ}
    (ht : 0 < t) (F : ℝ → ℝ) :
    t ^ (((h : ℝ) + 1) / (2 * (k + m))) *
      ∫ x, g (t ^ (1 / (2 * ((k : ℝ) + m))) * x) * (χ x * |x| ^ h *
        F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k)))) =
      ∫ u, g u * (χ (t ^ (-(1 / (2 * ((k : ℝ) + m)))) * u) * |u| ^ h *
        F (σ * u ^ (2 * k) + u ^ (2 * (k + m)))) := by
  have hn' : (0 : ℝ) < (k : ℝ) + m := by exact_mod_cast hn
  set c : ℝ := t ^ (-(1 / (2 * ((k : ℝ) + m)))) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hcinv : t ^ (1 / (2 * ((k : ℝ) + m))) * c = 1 := by
    rw [hc, ← Real.rpow_add ht]
    simp
  have hc2n : t * c ^ (2 * (k + m)) = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    rw [show -(1 / (2 * ((k : ℝ) + m))) * (2 * (k + m)) = -1 by field_simp, Real.rpow_neg_one,
      mul_inv_cancel₀ ht.ne']
  have hc2k : t * (t ^ (-((m : ℝ) / (k + m))) * c ^ (2 * k)) = 1 := by
    have h1 := Real.rpow_add ht 1 (-((m : ℝ) / (k + m)))
    rw [Real.rpow_one] at h1
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← mul_assoc, ← h1, ← Real.rpow_add ht]
    push_cast
    rw [show (1 : ℝ) + -((m : ℝ) / (k + m)) + -(1 / (2 * ((k : ℝ) + m))) * (2 * k) = 0 by
      field_simp; ring, Real.rpow_zero]
  have hch : t ^ (((h : ℝ) + 1) / (2 * (k + m))) * c ^ (h + 1) = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    push_cast
    rw [show ((h : ℝ) + 1) / (2 * (k + m)) + -(1 / (2 * ((k : ℝ) + m))) * ((h : ℝ) + 1) = 0 by
      ring, Real.rpow_zero]
  have hpt : ∀ u : ℝ, t * ((wallPath k m σ t + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k)) =
      σ * u ^ (2 * k) + u ^ (2 * (k + m)) := by
    intro u
    have : t * ((wallPath k m σ t + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k)) =
        σ * (t * (t ^ (-((m : ℝ) / (k + m))) * c ^ (2 * k))) * u ^ (2 * k) +
          (t * c ^ (2 * (k + m))) * u ^ (2 * (k + m)) := by
      unfold wallPath
      ring
    rw [this, hc2k, hc2n, one_mul, mul_one]
  have hg : ∀ u : ℝ, t ^ (1 / (2 * ((k : ℝ) + m))) * (c * u) = u := by
    intro u
    rw [← mul_assoc, hcinv, one_mul]
  have hcomp := Measure.integral_comp_mul_left (fun x : ℝ ↦ g (t ^ (1 / (2 * ((k : ℝ) + m))) * x) *
    (χ x * |x| ^ h * F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k))))) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hcomp
  have hpt' : ∀ u : ℝ, g (t ^ (1 / (2 * ((k : ℝ) + m))) * (c * u)) * (χ (c * u) * |c * u| ^ h *
      F (t * ((wallPath k m σ t + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k)))) =
      c ^ h * (g u * (χ (c * u) * |u| ^ h * F (σ * u ^ (2 * k) + u ^ (2 * (k + m))))) := by
    intro u
    rw [hpt, hg, abs_mul, abs_of_pos hcpos, mul_pow]
    ring
  simp only [hpt', integral_const_mul] at hcomp
  have hI : (∫ x, g (t ^ (1 / (2 * ((k : ℝ) + m))) * x) *
      (χ x * |x| ^ h * F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k))))) =
      c ^ (h + 1) * ∫ u, g u * (χ (c * u) * |u| ^ h * F (σ * u ^ (2 * k) + u ^ (2 * (k + m)))) := by
    have hF : (∫ x, g (t ^ (1 / (2 * ((k : ℝ) + m))) * x) *
        (χ x * |x| ^ h * F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k))))) =
        c * (c⁻¹ * ∫ x, g (t ^ (1 / (2 * ((k : ℝ) + m))) * x) *
          (χ x * |x| ^ h * F (t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k))))) := by
      rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
    rw [hF, ← hcomp, pow_succ]
    ring
  rw [hI, ← mul_assoc, hch, one_mul]

/-- The population expectation of the rescaled test `g(t^{1/2(k+m)} x)` under the cutoff wall
posterior. -/
noncomputable def wallExpCutoff (χ g : ℝ → ℝ) (k m h : ℕ) (ε t : ℝ) : ℝ :=
  (∫ x, g (t ^ (1 / (2 * ((k : ℝ) + m))) * x) *
      (χ x * |x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k)))))) /
    ∫ x, χ x * |x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k))))

/-- **Along the wall path a rescaled bounded test converges to its wall-density expectation.** -/
theorem tendsto_wallExpCutoff {χ g : ℝ → ℝ} (hχ : Cutoff χ) (hgc : Continuous g) {Mg : ℝ}
    (hg : ∀ u, |g u| ≤ Mg) (k m h : ℕ) (hn : 1 ≤ k + m) {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t ↦ wallExpCutoff χ g k m h (wallPath k m σ t) t) atTop
      (𝓝 (wallExp k m h σ g)) := by
  have hi := integrable_abs_pow_mul_wallW k m h 0 hn hσ
  simp only [pow_zero, one_mul] at hi
  have hgW : Integrable fun u ↦ g u * wallW k m h σ u :=
    hi.bdd_mul (hgc.aestronglyMeasurable) (Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]; exact hg u)
  have hN := tendsto_wall_cutoff hχ k m hn (W := fun u ↦ g u * wallW k m h σ u)
    (by unfold wallW; fun_prop) hgW
  have hD := tendsto_rpow_mul_wallCutoff_den hχ k m h hn hσ
  have hD0 : χ 0 * ∫ u, wallW k m h σ u ≠ 0 :=
    (mul_pos hχ.pos (integral_wallW_pos k m h hn hσ)).ne'
  have := hN.div hD hD0
  unfold wallExp
  rw [mul_div_mul_left _ _ hχ.pos.ne'] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Pi.div_apply]
  have hnum := rpow_mul_wall_integral_eq' χ g k m h hn σ ht (fun y ↦ Real.exp (-y))
  have hnum' : (∫ u, χ (t ^ (-(1 / (2 * ((k : ℝ) + m)))) * u) * (g u * wallW k m h σ u)) =
      t ^ (((h : ℝ) + 1) / (2 * (k + m))) * ∫ x, g (t ^ (1 / (2 * ((k : ℝ) + m))) * x) *
        (χ x * |x| ^ h * Real.exp (-(t * ((wallPath k m σ t + x ^ (2 * m)) * x ^ (2 * k))))) := by
    rw [hnum]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [wallW]
    ring
  unfold wallExpCutoff
  rw [hnum', mul_div_mul_left _ _ (Real.rpow_pos_of_pos ht _).ne']

/-! ### The empirical posterior -/

/-- The population weight of the cutoff wall posterior. -/
noncomputable def wallWeight (χ : ℝ → ℝ) (k m h : ℕ) (ε t : ℝ) (x : ℝ) : ℝ :=
  χ x * |x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k))))

theorem wallWeight_nonneg {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m h : ℕ) (ε t x : ℝ) :
    0 ≤ wallWeight χ k m h ε t x :=
  mul_nonneg (mul_nonneg (hχ.nonneg x) (pow_nonneg (abs_nonneg _) _)) (Real.exp_pos _).le

theorem integrable_wallWeight {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m h : ℕ) (ε t : ℝ) :
    Integrable (wallWeight χ k m h ε t) := by
  have hc : Continuous (wallWeight χ k m h ε t) := by
    have := hχ.cont
    unfold wallWeight
    fun_prop
  refine hc.integrable_of_hasCompactSupport ?_
  have : wallWeight χ k m h ε t = fun x ↦ χ x * (|x| ^ h *
      Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k))))) := by
    funext x
    unfold wallWeight
    ring
  rw [this]
  exact hχ.supp.mul_right

theorem integral_wallWeight_pos {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m h : ℕ) (ε t : ℝ) :
    0 < ∫ x, wallWeight χ k m h ε t x := by
  refine (integral_pos_iff_support_of_nonneg (wallWeight_nonneg hχ k m h ε t)
    (integrable_wallWeight hχ k m h ε t)).mpr ?_
  -- the support contains a punctured ball around `0`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hχ.cont.isOpen_support 0 hχ.pos.ne'
  have hsub : Metric.ball (0 : ℝ) r \ {0} ⊆ Function.support (wallWeight χ k m h ε t) := by
    intro x hx
    have hχx : χ x ≠ 0 := hball hx.1
    have hx0 : x ≠ 0 := hx.2
    unfold wallWeight
    exact mul_ne_zero (mul_ne_zero hχx (pow_ne_zero _ (abs_pos.mpr hx0).ne'))
      (Real.exp_pos _).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [measure_sdiff_null (measure_singleton 0)]
  exact Metric.measure_ball_pos volume 0 hr

/-- The population posterior is a `TiltData` weight for any bounded measurable residual. -/
theorem wallWeight_tiltData {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m h : ℕ) (ε t : ℝ) {R : ℝ → ℝ}
    (hRm : Measurable R) {M : ℝ} (hR : ∀ x, |R x| ≤ M) :
    TiltData volume (wallWeight χ k m h ε t) R M where
  ν_meas := by
    have := hχ.cont
    unfold wallWeight
    fun_prop
  ν_int := integrable_wallWeight hχ k m h ε t
  ν_nonneg := wallWeight_nonneg hχ k m h ε t
  ν_pos := integral_wallWeight_pos hχ k m h ε t
  R_meas := hRm
  R_bound := hR

/-- **Empirical versus population**: for a bounded measurable test the two expectations differ by
at most `2 t M ‖f‖` (the tilt interpolation of S3). -/
theorem abs_empirical_sub_population_le {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m h : ℕ) (ε : ℝ) {t : ℝ}
    (ht : 0 ≤ t) {R : ℝ → ℝ} (hRm : Measurable R) {M : ℝ} (hR : ∀ x, |R x| ≤ M) {f : ℝ → ℝ}
    (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) :
    |tiltExp volume (wallWeight χ k m h ε t) f R t 1 -
      tiltExp volume (wallWeight χ k m h ε t) f R t 0| ≤ t * (2 * Mf * M) := by
  have hT := wallWeight_tiltData hχ k m h ε t hRm hR
  exact hT.abs_tiltExp_one_sub_zero_le hfm hf ht
    (fun u _ ↦ hT.abs_tiltCov_le_of_bdd hfm hf hRm hR t u)

/-- The population endpoint is the cutoff rescaled expectation. -/
theorem tiltExp_zero_eq_wallExpCutoff (χ g : ℝ → ℝ) (k m h : ℕ) (ε t : ℝ) (R : ℝ → ℝ) :
    tiltExp volume (wallWeight χ k m h ε t) (fun x ↦ g (t ^ (1 / (2 * ((k : ℝ) + m))) * x)) R t 0 =
      wallExpCutoff χ g k m h ε t := by
  rw [tiltExp_zero]
  rfl

/-- **The empirical wall crossover.** Along a schedule `t_n → ∞` with `t_n M_n → 0`, where `M_n`
bounds the residual `R_n = L_n − L`, the empirical expectation of the rescaled bounded test
`g(t_n^{1/2(k+m)} x)` on the wall path converges to the wall-density expectation `E_σ[g]`. -/
theorem tendsto_empirical_wall {χ g : ℝ → ℝ} (hχ : Cutoff χ) (hgc : Continuous g) {Mg : ℝ}
    (hg : ∀ u, |g u| ≤ Mg) (k m h : ℕ) (hn : 1 ≤ k + m) {σ : ℝ} (hσ : 0 ≤ σ)
    (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (ht : Tendsto t atTop atTop)
    (R : ℕ → ℝ → ℝ) (hRm : ∀ n, Measurable (R n)) (M : ℕ → ℝ) (hR : ∀ n x, |R n x| ≤ M n)
    (htM : Tendsto (fun n ↦ t n * M n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ tiltExp volume (wallWeight χ k m h (wallPath k m σ (t n)) (t n))
      (fun x ↦ g ((t n) ^ (1 / (2 * ((k : ℝ) + m))) * x)) (R n) (t n) 1) atTop
      (𝓝 (wallExp k m h σ g)) := by
  have hpop : Tendsto (fun n ↦ wallExpCutoff χ g k m h (wallPath k m σ (t n)) (t n)) atTop
      (𝓝 (wallExp k m h σ g)) :=
    (tendsto_wallExpCutoff hχ hgc hg k m h hn hσ).comp ht
  have hdiff : Tendsto (fun n ↦ tiltExp volume (wallWeight χ k m h (wallPath k m σ (t n)) (t n))
      (fun x ↦ g ((t n) ^ (1 / (2 * ((k : ℝ) + m))) * x)) (R n) (t n) 1 -
      wallExpCutoff χ g k m h (wallPath k m σ (t n)) (t n)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n ↦ t n * M n * (2 * Mg)) atTop (𝓝 0) := by
      simpa using htM.mul_const (2 * Mg)
    refine squeeze_zero_norm (fun n ↦ ?_) hb
    rw [Real.norm_eq_abs, ← tiltExp_zero_eq_wallExpCutoff χ g k m h _ _ (R n)]
    have := abs_empirical_sub_population_le hχ k m h (wallPath k m σ (t n)) (ht0 n) (hRm n) (hR n)
      (f := fun x ↦ g ((t n) ^ (1 / (2 * ((k : ℝ) + m))) * x))
      (hgc.measurable.comp (measurable_const.mul measurable_id)) (fun x ↦ hg _)
    calc _ ≤ t n * (2 * Mg * M n) := this
      _ = t n * M n * (2 * Mg) := by ring
  have := hdiff.add hpop
  rw [zero_add] at this
  refine this.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  simp only
  ring

end Laplace.Multi
