/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.SingularPowerNormalForm
import Laplace.Multi.MorseBottLeading

/-!
# A toy phase transition: `L_u = x⁴ + u²x²`

Astra's warning example (`research_truth_variation_v1`, Q4/D) for why the smooth fixed-temperature
theory of `TruthVariation` does not extend uniformly across singularity strata. On the line with
flat prior, the energy observable of `L_u(x) = x⁴ + u²x²` is exactly a function of the crossover
variable `s = u²√t` (`energy_eq_crossover`):
`t E_{u,t}[L_u] = G(u²√t)`, `G(s) = ∫ (y⁴ + sy²) e^{-y⁴-sy²} / ∫ e^{-y⁴-sy²}`.
`G` is continuous on `[0, ∞)` (`crossover_continuousOn`), `G(0) = 1/4` (`crossover_zero`) and
`G(s) → 1/2` as `s → ∞` (`tendsto_crossover_atTop`, after `y = z/√s` the Gaussian dominates).
Hence (`energy_continuous`, `tendsto_energy_zero`, `tendsto_energy_ne_zero`): at every
fixed temperature
`u ↦ t E_{u,t}[L_u]` is continuous, while its low-temperature limit is `1/2` for `u ≠ 0` and
`1/4` at `u = 0` — the RLCT `λ(u)`, a discontinuous function of the truth. The real RLCT has no
semicontinuity direction in general; here the special fibre is the more singular one.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### The crossover function -/

/-- `G(s) = ∫ (y⁴ + s y²) e^{-(y⁴ + s y²)} dy / ∫ e^{-(y⁴ + s y²)} dy`. -/
noncomputable def crossover (s : ℝ) : ℝ :=
  (∫ y : ℝ, (y ^ 4 + s * y ^ 2) * Real.exp (-(y ^ 4 + s * y ^ 2))) /
    ∫ y : ℝ, Real.exp (-(y ^ 4 + s * y ^ 2))

theorem integrable_pow_mul_exp_neg_quartic (m : ℕ) :
    Integrable fun y : ℝ ↦ y ^ m * Real.exp (-(y ^ 4)) := by
  have := integrable_pow_mul_exp_neg_mul_pow one_pos 2 (by norm_num) m
  simpa using this

/-- The dominating function `(y⁴ + S y²) e^{-y⁴}`. -/
theorem integrable_dom (S : ℝ) :
    Integrable fun y : ℝ ↦ (y ^ 4 + S * y ^ 2) * Real.exp (-(y ^ 4)) := by
  have h4 := integrable_pow_mul_exp_neg_quartic 4
  have h2 := (integrable_pow_mul_exp_neg_quartic 2).const_mul S
  refine (h4.add h2).congr (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.add_apply]
  ring

theorem exp_neg_quartic_le {s y : ℝ} (hs : 0 ≤ s) :
    Real.exp (-(y ^ 4 + s * y ^ 2)) ≤ Real.exp (-(y ^ 4)) := by
  apply Real.exp_le_exp.mpr
  have : 0 ≤ s * y ^ 2 := by positivity
  linarith

theorem abs_num_le {s S y : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S) :
    |(y ^ 4 + s * y ^ 2) * Real.exp (-(y ^ 4 + s * y ^ 2))| ≤
      (y ^ 4 + S * y ^ 2) * Real.exp (-(y ^ 4)) := by
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy4 : 0 ≤ y ^ 4 := by positivity
  rw [abs_mul, Real.abs_exp, abs_of_nonneg (add_nonneg hy4 (mul_nonneg hs hy2))]
  exact mul_le_mul (by nlinarith) (exp_neg_quartic_le hs) (Real.exp_pos _).le
    (add_nonneg hy4 (mul_nonneg (hs.trans hsS) hy2))

theorem integrable_crossover_num {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun y : ℝ ↦ (y ^ 4 + s * y ^ 2) * Real.exp (-(y ^ 4 + s * y ^ 2)) :=
  (integrable_dom s).mono' (by fun_prop) (Filter.Eventually.of_forall fun y ↦ by
    rw [Real.norm_eq_abs]
    exact abs_num_le hs le_rfl)

theorem integrable_crossover_den {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun y : ℝ ↦ Real.exp (-(y ^ 4 + s * y ^ 2)) := by
  have h0 := integrable_pow_mul_exp_neg_quartic 0
  simp only [pow_zero, one_mul] at h0
  refine h0.mono' (by fun_prop) (Filter.Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, Real.abs_exp]
  exact exp_neg_quartic_le hs

theorem crossover_den_pos {s : ℝ} (hs : 0 ≤ s) :
    0 < ∫ y : ℝ, Real.exp (-(y ^ 4 + s * y ^ 2)) := by
  refine (integral_pos_iff_support_of_nonneg (fun y ↦ (Real.exp_pos _).le)
    (integrable_crossover_den hs)).mpr ?_
  have : Function.support (fun y : ℝ ↦ Real.exp (-(y ^ 4 + s * y ^ 2))) = Set.univ := by
    ext y
    simp [(Real.exp_pos _).ne']
  rw [this]
  simp

/-- `G(0) = 1/4`: the RLCT of `x⁴`. -/
theorem crossover_zero : crossover 0 = 1 / 4 := by
  have h := gmom_two_k_div_zero 2 (by norm_num)
  unfold gmom at h
  unfold crossover
  norm_num at h ⊢
  exact h

/-- `G` is continuous on `[0, ∞)`. -/
theorem crossover_continuousOn : ContinuousOn crossover (Ici 0) := by
  intro s₀ hs₀
  have hs₀' : (0 : ℝ) ≤ s₀ := hs₀
  have hnhds : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] s₀, 0 ≤ s ∧ s ≤ s₀ + 1 := by
    have h1 : Ici (0 : ℝ) ∈ 𝓝[Ici (0 : ℝ)] s₀ := self_mem_nhdsWithin
    have h2 : Iio (s₀ + 1) ∈ 𝓝[Ici (0 : ℝ)] s₀ :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs1, le_of_lt hs2⟩
  have hnum : ContinuousWithinAt (fun s : ℝ ↦ ∫ y : ℝ, (y ^ 4 + s * y ^ 2) *
      Real.exp (-(y ^ 4 + s * y ^ 2))) (Ici 0) s₀ := by
    refine continuousWithinAt_of_dominated
      (bound := fun y ↦ (y ^ 4 + (s₀ + 1) * y ^ 2) * Real.exp (-(y ^ 4)))
      (Filter.Eventually.of_forall fun s ↦ by fun_prop) ?_ (integrable_dom _)
      (Filter.Eventually.of_forall fun y ↦ by fun_prop)
    filter_upwards [hnhds] with s hs
    exact Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs]
      exact abs_num_le hs.1 hs.2
  have hden : ContinuousWithinAt (fun s : ℝ ↦ ∫ y : ℝ, Real.exp (-(y ^ 4 + s * y ^ 2)))
      (Ici 0) s₀ := by
    have h0 := integrable_pow_mul_exp_neg_quartic 0
    simp only [pow_zero, one_mul] at h0
    refine continuousWithinAt_of_dominated (bound := fun y ↦ Real.exp (-(y ^ 4)))
      (Filter.Eventually.of_forall fun s ↦ by fun_prop) ?_ h0
      (Filter.Eventually.of_forall fun y ↦ by fun_prop)
    filter_upwards [hnhds] with s hs
    exact Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact exp_neg_quartic_le hs.1
  exact hnum.div hden (crossover_den_pos hs₀').ne'

/-! ### The Gaussian limit `G(s) → 1/2` -/

/-- After `y = z/√s`: `G(s) = ∫ (z⁴/s² + z²) e^{-z⁴/s² - z²} / ∫ e^{-z⁴/s² - z²}`. -/
theorem crossover_eq_rescaled {s : ℝ} (hs : 0 < s) :
    crossover s =
      (∫ z : ℝ, (z ^ 4 / s ^ 2 + z ^ 2) * Real.exp (-(z ^ 4 / s ^ 2 + z ^ 2))) /
        ∫ z : ℝ, Real.exp (-(z ^ 4 / s ^ 2 + z ^ 2)) := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hr2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hr4 : Real.sqrt s ^ 4 = s ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hr2]
  -- numerator
  have hn := Measure.integral_comp_mul_left
    (fun y : ℝ ↦ (y ^ 4 + s * y ^ 2) * Real.exp (-(y ^ 4 + s * y ^ 2))) (Real.sqrt s)⁻¹
  have hd := Measure.integral_comp_mul_left
    (fun y : ℝ ↦ Real.exp (-(y ^ 4 + s * y ^ 2))) (Real.sqrt s)⁻¹
  simp only [inv_inv, abs_of_pos hr, smul_eq_mul] at hn hd
  have hpt1 : ∀ z : ℝ, ((Real.sqrt s)⁻¹ * z) ^ 4 + s * ((Real.sqrt s)⁻¹ * z) ^ 2 =
      z ^ 4 / s ^ 2 + z ^ 2 := by
    intro z
    rw [mul_pow, mul_pow, inv_pow, inv_pow, hr2, hr4]
    field_simp
  simp only [hpt1] at hn hd
  unfold crossover
  rw [hn, hd, mul_div_mul_left _ _ hr.ne']

/-- `G(s) → 1/2` as `s → ∞`: the Gaussian second moment. -/
theorem tendsto_crossover_atTop : Tendsto crossover atTop (𝓝 (1 / 2)) := by
  -- the limit is `∫ z² e^{-z²} / ∫ e^{-z²} = 1/2`
  have hlim : (∫ z : ℝ, z ^ 2 * Real.exp (-(z ^ 2))) / (∫ z : ℝ, Real.exp (-(z ^ 2))) = 1 / 2 := by
    have h := gmom_two_k_div_zero 1 le_rfl
    unfold gmom at h
    norm_num at h ⊢
    exact h
  have hG2 := integrable_pow_mul_exp_neg_mul_pow one_pos 1 le_rfl 2
  have hG4 := integrable_pow_mul_exp_neg_mul_pow one_pos 1 le_rfl 4
  have hG0 := integrable_pow_mul_exp_neg_mul_pow one_pos 1 le_rfl 0
  simp only [mul_one, one_mul, pow_zero] at hG2 hG4 hG0
  -- pointwise bounds for `s ≥ 1`
  have hbound : ∀ s : ℝ, 1 ≤ s → ∀ z : ℝ,
      |(z ^ 4 / s ^ 2 + z ^ 2) * Real.exp (-(z ^ 4 / s ^ 2 + z ^ 2))| ≤
        (z ^ 4 + z ^ 2) * Real.exp (-(z ^ 2)) := by
    intro s hs z
    have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
    have hz4 : 0 ≤ z ^ 4 := by positivity
    have hdiv : z ^ 4 / s ^ 2 ≤ z ^ 4 := div_le_self hz4 hs2
    have hdiv0 : 0 ≤ z ^ 4 / s ^ 2 := by positivity
    rw [abs_mul, Real.abs_exp, abs_of_nonneg (by positivity)]
    refine mul_le_mul (by nlinarith) ?_ (Real.exp_pos _).le (by positivity)
    exact Real.exp_le_exp.mpr (by linarith)
  have hbound0 : ∀ s : ℝ, 1 ≤ s → ∀ z : ℝ,
      |Real.exp (-(z ^ 4 / s ^ 2 + z ^ 2))| ≤ Real.exp (-(z ^ 2)) := by
    intro s hs z
    rw [Real.abs_exp]
    have : 0 ≤ z ^ 4 / s ^ 2 := by positivity
    exact Real.exp_le_exp.mpr (by linarith)
  have hdom : Integrable fun z : ℝ ↦ (z ^ 4 + z ^ 2) * Real.exp (-(z ^ 2)) := by
    refine (hG4.add hG2).congr (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [Pi.add_apply]
    ring
  -- `1/s² → 0`
  have hinv : Tendsto (fun s : ℝ ↦ s ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hinv' : Tendsto (fun s : ℝ ↦ (s ^ 2)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hinv
  have hnum : Tendsto (fun s : ℝ ↦ ∫ z : ℝ, (z ^ 4 / s ^ 2 + z ^ 2) *
      Real.exp (-(z ^ 4 / s ^ 2 + z ^ 2))) atTop (𝓝 (∫ z : ℝ, z ^ 2 * Real.exp (-(z ^ 2)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z ↦ (z ^ 4 + z ^ 2) * Real.exp (-(z ^ 2)))
      (Filter.Eventually.of_forall fun s ↦ by fun_prop) ?_ hdom
      (Filter.Eventually.of_forall fun z ↦ ?_)
    · filter_upwards [eventually_ge_atTop 1] with s hs
      exact Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs]
        exact hbound s hs z
    · have h1 : Tendsto (fun s : ℝ ↦ z ^ 4 / s ^ 2 + z ^ 2) atTop (𝓝 (0 + z ^ 2)) := by
        have := (hinv'.const_mul (z ^ 4)).add (tendsto_const_nhds (x := z ^ 2))
        simpa [div_eq_mul_inv] using this
      rw [zero_add] at h1
      exact h1.mul ((Real.continuous_exp.tendsto _).comp h1.neg)
  have hden : Tendsto (fun s : ℝ ↦ ∫ z : ℝ, Real.exp (-(z ^ 4 / s ^ 2 + z ^ 2))) atTop
      (𝓝 (∫ z : ℝ, Real.exp (-(z ^ 2)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z ↦ Real.exp (-(z ^ 2)))
      (Filter.Eventually.of_forall fun s ↦ by fun_prop) ?_ hG0
      (Filter.Eventually.of_forall fun z ↦ ?_)
    · filter_upwards [eventually_ge_atTop 1] with s hs
      exact Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs]
        exact hbound0 s hs z
    · have h1 : Tendsto (fun s : ℝ ↦ z ^ 4 / s ^ 2 + z ^ 2) atTop (𝓝 (0 + z ^ 2)) := by
        have := (hinv'.const_mul (z ^ 4)).add (tendsto_const_nhds (x := z ^ 2))
        simpa [div_eq_mul_inv] using this
      rw [zero_add] at h1
      exact (Real.continuous_exp.tendsto _).comp h1.neg
  have hden0 : (∫ z : ℝ, Real.exp (-(z ^ 2))) ≠ 0 := by
    refine ((integral_pos_iff_support_of_nonneg (fun z ↦ (Real.exp_pos _).le) hG0).mpr ?_).ne'
    have : Function.support (fun z : ℝ ↦ Real.exp (-(z ^ 2))) = Set.univ := by
      ext z
      simp [(Real.exp_pos _).ne']
    rw [this]
    simp
  have := hnum.div hden hden0
  rw [hlim] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [Pi.div_apply]
  rw [crossover_eq_rescaled hs]

/-! ### The energy observable of `L_u = x⁴ + u²x²` -/

/-- `L_u(x) = x⁴ + u² x²`. -/
noncomputable def toyLoss (u x : ℝ) : ℝ := x ^ 4 + u ^ 2 * x ^ 2

/-- The energy observable `t E_{u,t}[L_u]` with flat prior on the line. -/
noncomputable def toyEnergy (u t : ℝ) : ℝ :=
  t * ((∫ x : ℝ, toyLoss u x * Real.exp (-(t * toyLoss u x))) /
    ∫ x : ℝ, Real.exp (-(t * toyLoss u x)))

/-- **The exact crossover**: `t E_{u,t}[L_u] = G(u² √t)`. -/
theorem energy_eq_crossover (u : ℝ) {t : ℝ} (ht : 0 < t) :
    toyEnergy u t = crossover (u ^ 2 * Real.sqrt t) := by
  -- substitute `x = y / t^{1/4}`, with `t^{1/4} = √√t`
  set a : ℝ := Real.sqrt (Real.sqrt t) with ha
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hapos : 0 < a := Real.sqrt_pos.mpr hst
  have ha2 : a ^ 2 = Real.sqrt t := Real.sq_sqrt hst.le
  have ha4 : a ^ 4 = t := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, ha2, Real.sq_sqrt ht.le]
  have hn := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ toyLoss u x * Real.exp (-(t * toyLoss u x))) a⁻¹
  have hd := Measure.integral_comp_mul_left (fun x : ℝ ↦ Real.exp (-(t * toyLoss u x))) a⁻¹
  simp only [inv_inv, abs_of_pos hapos, smul_eq_mul] at hn hd
  have hpt : ∀ y : ℝ, t * toyLoss u (a⁻¹ * y) = y ^ 4 + u ^ 2 * Real.sqrt t * y ^ 2 := by
    intro y
    unfold toyLoss
    rw [mul_pow, mul_pow, inv_pow, inv_pow, ha2, ha4]
    field_simp
    have h2 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    linear_combination (-(y ^ 2 * u ^ 2)) * h2
  simp only [hpt] at hn hd
  have hn' : (∫ y : ℝ, toyLoss u y * Real.exp (-(t * toyLoss u y))) =
      a⁻¹ * ∫ x : ℝ, toyLoss u (a⁻¹ * x) * Real.exp (-(x ^ 4 + u ^ 2 * Real.sqrt t * x ^ 2)) := by
    rw [hn, ← mul_assoc, inv_mul_cancel₀ hapos.ne', one_mul]
  have hd' : (∫ y : ℝ, Real.exp (-(t * toyLoss u y))) =
      a⁻¹ * ∫ x : ℝ, Real.exp (-(x ^ 4 + u ^ 2 * Real.sqrt t * x ^ 2)) := by
    rw [hd, ← mul_assoc, inv_mul_cancel₀ hapos.ne', one_mul]
  unfold toyEnergy crossover
  rw [hn', hd', mul_div_mul_left _ _ (inv_ne_zero hapos.ne'), ← mul_div_assoc,
    ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only
  rw [← mul_assoc, hpt y]

/-- **At every fixed temperature the energy is continuous in the truth parameter `u`.** -/
theorem energy_continuous {t : ℝ} (ht : 0 < t) : Continuous fun u ↦ toyEnergy u t := by
  have heq : (fun u ↦ toyEnergy u t) = fun u ↦ crossover (u ^ 2 * Real.sqrt t) := by
    funext u
    exact energy_eq_crossover u ht
  rw [heq]
  exact crossover_continuousOn.comp_continuous (by fun_prop) fun u ↦ by
    simp only [mem_Ici]
    positivity

/-- **At `u = 0` the low-temperature limit is `1/4`** (in fact `t E[L_0] = 1/4` exactly). -/
theorem tendsto_energy_zero : Tendsto (fun t ↦ toyEnergy 0 t) atTop (𝓝 (1 / 4)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [energy_eq_crossover 0 ht]
  simp [crossover_zero]

/-- **For `u ≠ 0` the low-temperature limit is `1/2`**: the RLCT jumps from `1/4` to `1/2`. -/
theorem tendsto_energy_ne_zero {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun t ↦ toyEnergy u t) atTop (𝓝 (1 / 2)) := by
  have hs : Tendsto (fun t : ℝ ↦ u ^ 2 * Real.sqrt t) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) tendsto_sqrt_atTop'
  have := tendsto_crossover_atTop.comp hs
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp]
  rw [energy_eq_crossover u ht]

end Laplace.Multi
