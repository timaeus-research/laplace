/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ToyCrossover
import Laplace.Multi.RelativeChartLeading

/-!
# The response across a phase transition: the crossover function is smooth, its derivative is a
covariance, and the finite-temperature response collapses onto one curve

For the toy family `L_u(x) = x⁴ + u²x²` the energy observable is `t E_{u,t}[L_u] = G(u²√t)`
(`energy_eq_crossover`). Here:

* `G` is differentiable on all of `ℝ`, with `G'(s) = E_s[y²] − Cov_s(y⁴ + s y², y²)` under the
  crossover density `e^{-(y⁴ + s y²)}` (`hasDerivAt_crossover`): the derivative of the observable
  with respect to the truth parameter is a covariance against the energy, the Level-1 response
  formula evaluated on the rescaled variable;
* the response of the energy to `u` at fixed temperature is
  `∂_u (t E_{u,t}[L_u]) = 2u√t · G'(u²√t)` (`hasDerivAt_toyEnergy`), and for `u ≥ 0` this equals
  `2 t^{1/4} R(u²√t)` with `R(s) = √s · G'(s)` (`toyResponse_collapse`): one fixed shape `R`, of
  amplitude `t^{1/4}` and of width `t^{-1/4}` in `u`. The jump of the RLCT (`1/4` at `u = 0`,
  `1/2` off it) is seen at finite temperature as a susceptibility peak that sharpens like `t^{-1/4}`
  and grows like `t^{1/4}`, never as a discontinuity.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The crossover weight `e^{-(y⁴ + s y²)}`. -/
noncomputable def cw (s y : ℝ) : ℝ := Real.exp (-(y ^ 4 + s * y ^ 2))

/-- The rescaled energy `y⁴ + s y²`. -/
noncomputable def cE (s y : ℝ) : ℝ := y ^ 4 + s * y ^ 2

/-- Normalised expectation under the crossover density. -/
noncomputable def crossExp (s : ℝ) (g : ℝ → ℝ) : ℝ := (∫ y, g y * cw s y) / ∫ y, cw s y

/-- Covariance under the crossover density. -/
noncomputable def crossCov (s : ℝ) (f g : ℝ → ℝ) : ℝ :=
  crossExp s (fun y ↦ f y * g y) - crossExp s f * crossExp s g

theorem crossover_eq (s : ℝ) : crossover s = (∫ y, cE s y * cw s y) / ∫ y, cw s y := rfl

theorem cw_pos (s y : ℝ) : 0 < cw s y := Real.exp_pos _

/-- `e^{-(y⁴ + s y²)} ≤ e^{c²/2} e^{-y⁴/2}` for `|s| ≤ c`. -/
theorem cw_le {s c y : ℝ} (hs : |s| ≤ c) :
    cw s y ≤ Real.exp (c ^ 2 / 2) * Real.exp (-(1 / 2 * y ^ 4)) := by
  unfold cw
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : -s * y ^ 2 ≤ c * y ^ 2 :=
    mul_le_mul_of_nonneg_right ((neg_le_abs s).trans hs) (sq_nonneg y)
  nlinarith [sq_nonneg (c - y ^ 2)]

theorem integrable_abs_pow_mul_exp_neg_half_quartic (m : ℕ) :
    Integrable fun y : ℝ ↦ |y| ^ m * Real.exp (-(1 / 2 * y ^ 4)) := by
  have := integrable_abs_pow_mul_exp_neg_mul_pow (b := 1 / 2) (by norm_num) 2 (by norm_num) m
  simpa using this

theorem integrable_pow_mul_cw (m : ℕ) (s : ℝ) : Integrable fun y ↦ y ^ m * cw s y := by
  refine ((integrable_abs_pow_mul_exp_neg_half_quartic m).const_mul
    (Real.exp (|s| ^ 2 / 2))).mono' (by unfold cw; fun_prop)
    (Filter.Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (cw_pos s y), abs_pow]
  calc |y| ^ m * cw s y ≤ |y| ^ m * (Real.exp (|s| ^ 2 / 2) * Real.exp (-(1 / 2 * y ^ 4))) :=
        mul_le_mul_of_nonneg_left (cw_le le_rfl) (by positivity)
    _ = _ := by ring

theorem integral_cw_pos (s : ℝ) : 0 < ∫ y, cw s y := by
  have h := integrable_pow_mul_cw 0 s
  simp only [pow_zero, one_mul] at h
  refine (integral_pos_iff_support_of_nonneg (fun y ↦ (cw_pos s y).le) h).mpr ?_
  have : Function.support (fun y ↦ cw s y) = Set.univ := by
    ext y
    simp [(cw_pos s y).ne']
  rw [this]
  simp

theorem hasDerivAt_cw (s y : ℝ) : HasDerivAt (fun v ↦ cw v y) (-(y ^ 2) * cw s y) s := by
  have h := (((hasDerivAt_id s).mul_const (y ^ 2)).const_add (y ^ 4)).neg.exp
  refine h.congr_deriv ?_
  simp [cw]
  ring

theorem hasDerivAt_cE_mul_cw (s y : ℝ) :
    HasDerivAt (fun v ↦ cE v y * cw v y) (y ^ 2 * cw s y - cE s y * (y ^ 2 * cw s y)) s := by
  have h1 : HasDerivAt (fun v ↦ cE v y) (y ^ 2) s := by
    have := ((hasDerivAt_id s).mul_const (y ^ 2)).const_add (y ^ 4)
    refine this.congr_deriv ?_
    simp
  have := h1.mul (hasDerivAt_cw s y)
  refine this.congr_deriv ?_
  ring

/-- The bound used for both dominated differentiations on the unit ball around `s₀`. -/
theorem ball_abs_le {s₀ s : ℝ} (hs : s ∈ Metric.ball s₀ 1) : |s| ≤ |s₀| + 1 := by
  rw [Metric.mem_ball, Real.dist_eq] at hs
  calc |s| = |(s - s₀) + s₀| := by ring_nf
    _ ≤ |s - s₀| + |s₀| := abs_add_le _ _
    _ ≤ |s₀| + 1 := by linarith

/-- The denominator `D(s) = ∫ e^{-(y⁴+sy²)}` has derivative `−∫ y² e^{-(y⁴+sy²)}`. -/
theorem hasDerivAt_integral_cw (s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∫ y, cw s y) (-∫ y, y ^ 2 * cw s₀ y) s₀ := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := fun s y ↦ cw s y) (F' := fun s y ↦ -(y ^ 2) * cw s y)
    (x₀ := s₀) (bound := fun y ↦ Real.exp ((|s₀| + 1) ^ 2 / 2) *
      (|y| ^ 2 * Real.exp (-(1 / 2 * y ^ 4))))
    (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s ↦ by unfold cw; fun_prop)
    (by simpa using integrable_pow_mul_cw 0 s₀)
    (by unfold cw; fun_prop)
    (Filter.Eventually.of_forall fun y s hs ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg y), abs_of_pos (cw_pos s y),
        ← sq_abs]
      calc |y| ^ 2 * cw s y ≤ |y| ^ 2 * (Real.exp ((|s₀| + 1) ^ 2 / 2) *
            Real.exp (-(1 / 2 * y ^ 4))) :=
            mul_le_mul_of_nonneg_left (cw_le (ball_abs_le hs)) (by positivity)
        _ = _ := by ring)
    ((integrable_abs_pow_mul_exp_neg_half_quartic 2).const_mul _)
    (Filter.Eventually.of_forall fun y s _ ↦ hasDerivAt_cw s y)
  have := key.2
  rw [← integral_neg]
  refine this.congr_deriv ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  ring

/-- The numerator `N(s) = ∫ (y⁴+sy²) e^{-(y⁴+sy²)}` has derivative
`∫ y² w − ∫ (y⁴+sy²) y² w`. -/
theorem hasDerivAt_integral_cE_mul_cw (s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∫ y, cE s y * cw s y)
      ((∫ y, y ^ 2 * cw s₀ y) - ∫ y, cE s₀ y * y ^ 2 * cw s₀ y) s₀ := by
  have hint : ∀ s, Integrable fun y ↦ cE s y * cw s y := fun s ↦ by
    have h4 := integrable_pow_mul_cw 4 s
    have h2 := (integrable_pow_mul_cw 2 s).const_mul s
    refine (h4.add h2).congr (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.add_apply, cE]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := fun s y ↦ cE s y * cw s y)
    (F' := fun s y ↦ y ^ 2 * cw s y - cE s y * (y ^ 2 * cw s y))
    (x₀ := s₀) (bound := fun y ↦ Real.exp ((|s₀| + 1) ^ 2 / 2) *
      ((|y| ^ 2 + |y| ^ 6 + (|s₀| + 1) * |y| ^ 4) * Real.exp (-(1 / 2 * y ^ 4))))
    (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s ↦ (hint s).aestronglyMeasurable)
    (hint s₀)
    (by unfold cw cE; fun_prop)
    (Filter.Eventually.of_forall fun y s hs ↦ by
      have hs' := ball_abs_le hs
      have hc : 0 ≤ |s₀| + 1 := by positivity
      have hcw := cw_le (y := y) hs'
      have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
      have hy4 : y ^ 4 = |y| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
      have hy6 : y ^ 2 * y ^ 4 = |y| ^ 6 := by rw [hy2, hy4]; ring
      rw [Real.norm_eq_abs]
      have hpoly : |y ^ 2 - cE s y * y ^ 2| ≤ |y| ^ 2 + |y| ^ 6 + (|s₀| + 1) * |y| ^ 4 := by
        calc |y ^ 2 - cE s y * y ^ 2| ≤ |y ^ 2| + |cE s y * y ^ 2| := abs_sub _ _
          _ = |y| ^ 2 + |y ^ 4 + s * y ^ 2| * |y| ^ 2 := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg y), cE, sq_abs]
          _ ≤ |y| ^ 2 + (|y| ^ 4 + (|s₀| + 1) * |y| ^ 2) * |y| ^ 2 := by
            gcongr
            calc |y ^ 4 + s * y ^ 2| ≤ |y ^ 4| + |s * y ^ 2| := abs_add_le _ _
              _ = |y| ^ 4 + |s| * |y| ^ 2 := by
                rw [abs_mul, abs_of_nonneg (sq_nonneg y), abs_of_nonneg (by positivity), hy2, hy4]
              _ ≤ |y| ^ 4 + (|s₀| + 1) * |y| ^ 2 := by gcongr
          _ = |y| ^ 2 + |y| ^ 6 + (|s₀| + 1) * |y| ^ 4 := by ring
      calc |y ^ 2 * cw s y - cE s y * (y ^ 2 * cw s y)|
          = |y ^ 2 - cE s y * y ^ 2| * cw s y := by
            rw [show y ^ 2 * cw s y - cE s y * (y ^ 2 * cw s y) =
              (y ^ 2 - cE s y * y ^ 2) * cw s y by ring, abs_mul, abs_of_pos (cw_pos s y)]
        _ ≤ (|y| ^ 2 + |y| ^ 6 + (|s₀| + 1) * |y| ^ 4) *
            (Real.exp ((|s₀| + 1) ^ 2 / 2) * Real.exp (-(1 / 2 * y ^ 4))) :=
            mul_le_mul hpoly hcw (cw_pos s y).le (by positivity)
        _ = _ := by ring)
    (by
      have h2 := integrable_abs_pow_mul_exp_neg_half_quartic 2
      have h6 := integrable_abs_pow_mul_exp_neg_half_quartic 6
      have h4 := (integrable_abs_pow_mul_exp_neg_half_quartic 4).const_mul (|s₀| + 1)
      refine (((h2.add h6).add h4).const_mul (Real.exp ((|s₀| + 1) ^ 2 / 2))).congr
        (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [Pi.add_apply]
      ring)
    (Filter.Eventually.of_forall fun y s _ ↦ hasDerivAt_cE_mul_cw s y)
  have := key.2
  refine this.congr_deriv ?_
  have hi1 := integrable_pow_mul_cw 2 s₀
  have hi2 : Integrable fun y ↦ cE s₀ y * y ^ 2 * cw s₀ y := by
    have h6 := integrable_pow_mul_cw 6 s₀
    have h4 := (integrable_pow_mul_cw 4 s₀).const_mul s₀
    refine (h6.add h4).congr (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.add_apply, cE]
    ring
  rw [← integral_sub hi1 hi2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  ring

/-- **The crossover function is differentiable on all of `ℝ`, with derivative
`G'(s) = E_s[y²] − Cov_s(y⁴ + s y², y²)`.** -/
theorem hasDerivAt_crossover (s : ℝ) :
    HasDerivAt crossover
      (crossExp s (fun y ↦ y ^ 2) - crossCov s (cE s) (fun y ↦ y ^ 2)) s := by
  have hN := hasDerivAt_integral_cE_mul_cw s
  have hD := hasDerivAt_integral_cw s
  have hD0 := (integral_cw_pos s).ne'
  have h : HasDerivAt (fun s ↦ (∫ y, cE s y * cw s y) / ∫ y, cw s y) _ s := hN.div hD hD0
  have hfun : (fun s ↦ (∫ y, cE s y * cw s y) / ∫ y, cw s y) = crossover := by
    funext s
    exact (crossover_eq s).symm
  rw [hfun] at h
  refine h.congr_deriv ?_
  unfold crossCov crossExp
  field_simp
  ring

/-- `G'` as a function. -/
noncomputable def crossoverDeriv (s : ℝ) : ℝ :=
  crossExp s (fun y ↦ y ^ 2) - crossCov s (cE s) (fun y ↦ y ^ 2)

theorem deriv_crossover (s : ℝ) : deriv crossover s = crossoverDeriv s :=
  (hasDerivAt_crossover s).deriv

/-- **The response of the energy observable to the truth parameter at fixed temperature:**
`∂_u (t E_{u,t}[L_u]) = 2u√t · G'(u²√t)`. -/
theorem hasDerivAt_toyEnergy {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (fun u ↦ toyEnergy u t)
      (2 * u * Real.sqrt t * crossoverDeriv (u ^ 2 * Real.sqrt t)) u := by
  have hfun : (fun u ↦ toyEnergy u t) = fun u ↦ crossover (u ^ 2 * Real.sqrt t) := by
    funext u
    exact energy_eq_crossover u ht
  rw [hfun]
  have hin : HasDerivAt (fun u : ℝ ↦ u ^ 2 * Real.sqrt t) (2 * u * Real.sqrt t) u := by
    have := (hasDerivAt_pow 2 u).mul_const (Real.sqrt t)
    refine this.congr_deriv ?_
    simp
  have := (hasDerivAt_crossover (u ^ 2 * Real.sqrt t)).comp u hin
  refine this.congr_deriv ?_
  unfold crossoverDeriv
  ring

/-- The universal response shape `R(s) = √s · G'(s)`. -/
noncomputable def responseShape (s : ℝ) : ℝ := Real.sqrt s * crossoverDeriv s

/-- **Scaling collapse of the response.** For `u ≥ 0`,
`∂_u (t E_{u,t}[L_u]) = 2 t^{1/4} R(u²√t)`: one curve, amplitude `t^{1/4}`, width `t^{-1/4}`. -/
theorem toyResponse_collapse {t : ℝ} (ht : 0 < t) {u : ℝ} (hu : 0 ≤ u) :
    deriv (fun u ↦ toyEnergy u t) u =
      2 * Real.sqrt (Real.sqrt t) * responseShape (u ^ 2 * Real.sqrt t) := by
  rw [(hasDerivAt_toyEnergy ht u).deriv]
  unfold responseShape
  have h1 : Real.sqrt (u ^ 2 * Real.sqrt t) = u * Real.sqrt (Real.sqrt t) := by
    rw [Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu]
  have h2 : Real.sqrt t = Real.sqrt (Real.sqrt t) * Real.sqrt (Real.sqrt t) :=
    (Real.mul_self_sqrt (Real.sqrt_nonneg t)).symm
  rw [h1]
  linear_combination (-(2 * u * crossoverDeriv (u ^ 2 * Real.sqrt t))) * h2.symm

/-- At `u = 0` the response vanishes: the crossover is an even function of `u`. -/
theorem deriv_toyEnergy_zero {t : ℝ} (ht : 0 < t) : deriv (fun u ↦ toyEnergy u t) 0 = 0 := by
  rw [(hasDerivAt_toyEnergy ht 0).deriv]
  ring

end Laplace.Multi
