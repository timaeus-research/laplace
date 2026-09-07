/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseMajorant

/-!
# The derivative dictionary in the phase parameter (Stage 4j)

Unit 250 (Taylor-tree programme; Astra #28 candidate C, first half). The paper writes the
coefficients through derivatives of the fluctuation function `S_μ(a) = ∫₀^∞ t^{μ-1} e^{-βt+β√t a} dt`:
`∂_a^p S_μ(a) = β^p ∫₀^∞ t^{μ-1}(√t)^p e^{-βt+β√t a} dt`. Here this is a theorem: for `β > 0`, `μ > 0`,
```
∂_a fluctMoment β a p μ i = β · fluctMoment β a (p+1) μ i,
iteratedDeriv p (a ↦ fluctMoment β a q μ i) a = β^p · fluctMoment β a (p+q) μ i,
```
(`hasDerivAt_fluctMoment`, `iteratedDeriv_fluctMoment`), by differentiation under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with the log majorant of unit 234 at phase
parameter `|a| + 1` as the local dominating function. In particular
`β^p fluctMoment β a p μ 0 = ∂_a^p S_μ(a)` (`iteratedDeriv_fluctuationFn`), so the Stage 3 coefficient
formula reads as in the paper. No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

/-- The fluctuation function `S_μ(a) = ∫₀^∞ t^{μ-1} e^{-βt+β√t a} dt` (`fluctMoment` at `p = i = 0`). -/
noncomputable def fluctuationFn (β μ a : ℝ) : ℝ := fluctMoment β a 0 μ 0

theorem phaseKernel_eq_exp (β a : ℝ) (p : ℕ) (t : ℝ) :
    phaseKernel β a p t = Real.sqrt t ^ p * Real.exp (-(β * t) + β * Real.sqrt t * a) := rfl

/-- `∂_a phaseKernel β a p t = β √t · phaseKernel β a p t`. -/
theorem hasDerivAt_phaseKernel (β : ℝ) (p : ℕ) (t a : ℝ) :
    HasDerivAt (fun a => phaseKernel β a p t) (β * Real.sqrt t * phaseKernel β a p t) a := by
  have h : HasDerivAt (fun a => -(β * t) + β * Real.sqrt t * a) (β * Real.sqrt t) a := by
    simpa using ((hasDerivAt_id a).const_mul (β * Real.sqrt t)).const_add (-(β * t))
  have := (h.exp).const_mul (Real.sqrt t ^ p)
  simp only [phaseKernel_eq_exp]
  exact this.congr_deriv (by ring)

/-- The integrand of `fluctMoment` in the phase parameter. -/
noncomputable def fluctIntegrand (β : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (a t : ℝ) : ℝ :=
  t ^ (μ - 1) * (-Real.log t) ^ i * phaseKernel β a p t

theorem fluctIntegrand_succ (β : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (a t : ℝ) :
    β * Real.sqrt t * fluctIntegrand β p μ i a t = β * fluctIntegrand β (p + 1) μ i a t := by
  unfold fluctIntegrand phaseKernel
  rw [pow_succ]
  ring

/-- Local domination: for `|a' - a| < 1` and `t > 0`,
`|β √t · fluctIntegrand a' t| ≤ β · logMajorant β (|a|+1) μ i (p+1) t`. -/
theorem abs_deriv_fluctIntegrand_le (β : ℝ) (hβ : 0 < β) (p : ℕ) (μ : ℝ) (i : ℕ) {a a' : ℝ}
    (ha : a' ∈ Metric.ball a 1) {t : ℝ} (ht : 0 < t) :
    ‖β * Real.sqrt t * fluctIntegrand β p μ i a' t‖ ≤ β * logMajorant β (|a| + 1) μ i (p + 1) t := by
  rw [fluctIntegrand_succ, Real.norm_eq_abs, abs_mul, abs_of_pos hβ]
  refine mul_le_mul_of_nonneg_left ?_ hβ.le
  unfold fluctIntegrand logMajorant
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _),
    abs_of_nonneg (phaseKernel_nonneg _ _ _ _), abs_pow, abs_neg]
  have h1 : |Real.log t| ^ i ≤ (1 + |Real.log t|) ^ i :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log t)]) i
  have ha' : a' ≤ |a| + 1 := by
    have := Metric.mem_ball.1 ha
    rw [Real.dist_eq] at this
    linarith [le_abs_self a, (abs_sub_le_iff.1 this.le).1]
  have h2 : phaseKernel β a' (p + 1) t ≤ phaseKernel β (|a| + 1) (p + 1) t := by
    unfold phaseKernel
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (pow_nonneg (Real.sqrt_nonneg _) _)
    have : 0 ≤ β * Real.sqrt t := by positivity
    nlinarith
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht.le _)) h2
    (phaseKernel_nonneg _ _ _ _) (by positivity)

theorem continuous_fluctIntegrand_a (β : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (a : ℝ) :
    ContinuousOn (fluctIntegrand β p μ i a) (Ioi 0) := by
  unfold fluctIntegrand
  exact (((continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)).mul
    ((Real.continuousOn_log.mono fun _ ht => ne_of_gt ht).neg.pow i)).mul
    (continuous_phaseKernel β a p).continuousOn)

/-- **`∂_a fluctMoment = β · fluctMoment` at the next phase order.** -/
theorem hasDerivAt_fluctMoment (β : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) (a : ℝ) :
    HasDerivAt (fun a => fluctMoment β a p μ i) (β * fluctMoment β a (p + 1) μ i) a := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a t => fluctIntegrand β p μ i a t)
    (F' := fun a t => β * Real.sqrt t * fluctIntegrand β p μ i a t)
    (bound := fun t => β * logMajorant β (|a| + 1) μ i (p + 1) t) (x₀ := a)
    (Metric.ball_mem_nhds a one_pos)
    (Eventually.of_forall fun a' =>
      ((continuous_fluctIntegrand_a β p μ i a').aestronglyMeasurable measurableSet_Ioi))
    (integrableOn_fluct β a hβ p hμ i)
    (((continuous_const.mul Real.continuous_sqrt).continuousOn.mul
      (continuous_fluctIntegrand_a β p μ i a)).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht a' ha' =>
      abs_deriv_fluctIntegrand_le β hβ p μ i ha' (mem_Ioi.1 ht))
    ((integrableOn_logMajorant β (|a| + 1) μ hβ hμ i (p + 1)).const_mul β)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ a' _ => by
      have := (hasDerivAt_phaseKernel β p t a').const_mul (t ^ (μ - 1) * (-Real.log t) ^ i)
      unfold fluctIntegrand
      exact this.congr_deriv (by ring))
  have hval : ∫ t in Ioi (0 : ℝ), β * Real.sqrt t * fluctIntegrand β p μ i a t =
      β * fluctMoment β a (p + 1) μ i := by
    unfold fluctMoment
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => fluctIntegrand_succ β p μ i a t
  rw [hval] at key
  exact key.2

/-- **Iterated derivatives**: `∂_a^p fluctMoment(·, q) = β^p fluctMoment(·, p+q)`. -/
theorem iteratedDeriv_fluctMoment (β : ℝ) (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    ∀ p q : ℕ, iteratedDeriv p (fun a => fluctMoment β a q μ i) =
      fun a => β ^ p * fluctMoment β a (p + q) μ i
  | 0, q => by simp
  | p + 1, q => by
    rw [iteratedDeriv_succ, iteratedDeriv_fluctMoment β hβ hμ i p q]
    funext a
    have := ((hasDerivAt_fluctMoment β hβ (p + q) hμ i a).const_mul (β ^ p)).deriv
    rw [this, show p + 1 + q = p + q + 1 by ring, pow_succ]
    ring

/-- **The paper's dictionary**: `∂_a^p S_μ(a) = β^p ∫₀^∞ t^{μ-1}(√t)^p e^{-βt+β√t a} dt`, i.e.
`β^p · fluctMoment β a p μ 0 = ∂_a^p S_μ(a)`. -/
theorem iteratedDeriv_fluctuationFn (β : ℝ) (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (p : ℕ) (a : ℝ) :
    iteratedDeriv p (fluctuationFn β μ) a = β ^ p * fluctMoment β a p μ 0 := by
  unfold fluctuationFn
  rw [iteratedDeriv_fluctMoment β hβ hμ 0 p 0, add_zero]

end Laplace.Grammar
