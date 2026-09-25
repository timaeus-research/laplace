/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ProfileGammaTail
import Laplace.Multi.ProfileTailLength
import Laplace.Multi.WallWindowLength

/-!
# The wall recedes logarithmically

For the two-monomial data family `L_a(w) = w^p + a w^q` on `(0,∞)`, `0 < q < p`, the thermodynamic
length from the wall window `a = c₀ t^{-σ*}` (`σ* = 1 − q/p`) to a fixed data point `a₁ > 0` is,
by the exact window identity (`wall_window_length`), the profile length
`∫_{c₀}^{a₁ t^{σ*}} √Var_c(y^q) dc`, and the profile speed has the Gamma tail
`c √Var_c(y^q) → √(1/q)` (`ProfileGammaTail`). Hence

  `ℓ_t(c₀ t^{-σ*}, a₁) / log t → σ* · √(1/q) = σ* √λ_q`   (`wall_recedes`),

with `λ_q = 1/q` the RLCT of the dominant monomial `w^q` on the half-line: **the wall recedes
logarithmically**, at the rate "logarithmic scale range `σ*` × limiting dilation speed `√κ`" (Astra,
round 23). This is the singular-layer counterpart of the featureless law `ℓ(t)/log t → √λ` of
`ThermoLengthAsymptotic`: a wall is a point of the data manifold where one coupling is switched
off, and its distance from the data grows like the square root of the response-active exponent
times the width of the crossover chamber in logarithmic coupling coordinates.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The profile numerator is continuous in the wall variable on `[0, ∞)` for observables of
polynomial growth (dominated by `|ψ| e^{-y^p}`). -/
theorem continuousOn_profileNum {p q : ℝ} (hp : 0 < p) {ψ : ℝ → ℝ} (hψm : Measurable ψ)
    {Mψ r : ℝ} (hr : 0 ≤ r) (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r) :
    ContinuousOn (fun c ↦ profileNum p q ψ c) (Ici 0) := by
  unfold profileNum
  refine continuousOn_of_dominated (bound := fun y ↦ Mψ * (y ^ r * Real.exp (-(y ^ p)))) ?_ ?_ ?_ ?_
  · intro c _
    exact (hψm.mul (Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg)).aestronglyMeasurable
  · intro c hc
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy ↦ ?_)
    have hy0 : (0 : ℝ) < y := hy
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    have hbnd : Real.exp (-(y ^ p + c * y ^ q)) ≤ Real.exp (-(y ^ p)) := by
      rw [Real.exp_le_exp]
      have : 0 ≤ c * y ^ q := mul_nonneg (mem_Ici.mp hc) (Real.rpow_nonneg hy0.le q)
      linarith
    calc |ψ y| * Real.exp (-(y ^ p + c * y ^ q)) ≤ (Mψ * y ^ r) * Real.exp (-(y ^ p)) :=
          mul_le_mul (hψ y hy0) hbnd (Real.exp_pos _).le (le_trans (abs_nonneg _) (hψ y hy0))
      _ = Mψ * (y ^ r * Real.exp (-(y ^ p))) := by ring
  · exact (integrableOn_rpow_mul_exp_neg_rpow_nonneg hp hr).const_mul Mψ
  · exact Filter.Eventually.of_forall fun y ↦ Continuous.continuousOn (by fun_prop)

/-- The profile variance of `y^q` is continuous in the wall variable on `[0, ∞)`. -/
theorem continuousOn_profileVar {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ContinuousOn (fun c ↦ profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2) (Ici 0) := by
  have h0 := continuousOn_profileNum hp (q := q) (ψ := fun _ ↦ (1 : ℝ)) measurable_const (Mψ := 1)
    (r := 0) le_rfl (fun y _ ↦ by simp)
  have h1 := continuousOn_profileNum hp (q := q) (ψ := fun y ↦ y ^ q) (measurable_id.pow_const q)
    (Mψ := 1) (r := q) hq (abs_rpow_le_self_rpow q)
  have h2 := continuousOn_profileNum hp (q := q) (ψ := fun y ↦ y ^ q * y ^ q)
    ((measurable_id.pow_const q).mul (measurable_id.pow_const q)) (Mψ := 1) (r := q + q)
    (add_nonneg hq hq) fun y hy ↦ by
      rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hy q) (Real.rpow_pos_of_pos hy q)),
        Real.rpow_add hy, one_mul]
  have hne : ∀ c ∈ Ici (0 : ℝ), profileNum p q (fun _ ↦ 1) c ≠ 0 := fun c hc ↦
    (profileNum_one_pos (q := q) hp hc).ne'
  unfold profilePosterior
  exact (h2.div h0 hne).sub ((h1.div h0 hne).pow 2)

/-- **The wall recedes logarithmically**: the thermodynamic length from the wall window
`c₀ t^{-σ*}` to a fixed data point `a₁` satisfies `ℓ_t / log t → σ* √(1/q)`. -/
theorem wall_recedes {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hqp : q < p) {a₁ : ℝ} (ha₁ : 0 < a₁)
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    Tendsto (fun t ↦ (∫ a in (c₀ * t ^ (-(1 - q / p)))..a₁, Real.sqrt (fisherSpeed
      (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q) (twoMonoVel q) t a)) / Real.log t)
      atTop (𝓝 ((1 - q / p) * Real.sqrt (1 / q))) := by
  set V : ℝ → ℝ := fun c ↦ profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
    profilePosterior p q (fun y ↦ y ^ q) c ^ 2 with hV
  have hσ : 0 < 1 - q / p := by
    rw [sub_pos, div_lt_one hp]
    exact hqp
  have hcont : ContinuousOn V (Ici 0) := continuousOn_profileVar hp hq.le
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun c ↦ Real.sqrt (V c)) volume a b := fun a b ha hb ↦ by
    have hsub : uIcc a b ⊆ Ici 0 := fun x hx ↦ le_trans (le_min ha hb) hx.1
    exact (Real.continuous_sqrt.comp_continuousOn (hcont.mono hsub)).intervalIntegrable
  have hlim : Tendsto (fun c ↦ c * Real.sqrt (V c)) atTop (𝓝 (Real.sqrt (1 / q))) := by
    have := (Real.continuous_sqrt.tendsto _).comp (tendsto_sq_mul_profileVar hp hq)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
    simp only [Function.comp_apply, hV]
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  have key := tendsto_integral_div_log_scaled hint hlim hσ ha₁ hc₀
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hw := wall_window_length (q := q) hp ht c₀ (a₁ * t ^ (1 - q / p))
  have e : a₁ * t ^ (1 - q / p) * t ^ (-(1 - q / p)) = a₁ := by
    rw [mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [e] at hw
  rw [hw]

end Laplace.Multi
