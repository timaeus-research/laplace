/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WallPhaseDiagram

/-!
# Interior-minimum geometry of the two-monomial model

In the negative chamber `a < 0` the potential `w^p + a w^q` has the interior minimiser
`x_a = (−qa/p)^{1/(p−q)}` with Hessian `H_a = p(p−q) x_a^{p−2}`, and the observable `f = w^q` has
slope `f'(x_a) = q x_a^{q−1}`. The `√t` law is explained geometrically (Astra round 28 item 2):

* **Pointwise**: `t Var_{t,a}(w^q) → f'(x_a)²/H_a`  (`tendsto_fisherSpeed_div_interior`).
* **The moving minimiser**: `x_a' = −f'(x_a)/H_a`  (`hasDerivAt_interiorMin`), so the limiting speed
  is `√H_a |x_a'| = k₋ |a|^{β−1}`  (`sqrt_interiorHess_mul_abs_deriv`).
* **Length**: for `a₀ < a₁ < 0`, `ℓ_t(a₀,a₁)/√t → ∫_{a₀}^{a₁} √H_a |x_a'| da`
  (`interior_minimum_length`): the `√t` law measures the motion of the posterior centre in units of
  its shrinking Gaussian width.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The interior minimiser `x_a = (−qa/p)^{1/(p−q)}` (`= negScale p q (−a)`). -/
noncomputable def interiorMin (p q a : ℝ) : ℝ := negScale p q (-a)

/-- The Hessian at the interior minimiser, `H_a = p(p−q) x_a^{p−2}`. -/
noncomputable def interiorHess (p q a : ℝ) : ℝ := p * (p - q) * interiorMin p q a ^ (p - 2)

section

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p)
include hq hqp

theorem interiorMin_pos {a : ℝ} (ha : a < 0) : 0 < interiorMin p q a :=
  negScale_pos hq hqp (by linarith)

theorem interiorHess_pos {a : ℝ} (ha : a < 0) : 0 < interiorHess p q a := by
  unfold interiorHess
  have := interiorMin_pos hq hqp ha
  have : 0 < p := by linarith
  have : 0 < p - q := by linarith
  positivity

/-- The powers of the minimiser: `x_a^r = (−qa/p)^{r/(p−q)}`. -/
theorem interiorMin_rpow {a : ℝ} (ha : a < 0) (r : ℝ) :
    interiorMin p q a ^ r = (q * -a / p) ^ (r / (p - q)) := by
  unfold interiorMin negScale
  have hp : 0 < p := by linarith
  have hqa : 0 < -a := by linarith
  have hX : 0 < q * -a / p := by positivity
  rw [← Real.rpow_mul hX.le, one_div_mul_eq_div]

/-- **The moving minimiser**: `x_a' = −f'(x_a)/H_a` with `f = w^q`. -/
theorem hasDerivAt_interiorMin {a : ℝ} (ha : a < 0) :
    HasDerivAt (fun a ↦ interiorMin p q a)
      (-(q * interiorMin p q a ^ (q - 1)) / interiorHess p q a) a := by
  have hp : 0 < p := by linarith
  have hr : 0 < p - q := by linarith
  have hqa : 0 < -a := by linarith
  have hX : 0 < q * -a / p := by positivity
  have hinner : HasDerivAt (fun a : ℝ ↦ q * -a / p) (q * -1 / p) a :=
    ((hasDerivAt_id a).neg.const_mul q).div_const p
  have hpow := (Real.hasDerivAt_rpow_const (p := 1 / (p - q)) (Or.inl hX.ne')).comp a hinner
  refine hpow.congr_deriv ?_
  unfold interiorHess
  rw [interiorMin_rpow hq hqp ha, interiorMin_rpow hq hqp ha]
  have e1 : 1 / (p - q) - 1 = (q - 1) / (p - q) - (p - 2) / (p - q) := by
    field_simp
    ring
  rw [e1, Real.rpow_sub hX]
  have hden : (q * -a / p) ^ ((p - 2) / (p - q)) ≠ 0 := (Real.rpow_pos_of_pos hX _).ne'
  field_simp

/-- **The limiting speed** `√H_a |x_a'| = k₋ |a|^{β−1}`. -/
theorem sqrt_interiorHess_mul_abs_deriv {a : ℝ} (ha : a < 0) :
    Real.sqrt (interiorHess p q a) * |-(q * interiorMin p q a ^ (q - 1)) / interiorHess p q a| =
      negSpeedCoeff p q * (-a) ^ negGamma p q := by
  have hp : 0 < p := by linarith
  have hr : 0 < p - q := by linarith
  have hκ : 0 < p * (p - q) := by positivity
  have hx := interiorMin_pos hq hqp ha
  have hH := interiorHess_pos hq hqp ha
  have hqa : 0 < -a := by linarith
  have hX : 0 < q * -a / p := by positivity
  rw [abs_div, abs_neg, abs_of_pos hH, abs_of_pos (by positivity)]
  -- `√H = √(p(p−q)) x^{(p−2)/2}`
  have hsqrtH : Real.sqrt (interiorHess p q a) =
      Real.sqrt (p * (p - q)) * interiorMin p q a ^ ((p - 2) / 2) := by
    unfold interiorHess
    rw [Real.sqrt_mul hκ.le, Real.sqrt_eq_rpow (interiorMin p q a ^ (p - 2)),
      ← Real.rpow_mul hx.le]
    congr 2
    ring
  rw [hsqrtH]
  have hsκ : 0 < Real.sqrt (p * (p - q)) := Real.sqrt_pos.mpr hκ
  have hsq : Real.sqrt (p * (p - q)) * Real.sqrt (p * (p - q)) = p * (p - q) :=
    Real.mul_self_sqrt hκ.le
  -- combine the powers of `x`
  have hpow : interiorMin p q a ^ ((p - 2) / 2) * interiorMin p q a ^ (q - 1) =
      interiorMin p q a ^ ((2 * q - p) / 2) * interiorMin p q a ^ (p - 2) := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  have hval : interiorMin p q a ^ ((2 * q - p) / 2) =
      (q / p) ^ negGamma p q * (-a) ^ negGamma p q := by
    rw [interiorMin_rpow hq hqp ha, ← Real.mul_rpow (by positivity) hqa.le]
    unfold negGamma
    congr 1
    · ring
    · field_simp
  unfold interiorHess negSpeedCoeff
  have hxp : interiorMin p q a ^ (p - 2) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  set s := Real.sqrt (p * (p - q)) with hs
  have hs2 : s ^ 2 = p * (p - q) := Real.sq_sqrt hκ.le
  have hs0 : s ≠ 0 := hsκ.ne'
  clear_value s
  rw [← hs2]
  have e : s * interiorMin p q a ^ ((p - 2) / 2) *
      (q * interiorMin p q a ^ (q - 1) / (s ^ 2 * interiorMin p q a ^ (p - 2))) =
      q * (interiorMin p q a ^ ((p - 2) / 2) * interiorMin p q a ^ (q - 1)) /
        (s * interiorMin p q a ^ (p - 2)) := by
    field_simp
  rw [e, hpow, hval]
  field_simp

/-- The chamber constant is the integral of the limiting speed:
`K₋(A) = ∫₀ᴬ k₋ s^{β−1} ds`. -/
theorem negChamberConst_eq_integral (A : ℝ) :
    negChamberConst p q A = ∫ s in (0 : ℝ)..A, negSpeedCoeff p q * s ^ negGamma p q := by
  have hβ := negBeta_pos hq hqp
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (neg_one_lt_negGamma hq hqp)),
    negGamma_add_one hqp, Real.zero_rpow hβ.ne', sub_zero]
  unfold negChamberConst
  ring

/-- **The length identity**: `∫_{a₀}^{a₁} √H_a |x_a'| da = K₋(−a₀) − K₋(−a₁)` for `a₀ ≤ a₁ < 0`. -/
theorem integral_sqrt_interiorHess_mul_abs_deriv {a₀ a₁ : ℝ} (h01 : a₀ ≤ a₁) (ha₁ : a₁ < 0) :
    ∫ a in a₀..a₁, Real.sqrt (interiorHess p q a) *
      |-(q * interiorMin p q a ^ (q - 1)) / interiorHess p q a| =
      negChamberConst p q (-a₀) - negChamberConst p q (-a₁) := by
  have ha₀ : a₀ < 0 := lt_of_le_of_lt h01 ha₁
  have hγ := neg_one_lt_negGamma hq hqp
  have hI : ∀ b : ℝ, IntervalIntegrable (fun s : ℝ ↦ negSpeedCoeff p q * s ^ negGamma p q)
      volume 0 b := fun b ↦ (intervalIntegral.intervalIntegrable_rpow' hγ).const_mul _
  have e : (∫ a in a₀..a₁, Real.sqrt (interiorHess p q a) *
      |-(q * interiorMin p q a ^ (q - 1)) / interiorHess p q a|) =
      ∫ a in a₀..a₁, negSpeedCoeff p q * (-a) ^ negGamma p q := by
    refine intervalIntegral.integral_congr fun a ha ↦ ?_
    rw [uIcc_of_le h01] at ha
    exact sqrt_interiorHess_mul_abs_deriv hq hqp (lt_of_le_of_lt ha.2 ha₁)
  rw [e, intervalIntegral.integral_comp_neg (f := fun s ↦ negSpeedCoeff p q * s ^ negGamma p q),
    ← intervalIntegral.integral_interval_sub_left (hI (-a₀)) (hI (-a₁)),
    negChamberConst_eq_integral hq hqp, negChamberConst_eq_integral hq hqp]

/-- **The pointwise interior-minimum law**: `t Var_{t,a}(w^q) → f'(x_a)²/H_a` for `a < 0`. -/
theorem tendsto_fisherSpeed_div_interior {a : ℝ} (ha : a < 0) :
    Tendsto (fun t ↦ fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q)
      (twoMonoVel q) t a / t) atTop
      (𝓝 ((q * interiorMin p q a ^ (q - 1)) ^ 2 / interiorHess p q a)) := by
  have hp : 0 < p := by linarith
  have hr : 0 < p - q := by linarith
  set σ : ℝ := 1 - q / p with hσ
  have hσpos : 0 < σ := by rw [hσ, sub_pos, div_lt_one hp]; exact hqp
  have hA : 0 < -a := by linarith
  have hX : 0 < q * -a / p := by positivity
  set e : ℝ := (p - 2 * q) / (p - q) with he
  have hXe : 0 < (q * -a / p) ^ e := Real.rpow_pos_of_pos hX _
  -- the value of the limit
  have hval : (q * interiorMin p q a ^ (q - 1)) ^ 2 / interiorHess p q a =
      q ^ 2 / (p * (p - q)) / (q * -a / p) ^ e := by
    unfold interiorHess
    rw [interiorMin_rpow hq hqp ha, interiorMin_rpow hq hqp ha, mul_pow,
      ← Real.rpow_natCast ((q * -a / p) ^ ((q - 1) / (p - q))) 2, ← Real.rpow_mul hX.le]
    have e1 : (q - 1) / (p - q) * ((2 : ℕ) : ℝ) = (p - 2) / (p - q) + -e := by
      rw [he]; push_cast; field_simp; ring
    rw [e1, Real.rpow_add hX, Real.rpow_neg hX.le]
    have hne : (q * -a / p) ^ ((p - 2) / (p - q)) ≠ 0 := (Real.rpow_pos_of_pos hX _).ne'
    have hne' : (-(q * a / p)) ^ ((p - 2) / (p - q)) ≠ 0 := by
      rw [show -(q * a / p) = q * -a / p by ring]; exact hne
    have hXe' : (-(q * a / p)) ^ e ≠ 0 := by
      rw [show -(q * a / p) = q * -a / p by ring]; exact hXe.ne'
    field_simp
  rw [hval]
  -- the negative chamber along `b(t) = −a t^σ`
  have hb : Tendsto (fun t : ℝ ↦ -a * t ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσpos).const_mul_atTop hA
  have hlim := ((tendsto_negVar_mul_rpow' hq hqp).comp hb).div_const ((q * -a / p) ^ e)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply]
  have hpos : 0 < t ^ σ := Real.rpow_pos_of_pos ht _
  -- `fisherSpeed t a = (t^σ)² · negVar(−a t^σ)`
  have hF : fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q) (twoMonoVel q) t a =
      (t ^ σ) ^ 2 * negVar p q (-a * t ^ σ) := by
    have h1 : a = a * t ^ σ * t ^ (-σ) := by
      rw [mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
    conv_lhs => rw [h1]
    rw [fisherSpeed_twoMonoPath hp ht]
    unfold negVar
    rw [neg_mul, neg_neg]
  have hscale : (q * (-a * t ^ σ) / p) ^ e = (q * -a / p) ^ e * (t ^ σ) ^ e := by
    rw [show q * (-a * t ^ σ) / p = q * -a / p * t ^ σ by ring, Real.mul_rpow hX.le hpos.le]
  have hexp : (t ^ σ) ^ e = (t ^ σ) ^ 2 / t := by
    rw [← Real.rpow_natCast (t ^ σ) 2, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
      ← Real.rpow_sub_one ht.ne']
    congr 1
    rw [hσ, he]; push_cast; field_simp; ring
  rw [hF, hscale, hexp, eq_comm, mul_div_assoc (negVar p q (-a * t ^ σ)),
    mul_div_cancel_left₀ _ hXe.ne']
  ring

/-- **Phase I for a window inside the negative chamber**: for `a₀ ≤ a₁ < 0`,
`ℓ_t(a₀,a₁)/√t → K₋(−a₀) − K₋(−a₁)`. -/
theorem wall_phase_negative_pair {a₀ a₁ : ℝ} (h01 : a₀ ≤ a₁) (ha₁ : a₁ < 0) :
    Tendsto (fun t ↦ (∫ a in a₀..a₁, Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (twoMonoPath p q) (twoMonoVel q) t a)) / Real.sqrt t) atTop
      (𝓝 (negChamberConst p q (-a₀) - negChamberConst p q (-a₁))) := by
  have ha₀ : a₀ < 0 := lt_of_le_of_lt h01 ha₁
  have h0 := negative_chamber_law hq hqp (A := -a₀) (by linarith)
  have h1 := negative_chamber_law hq hqp (A := -a₁) (by linarith)
  rw [neg_neg] at h0 h1
  refine (h0.sub h1).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hcont := continuous_sqrt_fisherSpeed_twoMono hq hqp ht
  rw [← sub_div, ← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) a₀ a₁) (hcont.intervalIntegrable (μ := volume) a₁ 0),
    add_sub_cancel_right]

/-- **Interior-minimum geometry**: in the negative chamber the `√t`-normalised length converges to
`∫ √H_a |x_a'| da`, the motion of the posterior centre measured in units of its Gaussian width. -/
theorem interior_minimum_length {a₀ a₁ : ℝ} (h01 : a₀ ≤ a₁) (ha₁ : a₁ < 0) :
    Tendsto (fun t ↦ (∫ a in a₀..a₁, Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1)
      (twoMonoPath p q) (twoMonoVel q) t a)) / Real.sqrt t) atTop
      (𝓝 (∫ a in a₀..a₁, Real.sqrt (interiorHess p q a) *
        |-(q * interiorMin p q a ^ (q - 1)) / interiorHess p q a|)) := by
  rw [integral_sqrt_interiorHess_mul_abs_deriv hq hqp h01 ha₁]
  exact wall_phase_negative_pair hq hqp h01 ha₁

end

end Laplace.Multi
