/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MixtureRigidity

/-!
# A phase diagram over the data manifold: the coupled limit of `w⁴ + s w²`

The mixture path `L_s = (1 − s) w⁴ + s (w⁴ + w²) = w⁴ + s w²` joins the loss `w⁴` (exponent
`1/4`) to `w⁴ + w²` (exponent `1/2`) through mixtures with a common minimiser. By the interior
rigidity of `MixtureRigidity` the fixed-`s` exponent is `1/2` for every `s ∈ (0, 1]` and jumps to
`1/4` only at the face `s = 0`. The **coupled limit** `s = t^{-σ}`, in which the data distribution
approaches the face as the inverse temperature grows, resolves the jump into a piecewise affine
exponent

  `λ(σ) = max (1/4, (1 − σ)/2)`   (`coupledExponent`)

with `t^{λ(σ)} Z(t, t^{-σ}) → C(σ)` (`coupled_phase_diagram`): for `σ < 1/2` the quadratic term
dominates and `C = √π` (Gaussian regime); for `σ > 1/2` the quartic term dominates and
`C = ∫ e^{-y⁴}`; at the tie `σ = 1/2` both scale together and `C = ∫ e^{-(y⁴ + y²)}`. The exponent
is continuous with a change of slope at the tie, while the leading constant jumps there: ties
change slopes, not values, of the exponent, and the crossover variable is `s t^{1/2}`, not `st`.
This is the simplest instance of the singular layer of the response map: the asymptotic type is a
function on the data manifold that is locally constant on strata and has a piecewise affine
coupled-limit exponent at the boundary between them.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

/-- The coupled partition function `Z(t, s) = ∫ e^{-t(w⁴ + s w²)} dw`. -/
noncomputable def quartZ (t s : ℝ) : ℝ := ∫ w : ℝ, Real.exp (-(t * (w ^ 4 + s * w ^ 2)))

/-- The quartic profile `∫ e^{-(y⁴ + c y²)} dy`. -/
noncomputable def quartProfile (c : ℝ) : ℝ := ∫ y : ℝ, Real.exp (-(y ^ 4 + c * y ^ 2))

/-- The Gaussian profile `∫ e^{-(y² + c y⁴)} dy`. -/
noncomputable def gaussProfile (c : ℝ) : ℝ := ∫ y : ℝ, Real.exp (-(y ^ 2 + c * y ^ 4))

/-- The exponent of the coupled limit `s = t^{-σ}`: `λ(σ) = max (1/4, (1 − σ)/2)`. -/
noncomputable def coupledExponent (σ : ℝ) : ℝ := max (1 / 4) ((1 - σ) / 2)

/-- The leading constant of the coupled limit. -/
noncomputable def coupledConstant (σ : ℝ) : ℝ :=
  if σ < 1 / 2 then Real.sqrt Real.pi else if σ = 1 / 2 then quartProfile 1 else quartProfile 0

theorem coupledExponent_of_le {σ : ℝ} (hσ : σ ≤ 1 / 2) : coupledExponent σ = (1 - σ) / 2 :=
  max_eq_right (by linarith)

theorem coupledExponent_of_ge {σ : ℝ} (hσ : 1 / 2 ≤ σ) : coupledExponent σ = 1 / 4 :=
  max_eq_left (by linarith)

theorem integrable_exp_neg_quartic : Integrable fun y : ℝ ↦ Real.exp (-(y ^ 4)) := by
  have hg := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul (Real.exp (1 / 4))
  refine hg.mono' (by fun_prop : Continuous fun y : ℝ ↦ Real.exp (-(y ^ 4))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [sq_nonneg (y ^ 2 - 1 / 2)]

/-- `∫ e^{-(y⁴ + c y²)} → ∫ e^{-y⁴}` as `c → 0⁺`. -/
theorem tendsto_quartProfile {c : ℝ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hc0 : ∀ᶠ t in atTop, 0 ≤ c t) :
    Tendsto (fun t ↦ quartProfile (c t)) atTop (𝓝 (quartProfile 0)) := by
  unfold quartProfile
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ Real.exp (-(y ^ 4)))
    (Filter.Eventually.of_forall fun t ↦
      (by fun_prop : Continuous fun y : ℝ ↦ Real.exp (-(y ^ 4 + c t * y ^ 2))).aestronglyMeasurable)
    ?_ integrable_exp_neg_quartic (Filter.Eventually.of_forall fun y ↦ ?_)
  · filter_upwards [hc0] with t ht
    refine Filter.Eventually.of_forall fun y ↦ ?_
    rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
    nlinarith [sq_nonneg y, mul_nonneg ht (sq_nonneg y)]
  · have h1 : Tendsto (fun t ↦ -(y ^ 4 + c t * y ^ 2)) atTop (𝓝 (-(y ^ 4 + 0 * y ^ 2))) :=
      ((hc.mul_const _).const_add _).neg
    exact (Real.continuous_exp.tendsto _).comp h1

/-- `∫ e^{-(y² + c y⁴)} → ∫ e^{-y²} = √π` as `c → 0⁺`. -/
theorem tendsto_gaussProfile {c : ℝ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hc0 : ∀ᶠ t in atTop, 0 ≤ c t) :
    Tendsto (fun t ↦ gaussProfile (c t)) atTop (𝓝 (gaussProfile 0)) := by
  unfold gaussProfile
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ Real.exp (-(y ^ 2)))
    (Filter.Eventually.of_forall fun t ↦
      (by fun_prop :
        Continuous fun y : ℝ ↦ Real.exp (-(y ^ 2 + c t * y ^ 4))).aestronglyMeasurable)
    ?_ ?_ (Filter.Eventually.of_forall fun y ↦ ?_)
  · filter_upwards [hc0] with t ht
    refine Filter.Eventually.of_forall fun y ↦ ?_
    rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
    nlinarith [mul_nonneg ht (pow_nonneg (sq_nonneg y) 2)]
  · simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  · have h1 : Tendsto (fun t ↦ -(y ^ 2 + c t * y ^ 4)) atTop (𝓝 (-(y ^ 2 + 0 * y ^ 4))) :=
      ((hc.mul_const _).const_add _).neg
    exact (Real.continuous_exp.tendsto _).comp h1

theorem gaussProfile_zero : gaussProfile 0 = Real.sqrt Real.pi := by
  unfold gaussProfile
  have := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at this
  simpa using this

/-- The quartic scaling: `Z(t, s) = t^{-1/4} ∫ e^{-(y⁴ + t^{1/2} s y²)}`. -/
theorem quartZ_eq_quartProfile {t : ℝ} (ht : 0 < t) (s : ℝ) :
    quartZ t s = t ^ (-(1 / 4 : ℝ)) * quartProfile (t ^ (1 / 2 : ℝ) * s) := by
  unfold quartZ quartProfile
  have ha : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun y ↦ Real.exp (-(y ^ 4 + (t ^ (1 / 2 : ℝ) * s) * y ^ 2))) (t ^ (1 / 4 : ℝ))
  beta_reduce at key
  rw [abs_of_pos (inv_pos.mpr ha), smul_eq_mul, ← Real.rpow_neg ht.le] at key
  rw [← key]
  have h4 : (t ^ (1 / 4 : ℝ)) ^ 4 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  have h2 : (t ^ (1 / 4 : ℝ)) ^ 2 = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  have hh : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by
    rw [← Real.rpow_add ht]; norm_num
  congr 1
  funext w
  congr 1
  rw [mul_pow, mul_pow, h4, h2]
  linear_combination (s * w ^ 2) * hh

/-- The Gaussian scaling at `s = t^{-σ}`:
`Z(t, t^{-σ}) = t^{-(1-σ)/2} ∫ e^{-(y² + t^{2σ-1} y⁴)}`. -/
theorem quartZ_eq_gaussProfile {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    quartZ t (t ^ (-σ)) = t ^ (-((1 - σ) / 2)) * gaussProfile (t ^ (2 * σ - 1)) := by
  unfold quartZ gaussProfile
  have ha : 0 < t ^ ((1 - σ) / 2) := Real.rpow_pos_of_pos ht _
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun y ↦ Real.exp (-(y ^ 2 + t ^ (2 * σ - 1) * y ^ 4))) (t ^ ((1 - σ) / 2))
  beta_reduce at key
  rw [abs_of_pos (inv_pos.mpr ha), smul_eq_mul, ← Real.rpow_neg ht.le] at key
  rw [← key]
  have h2 : (t ^ ((1 - σ) / 2)) ^ 2 = t ^ (1 - σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  have h4 : (t ^ ((1 - σ) / 2)) ^ 4 = t ^ (2 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num; ring_nf
  have hA : t ^ (1 - σ) = t * t ^ (-σ) := by
    rw [show (1 - σ) = 1 + -σ by ring, Real.rpow_add ht, Real.rpow_one]
  have hB : t ^ (2 * σ - 1) * t ^ (2 * (1 - σ)) = t := by
    rw [← Real.rpow_add ht, show 2 * σ - 1 + 2 * (1 - σ) = 1 by ring, Real.rpow_one]
  congr 1
  funext w
  congr 1
  rw [mul_pow, mul_pow, h2, h4, hA]
  linear_combination (w ^ 4) * hB

/-- **Quartic regime** `σ > 1/2`: `t^{1/4} Z(t, t^{-σ}) → ∫ e^{-y⁴}`. -/
theorem coupled_quartic_regime {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun t ↦ t ^ (1 / 4 : ℝ) * quartZ t (t ^ (-σ))) atTop (𝓝 (quartProfile 0)) := by
  have hc : Tendsto (fun t : ℝ ↦ t ^ (1 / 2 - σ)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < σ - 1 / 2)
    simpa only [neg_sub] using this
  refine (tendsto_quartProfile hc ?_).congr' ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (Real.rpow_pos_of_pos ht _).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [quartZ_eq_quartProfile ht, ← mul_assoc, ← Real.rpow_add ht, ← Real.rpow_add ht]
    norm_num
    rw [sub_eq_add_neg]

/-- **Gaussian regime** `σ < 1/2`: `t^{(1-σ)/2} Z(t, t^{-σ}) → √π`. -/
theorem coupled_gaussian_regime {σ : ℝ} (hσ : σ < 1 / 2) :
    Tendsto (fun t ↦ t ^ ((1 - σ) / 2) * quartZ t (t ^ (-σ))) atTop (𝓝 (Real.sqrt Real.pi)) := by
  have hc : Tendsto (fun t : ℝ ↦ t ^ (2 * σ - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - 2 * σ)
    simpa only [neg_sub] using this
  rw [← gaussProfile_zero]
  refine (tendsto_gaussProfile hc ?_).congr' ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (Real.rpow_pos_of_pos ht _).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [quartZ_eq_gaussProfile ht, ← mul_assoc, ← Real.rpow_add ht]
    norm_num

/-- **The tie** `σ = 1/2`: `t^{1/4} Z(t, t^{-1/2}) → ∫ e^{-(y⁴ + y²)}`. -/
theorem coupled_tie :
    Tendsto (fun t ↦ t ^ (1 / 4 : ℝ) * quartZ t (t ^ (-(1 / 2 : ℝ)))) atTop
      (𝓝 (quartProfile 1)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [quartZ_eq_quartProfile ht, ← mul_assoc, ← Real.rpow_add ht, ← Real.rpow_add ht]
  norm_num

/-- **The phase diagram of the coupled limit**: `t^{λ(σ)} Z(t, t^{-σ}) → C(σ)` with the piecewise
affine exponent `λ(σ) = max (1/4, (1 − σ)/2)` and the constant `C(σ)` jumping at the tie. -/
theorem coupled_phase_diagram (σ : ℝ) :
    Tendsto (fun t ↦ t ^ coupledExponent σ * quartZ t (t ^ (-σ))) atTop
      (𝓝 (coupledConstant σ)) := by
  unfold coupledConstant
  rcases lt_trichotomy σ (1 / 2) with hσ | hσ | hσ
  · rw [if_pos hσ, coupledExponent_of_le hσ.le]
    exact coupled_gaussian_regime hσ
  · rw [if_neg (by rw [hσ]; norm_num), if_pos hσ, coupledExponent_of_ge hσ.ge, hσ]
    exact coupled_tie
  · rw [if_neg (by linarith), if_neg (by linarith), coupledExponent_of_ge hσ.le]
    exact coupled_quartic_regime hσ

end Laplace.Multi
