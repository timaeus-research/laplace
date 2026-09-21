/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.FourGonGibbs
import Laplace.OneD.Quartic

/-!
# The virial identity for radial potentials in the plane

The two-dimensional case of the virial identity of Proposition 12.4 of the working note
*Patterning flow*, for a radial potential `U(|δ|)`: in polar coordinates `E[δ·∇U] = 2` reduces
to the one-dimensional identity

  `∫_0^∞ r² U'(r) e^{-U(r)} dr = 2 ∫_0^∞ r e^{-U(r)} dr`,

which is the fundamental theorem of calculus on `(0, ∞)` for `r ↦ r² e^{-U(r)}`
(`radial_virial`). Applied to the localised dead component of the 4-gon,
`U(r) = t r⁴/15 + γ r²/2`, it gives the last clause of Proposition 11.1 (iii):

  `t ⟨K⟩_{t,γ} = ½ - (γ/4) ⟨r²⟩_{t,γ}`   (`deadQuartic_localized_virial`).
-/

namespace Laplace.Patterning

open Real MeasureTheory Set Filter Topology Laplace.TwoD

/-- **Radial virial identity.** For `U` differentiable on `(0, ∞)`, with `r e^{-U}` and
`r² U' e^{-U}` integrable on `(0, ∞)`, `r² e^{-U(r)}` continuous from the right at `0` and
tending to `0` at infinity, `∫_0^∞ r² U'(r) e^{-U(r)} dr = 2 ∫_0^∞ r e^{-U(r)} dr`. -/
theorem radial_virial (U U' : ℝ → ℝ) (hU : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt U (U' r) r)
    (hcont : ContinuousWithinAt (fun r => r ^ 2 * exp (-U r)) (Ici 0) 0)
    (hint1 : IntegrableOn (fun r => r * exp (-U r)) (Ioi 0))
    (hint2 : IntegrableOn (fun r => r ^ 2 * U' r * exp (-U r)) (Ioi 0))
    (htop : Tendsto (fun r => r ^ 2 * exp (-U r)) atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * U' r * exp (-U r) = 2 * ∫ r in Ioi (0 : ℝ), r * exp (-U r) := by
  have hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt (fun r => r ^ 2 * exp (-U r))
      (2 * (r * exp (-U r)) - r ^ 2 * U' r * exp (-U r)) r := by
    intro r hr
    have h := (hasDerivAt_pow 2 r).mul ((hU r hr).neg.exp)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.neg_apply]
    ring
  have h2r : IntegrableOn (fun r => 2 * (r * exp (-U r))) (Ioi (0 : ℝ)) := hint1.const_mul 2
  have hint : IntegrableOn (fun r => 2 * (r * exp (-U r)) - r ^ 2 * U' r * exp (-U r))
      (Ioi (0 : ℝ)) := h2r.sub hint2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  rw [integral_sub h2r hint2, integral_const_mul] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero] at h
  linarith

/-! ### The localised dead component `U(r) = a r⁴ + b r²` -/

/-- `rᵏ e^{-a r⁴}` is integrable on `(0, ∞)` for `a > 0`. -/
lemma integrableOn_pow_mul_exp_neg_quartic (a : ℝ) (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * exp (-(a * r ^ 4))) (Ioi 0) := by
  have h := Laplace.OneD.quartic_integrable_pow_pot k (t := 24 * a) (by positivity)
  refine (h.congr (Filter.Eventually.of_forall fun r => ?_)).integrableOn
  simp only [Laplace.OneD.quarticPotential_apply]
  congr 2
  ring

/-- `rᵏ e^{-(a r⁴ + b r²)}` is integrable on `(0, ∞)` for `a > 0`, `b ≥ 0`. -/
lemma integrableOn_pow_mul_exp_neg_quartic_quadratic (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * exp (-(a * r ^ 4 + b * r ^ 2))) (Ioi 0) := by
  refine (integrableOn_pow_mul_exp_neg_quartic a ha k).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun r : ℝ => r ^ k * exp (-(a * r ^ 4 + b * r ^ 2)))
      |>.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun r hr => ?_
    have hr' : (0 : ℝ) < r := hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg r]

/-- `r² e^{-(a r⁴ + b r²)} → 0` at infinity for `a > 0`, `b ≥ 0`. -/
lemma tendsto_sq_mul_exp_neg_quartic_quadratic (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    Tendsto (fun r : ℝ => r ^ 2 * exp (-(a * r ^ 4 + b * r ^ 2))) atTop (𝓝 0) := by
  have hg : Tendsto (fun r : ℝ => r ^ 2 * exp (-a * r ^ 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha).comp
      (tendsto_pow_atTop (n := 2) two_ne_zero)
    refine h.congr fun r => ?_
    simp [Function.comp, Real.rpow_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · exact Filter.Eventually.of_forall fun r => by positivity
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have h4 : r ^ 2 ≤ r ^ 4 := by
      have : (1 : ℝ) ≤ r ^ 2 := by nlinarith
      nlinarith [sq_nonneg r]
    nlinarith [mul_nonneg hb (sq_nonneg r)]

/-- **The localised radial virial** for `U(r) = a r⁴ + b r²`:
`∫_0^∞ (4a r⁵ + 2b r³) e^{-U} = 2 ∫_0^∞ r e^{-U}`. -/
theorem radial_virial_quartic_quadratic (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (4 * a * r ^ 3 + 2 * b * r) * exp (-(a * r ^ 4 + b * r ^ 2))
      = 2 * ∫ r in Ioi (0 : ℝ), r * exp (-(a * r ^ 4 + b * r ^ 2)) := by
  refine radial_virial (fun r => a * r ^ 4 + b * r ^ 2) (fun r => 4 * a * r ^ 3 + 2 * b * r)
    ?_ ?_ ?_ ?_ ?_
  · intro r _
    have h := ((hasDerivAt_pow 4 r).const_mul a).add ((hasDerivAt_pow 2 r).const_mul b)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  · exact (by fun_prop : Continuous fun r : ℝ => r ^ 2 * exp (-(a * r ^ 4 + b * r ^ 2)))
      |>.continuousWithinAt
  · simpa using integrableOn_pow_mul_exp_neg_quartic_quadratic a b ha hb 1
  · have h5 := (integrableOn_pow_mul_exp_neg_quartic_quadratic a b ha hb 5).const_mul (4 * a)
    have h3 := (integrableOn_pow_mul_exp_neg_quartic_quadratic a b ha hb 3).const_mul (2 * b)
    refine IntegrableOn.congr_fun (h5.add h3) (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    ring
  · exact tendsto_sq_mul_exp_neg_quartic_quadratic a b ha hb

/-- The localised loss of the dead component, `L = K + (γ/2t) r²`, so that
`e^{-tL} = e^{-tK - γ r²/2}`. -/
noncomputable def deadQuarticLocalized (t γ : ℝ) (z : ℝ × ℝ) : ℝ :=
  deadQuartic z + γ / (2 * t) * (z.1 ^ 2 + z.2 ^ 2)

lemma exp_neg_deadQuarticLocalized (t γ : ℝ) (ht : 0 < t) (z : ℝ × ℝ) :
    exp (-(t * deadQuarticLocalized t γ z))
      = exp (-(t / 15 * ((z.1 ^ 2 + z.2 ^ 2) ^ 2) + γ / 2 * (z.1 ^ 2 + z.2 ^ 2))) := by
  unfold deadQuarticLocalized deadQuartic
  congr 1
  field_simp

/-- **Proposition 11.1 (iii), localised form.** Under the Gibbs measure `∝ e^{-tK - γ r²/2}`
on the dead component, `t ⟨K⟩_{t,γ} = ½ - (γ/4) ⟨r²⟩_{t,γ}`. -/
theorem deadQuartic_localized_virial (t γ : ℝ) (ht : 0 < t) (hγ : 0 ≤ γ) :
    t * Laplace.TwoD.gibbsExpectation (deadQuarticLocalized t γ) t deadQuartic
      = 1 / 2 - γ / 4 *
        Laplace.TwoD.gibbsExpectation (deadQuarticLocalized t γ) t (fun z => z.1 ^ 2 + z.2 ^ 2) := by
  unfold Laplace.TwoD.gibbsExpectation Laplace.TwoD.partitionFunction
  simp_rw [exp_neg_deadQuarticLocalized t γ ht]
  set a := t / 15 with ha_def
  set b := γ / 2 with hb_def
  have ha : 0 < a := by positivity
  have hb : 0 ≤ b := by positivity
  -- the three integrals in radial form
  have hZ : ∫ z : ℝ × ℝ, exp (-(a * (z.1 ^ 2 + z.2 ^ 2) ^ 2 + b * (z.1 ^ 2 + z.2 ^ 2)))
      = (2 * π) * ∫ r in Ioi (0 : ℝ), r * exp (-(a * r ^ 4 + b * r ^ 2)) := by
    rw [integral_radial (fun s => exp (-(a * s ^ 2 + b * s)))]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [← pow_mul]
  have hK : ∫ z : ℝ × ℝ, deadQuartic z * exp (-(a * (z.1 ^ 2 + z.2 ^ 2) ^ 2 + b * (z.1 ^ 2 + z.2 ^ 2)))
      = (2 * π) * ∫ r in Ioi (0 : ℝ), r * (r ^ 4 / 15) * exp (-(a * r ^ 4 + b * r ^ 2)) := by
    unfold deadQuartic
    rw [integral_radial (fun s => s ^ 2 / 15 * exp (-(a * s ^ 2 + b * s)))]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [← pow_mul]
    ring
  have hR : ∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) * exp (-(a * (z.1 ^ 2 + z.2 ^ 2) ^ 2 + b * (z.1 ^ 2 + z.2 ^ 2)))
      = (2 * π) * ∫ r in Ioi (0 : ℝ), r * r ^ 2 * exp (-(a * r ^ 4 + b * r ^ 2)) := by
    rw [integral_radial (fun s => s * exp (-(a * s ^ 2 + b * s)))]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [← pow_mul]
    ring
  rw [hZ, hK, hR]
  -- the virial identity in radial form: 4t ∫ r K e^{-U} + γ ∫ r r² e^{-U} = 2 ∫ r e^{-U}
  have hvir := radial_virial_quartic_quadratic a b ha hb
  have hK5 : IntegrableOn
      (fun r : ℝ => 4 * t * (r * (r ^ 4 / 15) * exp (-(a * r ^ 4 + b * r ^ 2)))) (Ioi 0) :=
    IntegrableOn.congr_fun
      ((integrableOn_pow_mul_exp_neg_quartic_quadratic a b ha hb 5).const_mul (4 * t / 15))
      (fun r _ => by ring) measurableSet_Ioi
  have hR3 : IntegrableOn
      (fun r : ℝ => γ * (r * r ^ 2 * exp (-(a * r ^ 4 + b * r ^ 2)))) (Ioi 0) :=
    IntegrableOn.congr_fun
      ((integrableOn_pow_mul_exp_neg_quartic_quadratic a b ha hb 3).const_mul γ)
      (fun r _ => by ring) measurableSet_Ioi
  have hsplit : ∫ r in Ioi (0 : ℝ), r ^ 2 * (4 * a * r ^ 3 + 2 * b * r) * exp (-(a * r ^ 4 + b * r ^ 2))
      = 4 * t * (∫ r in Ioi (0 : ℝ), r * (r ^ 4 / 15) * exp (-(a * r ^ 4 + b * r ^ 2)))
        + γ * (∫ r in Ioi (0 : ℝ), r * r ^ 2 * exp (-(a * r ^ 4 + b * r ^ 2))) := by
    rw [← integral_const_mul (4 * t), ← integral_const_mul γ, ← integral_add hK5 hR3]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    simp only [ha_def, hb_def]
    ring
  rw [hsplit] at hvir
  have hZpos : 0 < ∫ r in Ioi (0 : ℝ), r * exp (-(a * r ^ 4 + b * r ^ 2)) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : Ioi (0 : ℝ) ⊆
          Function.support (fun r : ℝ => r * exp (-(a * r ^ 4 + b * r ^ 2))) ∩ Ioi 0 := by
        intro r hr
        refine ⟨?_, hr⟩
        rw [Function.mem_support]
        have : (0 : ℝ) < r := hr
        positivity
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      simp [Real.volume_Ioi]
    · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall fun r hr => by
        have : (0 : ℝ) < r := hr
        positivity
    · simpa using integrableOn_pow_mul_exp_neg_quartic_quadratic a b ha hb 1
  have h2π : (2 * π) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ h2π, mul_div_mul_left _ _ h2π, eq_sub_iff_add_eq, ← mul_div_assoc,
    ← mul_div_assoc, ← add_div, div_eq_iff hZpos.ne']
  linarith [hvir]

end Laplace.Patterning
