/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.TwoD.SemiDegenerate

/-!
# Gibbs moments of the dead component of the 4-gon

Proposition 11.1 (iii) of the working note *Patterning flow*: the restricted excess loss of the
dead component, `K(x, y) = (x² + y²)² / 15` on `ℝ²`, has under its unlocalised Gibbs measure
`∝ e^{-tK}` the partition function `Z(t) = (π^{3/2}/2) √(15/t)`, the exact identity
`t ⟨K⟩_t = ½` for every `t > 0` (the learning coefficient `λ_{C₄} = ½` read off at finite
temperature), and `⟨r⟩_t = Γ(3/4) π^{-1/2} (15/t)^{1/4}`.

The route is polar coordinates (`integral_comp_polarCoord_symm`) followed by the Gamma
integrals `integral_rpow_mul_exp_neg_mul_rpow`.
-/

namespace Laplace.Patterning

open Real MeasureTheory Set Laplace.TwoD

/-- The restricted excess loss of the dead component, `K(x, y) = (x² + y²)² / 15`. -/
noncomputable def deadQuartic (z : ℝ × ℝ) : ℝ := (z.1 ^ 2 + z.2 ^ 2) ^ 2 / 15

/-- **Radial integrals in polar coordinates.** `∫_{ℝ²} G(x² + y²) = 2π ∫_0^∞ r G(r²) dr`. -/
theorem integral_radial (G : ℝ → ℝ) :
    ∫ z : ℝ × ℝ, G (z.1 ^ 2 + z.2 ^ 2) = (2 * π) * ∫ r in Ioi (0 : ℝ), r * G (r ^ 2) := by
  rw [← integral_comp_polarCoord_symm]
  have hsymm : ∀ p : ℝ × ℝ, (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
    intro p
    change (p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2 = p.1 ^ 2
    have := sin_sq_add_cos_sq p.2
    linear_combination p.1 ^ 2 * this
  simp_rw [hsymm, smul_eq_mul]
  rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  rw [show (∫ p : ℝ × ℝ, p.1 * G (p.1 ^ 2)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))))
      = (∫ r in Ioi (0 : ℝ), r * G (r ^ 2)) * ∫ _ in Ioo (-π) π, (1 : ℝ) from by
        rw [← integral_prod_mul]
        simp]
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith [pi_pos])]
  ring

/-- `∫_0^∞ rⁿ e^{-a r⁴} dr = a^{-(n+1)/4} Γ((n+1)/4) / 4` for `a > 0`. -/
theorem integral_Ioi_pow_mul_exp_neg_mul_pow_four (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ n * exp (-a * r ^ 4)
      = a ^ (-((n : ℝ) + 1) / 4) * (1 / 4) * Gamma (((n : ℝ) + 1) / 4) := by
  have hq : (-1 : ℝ) < (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [← integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 4) hq ha]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  have h4 : x ^ (4 : ℝ) = x ^ 4 := by
    rw [← rpow_natCast]
    norm_num
  rw [rpow_natCast, h4]

/-- The Boltzmann factor of `K` as a radial function. -/
lemma exp_neg_deadQuartic (t : ℝ) (z : ℝ × ℝ) :
    exp (-(t * deadQuartic z)) = exp (-(t / 15) * (z.1 ^ 2 + z.2 ^ 2) ^ 2) := by
  unfold deadQuartic
  ring_nf

/-- **The partition function.** `Z(t) = 2π (t/15)^{-1/2} Γ(1/2) / 4`. -/
theorem partitionFunction_deadQuartic (t : ℝ) (ht : 0 < t) :
    Laplace.TwoD.partitionFunction deadQuartic t
      = (2 * π) * ((t / 15) ^ (-(2 : ℝ) / 4) * (1 / 4) * Gamma (2 / 4)) := by
  unfold Laplace.TwoD.partitionFunction
  simp_rw [exp_neg_deadQuartic]
  rw [integral_radial (fun s => exp (-(t / 15) * s ^ 2))]
  have h := integral_Ioi_pow_mul_exp_neg_mul_pow_four (t / 15) (by positivity) 1
  simp only [Nat.cast_one] at h
  rw [show ((1 : ℝ) + 1) = 2 by norm_num] at h
  rw [← h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  rw [pow_one, ← pow_mul]

/-- **The numerator** `∫ K e^{-tK} = (2π/15) (t/15)^{-3/2} Γ(3/2) / 4`. -/
theorem integral_deadQuartic_mul_exp (t : ℝ) (ht : 0 < t) :
    ∫ z : ℝ × ℝ, deadQuartic z * exp (-(t * deadQuartic z))
      = (2 * π) * ((1 / 15) * ((t / 15) ^ (-(6 : ℝ) / 4) * (1 / 4) * Gamma (6 / 4))) := by
  simp_rw [exp_neg_deadQuartic]
  unfold deadQuartic
  rw [integral_radial (fun s => s ^ 2 / 15 * exp (-(t / 15) * s ^ 2))]
  have h := integral_Ioi_pow_mul_exp_neg_mul_pow_four (t / 15) (by positivity) 5
  rw [show ((5 : ℕ) : ℝ) + 1 = 6 by norm_num] at h
  rw [← h, ← integral_const_mul (1 / 15 : ℝ)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  rw [← pow_mul]
  ring

/-- **`t ⟨K⟩_t = ½` exactly, for every `t > 0`** (Proposition 11.1 (iii)). -/
theorem deadQuartic_gibbs_excess (t : ℝ) (ht : 0 < t) :
    t * Laplace.TwoD.gibbsExpectation deadQuartic t deadQuartic = 1 / 2 := by
  unfold Laplace.TwoD.gibbsExpectation
  rw [integral_deadQuartic_mul_exp t ht, partitionFunction_deadQuartic t ht]
  have ha : (0 : ℝ) < t / 15 := by positivity
  have hG : Gamma (6 / 4) = (2 / 4) * Gamma (2 / 4) := by
    rw [show (6 / 4 : ℝ) = 2 / 4 + 1 by norm_num, Gamma_add_one (by norm_num)]
  have hpow : (t / 15) ^ (-(6 : ℝ) / 4) = (t / 15) ^ (-(2 : ℝ) / 4) * (t / 15)⁻¹ := by
    rw [← rpow_neg_one, ← rpow_add ha]
    norm_num
  rw [hG, hpow]
  have hGpos : (0 : ℝ) < Gamma (2 / 4) := Gamma_pos_of_pos (by norm_num)
  have hrpos : (0 : ℝ) < (t / 15) ^ (-(2 : ℝ) / 4) := rpow_pos_of_pos ha _
  field_simp
  ring

/-- **The mean radius** `⟨r⟩_t = (t/15)^{-1/4} Γ(3/4) / Γ(1/2)`, i.e.
`Γ(3/4) π^{-1/2} (15/t)^{1/4}`. -/
theorem deadQuartic_gibbs_radius (t : ℝ) (ht : 0 < t) :
    Laplace.TwoD.gibbsExpectation deadQuartic t (fun z => √(z.1 ^ 2 + z.2 ^ 2))
      = (t / 15) ^ (-(1 : ℝ) / 4) * Gamma (3 / 4) / Gamma (2 / 4) := by
  unfold Laplace.TwoD.gibbsExpectation
  rw [partitionFunction_deadQuartic t ht]
  simp_rw [exp_neg_deadQuartic]
  rw [integral_radial (fun s => √s * exp (-(t / 15) * s ^ 2))]
  have h := integral_Ioi_pow_mul_exp_neg_mul_pow_four (t / 15) (by positivity) 2
  rw [show ((2 : ℕ) : ℝ) + 1 = 3 by norm_num] at h
  have hrad : ∫ r in Ioi (0 : ℝ), r * (√(r ^ 2) * exp (-(t / 15) * (r ^ 2) ^ 2))
      = ∫ r in Ioi (0 : ℝ), r ^ 2 * exp (-(t / 15) * r ^ 4) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [Real.sqrt_sq (le_of_lt hr), ← pow_mul]
    ring
  rw [hrad, h]
  have ha : (0 : ℝ) < t / 15 := by positivity
  have hpow : (t / 15) ^ (-(3 : ℝ) / 4) = (t / 15) ^ (-(2 : ℝ) / 4) * (t / 15) ^ (-(1 : ℝ) / 4) := by
    rw [← rpow_add ha]
    norm_num
  rw [hpow]
  have hGpos : (0 : ℝ) < Gamma (2 / 4) := Gamma_pos_of_pos (by norm_num)
  have hrpos : (0 : ℝ) < (t / 15) ^ (-(2 : ℝ) / 4) := rpow_pos_of_pos ha _
  field_simp

end Laplace.Patterning
