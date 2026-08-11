/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The multivariate sector lower bound

The d-dimensional form of the germbij sector bound ("What expectation values
know about the loss landscape", 2026-08, Lemma 7.2), on `ι → ℝ` with the pi
(sup) norm and Lebesgue measure. The spherical-cap sector of the paper proof
is replaced by a *scaled set*: a measurable `S` of finite volume with
`‖x‖ ≤ 2` on `S`, windows `u • S`, and the Lebesgue scaling law
`vol (u • S) = u ^ d · vol S`. The analytic input (a nonvanishing leading
homogeneous part on a cap) is factored into the hypothesis
`c · u ^ m ≤ |a (u • x)|` on `S`, exactly as the 1D tide factored
`c · w ^ m ≤ |a w|`.

`sector_window_lower_bound_multi` bounds the window integral below by the
window volume times the worst constant; `sector_lower_bound_multi`
specialises to the Laplace scale `u = (√t)⁻¹`, giving the polynomial bound
`vol S · c² · exp (-(4 C0)) · t^(-m - d/2)`.
-/

open MeasureTheory Real Pointwise

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **Scale-window lower bound, multivariate.** The integral of
`a² · exp (-(t K))` over the scaled window `u • S` is at least the window
volume `u ^ d · vol S` times the constant
`c² u^(2m) · exp (-(4 C0 t u²))`. -/
theorem sector_window_lower_bound_multi
    (K a : (ι → ℝ) → ℝ) (m : ℕ) {c C0 u t : ℝ} {S : Set (ι → ℝ)}
    (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hu : 0 < u)
    (ha : ∀ x ∈ S, c * u ^ m ≤ |a (u • x)|)
    (hK : ∀ x ∈ S, K (u • x) ≤ 4 * (C0 * u ^ 2))
    (hint : IntegrableOn (fun w ↦ (a w) ^ 2 * Real.exp (-(t * K w)))
      (u • S) volume) :
    (volume S).toReal * u ^ (Fintype.card ι) *
      (c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2)))))
      ≤ ∫ w in u • S, (a w) ^ 2 * Real.exp (-(t * K w)) := by
  -- Measurability and volume of the window.
  have hSm : MeasurableSet (u • S) := hS.const_smul_of_ne_zero hu.ne'
  have hvol : volume (u • S)
      = ENNReal.ofReal (u ^ Fintype.card ι) * volume S := by
    rw [Measure.addHaar_smul]
    congr 2
    rw [Module.finrank_pi, abs_of_nonneg (by positivity)]
  have hvolfin : volume (u • S) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin
  -- Pointwise constant lower bound on the window.
  have hpt : ∀ w ∈ u • S,
      c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2))))
        ≤ (a w) ^ 2 * Real.exp (-(t * K w)) := by
    rintro w ⟨x, hxS, rfl⟩
    have hA : c ^ 2 * u ^ (2 * m) ≤ (a (u • x)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ c * u ^ m := by positivity
      calc c ^ 2 * u ^ (2 * m) = (c * u ^ m) ^ 2 := by ring
        _ ≤ |a (u • x)| ^ 2 := pow_le_pow_left₀ h0 (ha x hxS) 2
        _ = (a (u • x)) ^ 2 := sq_abs _
    have hB : Real.exp (-(4 * (C0 * (t * u ^ 2))))
        ≤ Real.exp (-(t * K (u • x))) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      calc t * K (u • x) ≤ t * (4 * (C0 * u ^ 2)) :=
            mul_le_mul_of_nonneg_left (hK x hxS) ht
        _ = 4 * (C0 * (t * u ^ 2)) := by ring
    calc c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2))))
        ≤ (a (u • x)) ^ 2 * Real.exp (-(4 * (C0 * (t * u ^ 2)))) :=
          mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
      _ ≤ (a (u • x)) ^ 2 * Real.exp (-(t * K (u • x))) :=
          mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  -- Integrate the constant bound.
  have hbound := MeasureTheory.setIntegral_ge_of_const_le (μ := volume)
    hSm hvolfin hpt hint
  have hlen : volume.real (u • S)
      = (volume S).toReal * u ^ (Fintype.card ι) := by
    rw [measureReal_def, hvol, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  calc (volume S).toReal * u ^ (Fintype.card ι) *
        (c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2)))))
      = volume.real (u • S)
          • (c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2))))) := by
        rw [hlen, smul_eq_mul]
    _ ≤ ∫ w in u • S, (a w) ^ 2 * Real.exp (-(t * K w)) := hbound

/-- **Sector lower bound at the Laplace scale, multivariate** (germbij
Lemma 7.2 in `ℝ^d`, scaled-set form). Substituting `u = (√t)⁻¹`, under
`4 ≤ r0² t`, a set `S` of directions with `‖x‖ ≤ 2` produces the polynomial
lower bound `vol S · c² · exp (-(4 C0)) · t^(-m - d/2)`. -/
theorem sector_lower_bound_multi
    (K a : (ι → ℝ) → ℝ) (m : ℕ) {c C0 r0 t : ℝ} {S : Set (ι → ℝ)}
    (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤)
    (hc : 0 ≤ c) (hC0 : 0 ≤ C0) (hr0 : 0 < r0) (hrt : 4 ≤ r0 ^ 2 * t)
    (hSnorm : ∀ x ∈ S, ‖x‖ ≤ 2)
    (ha : ∀ x ∈ S, c * ((Real.sqrt t)⁻¹) ^ m ≤ |a ((Real.sqrt t)⁻¹ • x)|)
    (hK : ∀ w : ι → ℝ, ‖w‖ ≤ r0 → K w ≤ C0 * ‖w‖ ^ 2)
    (hint : IntegrableOn (fun w ↦ (a w) ^ 2 * Real.exp (-(t * K w)))
      (((Real.sqrt t)⁻¹) • S) volume) :
    (volume S).toReal *
      (c ^ 2 * Real.exp (-(4 * C0)) *
        t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))
      ≤ ∫ w in ((Real.sqrt t)⁻¹) • S,
          (a w) ^ 2 * Real.exp (-(t * K w)) := by
  have ht : 0 < t := by
    by_contra h
    have h' : t ≤ 0 := not_lt.mp h
    nlinarith [sq_nonneg r0, mul_nonneg (sq_nonneg r0) (neg_nonneg.mpr h')]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set u : ℝ := (Real.sqrt t)⁻¹ with hu_def
  have hu : 0 < u := inv_pos.mpr hst
  -- `2u ≤ r0`, as in the 1D case.
  have h2 : (2 : ℝ) ≤ r0 * Real.sqrt t := by
    have hb : (0 : ℝ) ≤ r0 * Real.sqrt t := by positivity
    nlinarith [Real.sq_sqrt ht.le, sq_nonneg (r0 * Real.sqrt t - 2)]
  have hur : 2 * u ≤ r0 := by
    have heq : 2 * u = 2 / Real.sqrt t := by rw [hu_def]; ring
    rw [heq, div_le_iff₀ hst]
    linarith
  -- The window bound of `K` on `u • S`.
  have hKwin : ∀ x ∈ S, K (u • x) ≤ 4 * (C0 * u ^ 2) := by
    intro x hxS
    have hxn : ‖u • x‖ ≤ r0 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.le]
      calc u * ‖x‖ ≤ u * 2 := by
            exact mul_le_mul_of_nonneg_left (hSnorm x hxS) hu.le
        _ = 2 * u := by ring
        _ ≤ r0 := hur
    calc K (u • x) ≤ C0 * ‖u • x‖ ^ 2 := hK _ hxn
      _ ≤ 4 * (C0 * u ^ 2) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.le]
          have hx2 : ‖x‖ ≤ 2 := hSnorm x hxS
          have hxnn : 0 ≤ ‖x‖ := norm_nonneg x
          have hx4 : ‖x‖ ^ 2 ≤ 4 := by nlinarith
          nlinarith [mul_nonneg hC0 (sq_nonneg u), hx4]
  -- Algebra of the substitution.
  have htu : t * u ^ 2 = 1 := by
    rw [hu_def, inv_pow, Real.sq_sqrt ht.le]
    exact mul_inv_cancel₀ ht.ne'
  have hu2m : u ^ (2 * m) = (t ^ m)⁻¹ := by
    rw [hu_def, inv_pow, pow_mul, Real.sq_sqrt ht.le]
  have hud : u ^ (Fintype.card ι) = (Real.sqrt t ^ (Fintype.card ι))⁻¹ := by
    rw [hu_def, inv_pow]
  have hrpow : t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2)
      = (t ^ m)⁻¹ * (Real.sqrt t ^ (Fintype.card ι))⁻¹ := by
    rw [show -(m : ℝ) - (Fintype.card ι : ℝ) / 2
        = -(m : ℝ) + -((Fintype.card ι : ℝ) / 2) by ring,
      Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_neg ht.le,
      Real.rpow_natCast]
    congr 2
    rw [show (Fintype.card ι : ℝ) / 2 = 1 / 2 * (Fintype.card ι : ℝ) by ring,
      Real.rpow_mul ht.le, ← Real.sqrt_eq_rpow, Real.rpow_natCast]
  have hwin := sector_window_lower_bound_multi K a m hS hSfin hc ht.le hu
    ha hKwin hint
  calc (volume S).toReal *
        (c ^ 2 * Real.exp (-(4 * C0)) *
          t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))
      = (volume S).toReal * u ^ (Fintype.card ι) *
          (c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2))))) := by
        rw [hrpow, hu2m, htu, mul_one, hud]
        ring
    _ ≤ ∫ w in u • S, (a w) ^ 2 * Real.exp (-(t * K w)) := hwin

end Laplace
