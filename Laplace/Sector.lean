/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The sector lower bound

The second ingredient of the germbij identifiability theorem ("What
expectation values know about the loss landscape", 2026-08, Lemma 7.2), in
one dimension with the analytic-germ input factored into hypotheses: if
`0 ≤ K ≤ C0 * w^2` and `c * w^m ≤ |a w|` on `[0, r0]`, then the integral of
`a^2 · exp (-(t * K))` over the window `[u, 2u]` is bounded below by the
window length times the worst constant (`sector_window_lower_bound`), and at
the Laplace scale `u = (√t)⁻¹` this produces the polynomial lower bound
`c^2 · exp (-(4 C0)) · t^(-m - 1/2)` (`sector_lower_bound`), the quantity
that contradicts `o(t^{-∞})` in the identifiability argument.
-/

open MeasureTheory Real

namespace Laplace

/-- **Scale-window lower bound.** On a window `[u, 2u] ⊆ [0, r0]`, the
integrand `a^2 · exp (-(t K))` is bounded below by the constant
`c^2 u^(2m) · exp (-(4 C0 t u^2))`, so the integral is bounded below by `u`
times that constant. -/
theorem sector_window_lower_bound
    (K a : ℝ → ℝ) (m : ℕ) {c C0 r0 u t : ℝ}
    (hc : 0 ≤ c) (hC0 : 0 ≤ C0) (ht : 0 ≤ t)
    (hu : 0 < u) (hur : 2 * u ≤ r0)
    (hK2 : ∀ w ∈ Set.Icc (0 : ℝ) r0, K w ≤ C0 * w ^ 2)
    (ha : ∀ w ∈ Set.Icc (0 : ℝ) r0, c * w ^ m ≤ |a w|)
    (hcont : ContinuousOn (fun w ↦ (a w) ^ 2 * Real.exp (-(t * K w)))
      (Set.Icc u (2 * u))) :
    u * (c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2)))))
      ≤ ∫ w in Set.Icc u (2 * u), (a w) ^ 2 * Real.exp (-(t * K w)) := by
  have hsub : Set.Icc u (2 * u) ⊆ Set.Icc (0 : ℝ) r0 := fun w hw ↦
    ⟨le_trans hu.le hw.1, le_trans hw.2 hur⟩
  -- Pointwise lower bound by the constant on the window.
  have hpt : ∀ w ∈ Set.Icc u (2 * u),
      c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2))))
        ≤ (a w) ^ 2 * Real.exp (-(t * K w)) := by
    intro w hw
    have hw0r : w ∈ Set.Icc (0 : ℝ) r0 := hsub hw
    -- Amplitude factor: `c^2 u^(2m) ≤ (a w)^2`.
    have hA : c ^ 2 * u ^ (2 * m) ≤ (a w) ^ 2 := by
      have h0 : (0 : ℝ) ≤ c * u ^ m := by positivity
      have h2 : c * u ^ m ≤ |a w| :=
        le_trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hu.le hw.1 m) hc) (ha w hw0r)
      calc c ^ 2 * u ^ (2 * m) = (c * u ^ m) ^ 2 := by ring
        _ ≤ |a w| ^ 2 := pow_le_pow_left₀ h0 h2 2
        _ = (a w) ^ 2 := sq_abs (a w)
    -- Boltzmann factor: `exp (-(4 C0 t u^2)) ≤ exp (-(t K w))`.
    have hB : Real.exp (-(4 * (C0 * (t * u ^ 2)))) ≤ Real.exp (-(t * K w)) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have hw2 : w ^ 2 ≤ (2 * u) ^ 2 := by nlinarith [hw.1, hw.2, hu.le]
      have hKw : K w ≤ 4 * (C0 * u ^ 2) := by
        have := hK2 w hw0r
        nlinarith
      calc t * K w ≤ t * (4 * (C0 * u ^ 2)) := mul_le_mul_of_nonneg_left hKw ht
        _ = 4 * (C0 * (t * u ^ 2)) := by ring
    calc c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2))))
        ≤ (a w) ^ 2 * Real.exp (-(4 * (C0 * (t * u ^ 2)))) :=
          mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
      _ ≤ (a w) ^ 2 * Real.exp (-(t * K w)) :=
          mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  -- Integrate the constant lower bound over the window.
  have hmeas : MeasurableSet (Set.Icc u (2 * u)) := measurableSet_Icc
  have hvol : volume (Set.Icc u (2 * u)) ≠ ⊤ := by
    simp [Real.volume_Icc]
  have hintOn : IntegrableOn (fun w ↦ (a w) ^ 2 * Real.exp (-(t * K w)))
      (Set.Icc u (2 * u)) volume :=
    hcont.integrableOn_compact isCompact_Icc
  have hbound := MeasureTheory.setIntegral_ge_of_const_le (μ := volume)
    hmeas hvol hpt hintOn
  have hlen : volume.real (Set.Icc u (2 * u)) = u := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  calc u * (c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2)))))
      = volume.real (Set.Icc u (2 * u))
          • (c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2))))) := by
        rw [hlen, smul_eq_mul]
    _ ≤ ∫ w in Set.Icc u (2 * u), (a w) ^ 2 * Real.exp (-(t * K w)) := hbound

/-- **Sector lower bound at the Laplace scale** (germbij Lemma 7.2, 1D).
Substituting `u = (√t)⁻¹` in the window bound, under `4 ≤ r0^2 * t`, gives
the polynomial lower bound `c^2 · exp (-(4 C0)) · t^(-m - 1/2)`. -/
theorem sector_lower_bound
    (K a : ℝ → ℝ) (m : ℕ) {c C0 r0 t : ℝ}
    (hc : 0 ≤ c) (hC0 : 0 ≤ C0) (hr0 : 0 < r0) (hrt : 4 ≤ r0 ^ 2 * t)
    (hK2 : ∀ w ∈ Set.Icc (0 : ℝ) r0, K w ≤ C0 * w ^ 2)
    (ha : ∀ w ∈ Set.Icc (0 : ℝ) r0, c * w ^ m ≤ |a w|)
    (hcont : ContinuousOn (fun w ↦ (a w) ^ 2 * Real.exp (-(t * K w)))
      (Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹))) :
    c ^ 2 * Real.exp (-(4 * C0)) * t ^ (-(m : ℝ) - 1 / 2)
      ≤ ∫ w in Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹),
          (a w) ^ 2 * Real.exp (-(t * K w)) := by
  have ht : 0 < t := by
    by_contra h
    have h' : t ≤ 0 := not_lt.mp h
    nlinarith [sq_nonneg r0, mul_nonneg (sq_nonneg r0) (neg_nonneg.mpr h')]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set u : ℝ := (Real.sqrt t)⁻¹ with hu_def
  have hu : 0 < u := inv_pos.mpr hst
  -- `2 ≤ r0 √t`, hence `2u ≤ r0`.
  have h2 : (2 : ℝ) ≤ r0 * Real.sqrt t := by
    have hb : (0 : ℝ) ≤ r0 * Real.sqrt t := by positivity
    nlinarith [Real.sq_sqrt ht.le, sq_nonneg (r0 * Real.sqrt t - 2)]
  have hur : 2 * u ≤ r0 := by
    have : 2 * u = 2 / Real.sqrt t := by rw [hu_def]; ring
    rw [this, div_le_iff₀ hst]
    linarith
  -- Algebra of the substitution `u = (√t)⁻¹`.
  have htu : t * u ^ 2 = 1 := by
    rw [hu_def, inv_pow, Real.sq_sqrt ht.le]
    exact mul_inv_cancel₀ ht.ne'
  have hu2m : u ^ (2 * m) = (t ^ m)⁻¹ := by
    rw [hu_def, inv_pow, pow_mul, Real.sq_sqrt ht.le]
  have hrpow : t ^ (-(m : ℝ) - 1 / 2) = (t ^ m)⁻¹ * u := by
    rw [hu_def,
      show -(m : ℝ) - 1 / 2 = -(m : ℝ) + -(1 / 2) by ring,
      Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_neg ht.le,
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hwin := sector_window_lower_bound K a m hc hC0 ht.le hu hur hK2 ha hcont
  calc c ^ 2 * Real.exp (-(4 * C0)) * t ^ (-(m : ℝ) - 1 / 2)
      = u * (c ^ 2 * u ^ (2 * m) * Real.exp (-(4 * (C0 * (t * u ^ 2))))) := by
        rw [hrpow, hu2m, htu, mul_one]
        ring
    _ ≤ ∫ w in Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹),
          (a w) ^ 2 * Real.exp (-(t * K w)) := hwin

end Laplace
