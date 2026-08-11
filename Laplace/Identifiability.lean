/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Pencil
import Laplace.Sector

/-!
# The identifiability lower bound

The quantitative core of the germbij identifiability theorem ("What
expectation values know about the loss landscape", 2026-08, Theorem 7.3), in
one dimension. For nonnegative potentials `L₁, L₂` vanishing at `0` with
`L₁ + L₂ ≤ C0 w^2` near `0`, difference `g = L₂ - L₁` of finite vanishing
order (`c w^m ≤ |g|`), and a nonnegative bump `ψ` equal to `1` near `0`, the
observable `φ = g ψ` witnesses a polynomial lower bound

  `c^2 exp (-(4 C0)) · t · t^(-m - 1/2)
     ≤ ∫ φ (e^{-t L₁} - e^{-t L₂})`

so the two Boltzmann families cannot agree to all polynomial orders: this is
the contradiction that proves the identifiability theorem. The proof composes
the pencil identity (`pencil_identity_integrated`), the comparison along the
pencil (`exp_pencil_ge`), and the sector bound (`sector_lower_bound`).
-/

open MeasureTheory Real

namespace Laplace

/-- **Identifiability lower bound** (germbij Theorem 7.3, quantitative core,
1D). The observable `g ψ` with `g = L₂ - L₁` makes the difference of
Boltzmann integrals at least `c^2 exp (-(4 C0)) · t^(1 - m - 1/2)`. -/
theorem pencil_difference_lower_bound
    (L₁ L₂ ψ : ℝ → ℝ) (m : ℕ) {c C0 r0 t : ℝ}
    (hc : 0 ≤ c) (hC0 : 0 ≤ C0) (hr0 : 0 < r0) (hrt : 4 ≤ r0 ^ 2 * t)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hsum : ∀ w ∈ Set.Icc (0 : ℝ) r0, L₁ w + L₂ w ≤ C0 * w ^ 2)
    (hgrow : ∀ w ∈ Set.Icc (0 : ℝ) r0, c * w ^ m ≤ |L₂ w - L₁ w|)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w ∈ Set.Icc (0 : ℝ) r0, ψ w = 1)
    (hmin : Integrable fun w ↦
      (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
    (hint : Integrable (Function.uncurry fun s w ↦
        ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
          Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume))
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, Integrable fun w ↦
        ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
          Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
    (hcontW : ContinuousOn
      (fun w ↦ (L₂ w - L₁ w) ^ 2 * Real.exp (-(t * (L₁ w + L₂ w))))
      (Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹))) :
    c ^ 2 * Real.exp (-(4 * C0)) * (t * t ^ (-(m : ℝ) - 1 / 2))
      ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := by
  have ht : 0 < t := by
    by_contra h
    have h' : t ≤ 0 := not_lt.mp h
    nlinarith [sq_nonneg r0, mul_nonneg (sq_nonneg r0) (neg_nonneg.mpr h')]
  -- Step 1: the pencil identity with observable `φ = g ψ`.
  have hpencil := pencil_identity_integrated L₁ L₂
    (fun w ↦ (L₂ w - L₁ w) * ψ w) t hint
  beta_reduce at hpencil
  -- Step 2: every pencil slice dominates the minorant `B`.
  have hFB : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ w, (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
        ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
    intro s hs
    apply MeasureTheory.integral_mono hmin (hslice s hs)
    intro w
    have hle := exp_pencil_ge L₁ L₂ w ht.le hs.1 hs.2 (hL1 w) (hL2 w)
    have hψw := hψ0 w
    calc (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w)))
        ≤ (L₂ w - L₁ w) ^ 2 * ψ w *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))) := by
          apply mul_le_mul_of_nonneg_left hle
          positivity
      _ = ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by ring
  -- Step 3: interval-integrate the slice bound over `s ∈ [0, 1]`.
  have hFint : IntervalIntegrable (fun s ↦
      ∫ w, ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
        Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))))) volume 0 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hint.integral_prod_left
  have hIB : (∫ w, (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
      ≤ ∫ s in (0 : ℝ)..1, ∫ w, ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
          Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      intervalIntegrable_const hFint hFB
    simpa using h
  -- Step 4: the window `[u, 2u]` at `u = (√t)⁻¹` sits inside `[0, r0]`.
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hu : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hst
  have h2 : (2 : ℝ) ≤ r0 * Real.sqrt t := by
    have hb : (0 : ℝ) ≤ r0 * Real.sqrt t := by positivity
    nlinarith [Real.sq_sqrt ht.le, sq_nonneg (r0 * Real.sqrt t - 2)]
  have hur : 2 * (Real.sqrt t)⁻¹ ≤ r0 := by
    have heq : 2 * (Real.sqrt t)⁻¹ = 2 / Real.sqrt t := by ring
    rw [heq, div_le_iff₀ hst]
    linarith
  have hwin_sub : Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹)
      ⊆ Set.Icc (0 : ℝ) r0 := fun w hw ↦
    ⟨le_trans hu.le hw.1, le_trans hw.2 hur⟩
  -- Step 5: the minorant dominates its window restriction, where `ψ = 1`.
  have hBwin : (∫ w in Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹),
      (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
      ≤ ∫ w, (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))) := by
    apply MeasureTheory.setIntegral_le_integral hmin
    filter_upwards with w
    have hψw := hψ0 w
    positivity
  have hwin_eq : (∫ w in Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹),
      (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
      = ∫ w in Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹),
        (L₂ w - L₁ w) ^ 2 * Real.exp (-(t * (L₁ w + L₂ w))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro w hw
    simp only [hψ1 w (hwin_sub hw), mul_one]
  -- Step 6: the sector bound with `K = L₁ + L₂`, `a = g`.
  have hsec := sector_lower_bound (fun w ↦ L₁ w + L₂ w) (fun w ↦ L₂ w - L₁ w)
    m hc hC0 hr0 hrt hsum hgrow hcontW
  beta_reduce at hsec
  -- Assemble.
  calc c ^ 2 * Real.exp (-(4 * C0)) * (t * t ^ (-(m : ℝ) - 1 / 2))
      = t * (c ^ 2 * Real.exp (-(4 * C0)) * t ^ (-(m : ℝ) - 1 / 2)) := by
        ring
    _ ≤ t * ∫ w, (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))) := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        calc c ^ 2 * Real.exp (-(4 * C0)) * t ^ (-(m : ℝ) - 1 / 2)
            ≤ ∫ w in Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹),
                (L₂ w - L₁ w) ^ 2 * Real.exp (-(t * (L₁ w + L₂ w))) := hsec
          _ = ∫ w in Set.Icc ((Real.sqrt t)⁻¹) (2 * (Real.sqrt t)⁻¹),
                (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))) :=
              hwin_eq.symm
          _ ≤ ∫ w, (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))) :=
              hBwin
    _ ≤ t * ∫ s in (0 : ℝ)..1, ∫ w, ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
          Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) :=
        mul_le_mul_of_nonneg_left hIB ht.le
    _ = ∫ w, ((L₂ w - L₁ w) * ψ w) *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := hpencil.symm

end Laplace
