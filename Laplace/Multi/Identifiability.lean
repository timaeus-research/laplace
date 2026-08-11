/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Pencil
import Laplace.Multi.Sector

/-!
# The identifiability lower bound, multivariate

The quantitative core of the germbij identifiability theorem ("What
expectation values know about the loss landscape", 2026-08, Theorem 7.3) in
`ℝ^d`, completing the germbij arc. For nonnegative potentials `L₁, L₂` on
`ι → ℝ` with `L₁ + L₂ ≤ C0 ‖w‖²` on the ball of radius `r0`, difference
`g = L₂ - L₁` bounded below on a scaled set `S` at the Laplace scale, and a
nonnegative bump `ψ` equal to `1` on the ball, the observable `g ψ` gives

  `vol S · c² exp (-(4 C0)) · t · t^(-m - d/2)
     ≤ ∫ g ψ (e^{-t L₁} - e^{-t L₂})`,

so the two Boltzmann families cannot agree to all polynomial orders. The
proof composes the measure-general pencil identity
(`pencil_identity_integrated_measure`), the scalar comparison along the
pencil (`exp_pencil_ge_scalar`), and the multivariate sector bound
(`sector_lower_bound_multi`).
-/

open MeasureTheory Real Pointwise

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-- **Identifiability lower bound, multivariate** (germbij Theorem 7.3,
quantitative core, `ℝ^d`). -/
theorem pencil_difference_lower_bound_multi
    (L₁ L₂ ψ : (ι → ℝ) → ℝ) (m : ℕ) {c C0 r0 t : ℝ} {S : Set (ι → ℝ)}
    (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤)
    (hc : 0 ≤ c) (hC0 : 0 ≤ C0) (hr0 : 0 < r0) (hrt : 4 ≤ r0 ^ 2 * t)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hSnorm : ∀ x ∈ S, ‖x‖ ≤ 2)
    (hsum : ∀ w : ι → ℝ, ‖w‖ ≤ r0 → L₁ w + L₂ w ≤ C0 * ‖w‖ ^ 2)
    (hgrow : ∀ x ∈ S, c * ((Real.sqrt t)⁻¹) ^ m
      ≤ |L₂ ((Real.sqrt t)⁻¹ • x) - L₁ ((Real.sqrt t)⁻¹ • x)|)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ r0 → ψ w = 1)
    (hmin : Integrable fun w ↦
      (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
    (hint : Integrable (Function.uncurry fun s w ↦
        ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
          Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))))
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume))
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, Integrable fun w ↦
        ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
          Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))))) :
    (volume S).toReal *
      (c ^ 2 * Real.exp (-(4 * C0)) *
        (t * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2)))
      ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := by
  have ht : 0 < t := by
    by_contra h
    have h' : t ≤ 0 := not_lt.mp h
    nlinarith [sq_nonneg r0, mul_nonneg (sq_nonneg r0) (neg_nonneg.mpr h')]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set u : ℝ := (Real.sqrt t)⁻¹ with hu_def
  have hu : 0 < u := inv_pos.mpr hst
  have h2 : (2 : ℝ) ≤ r0 * Real.sqrt t := by
    have hb : (0 : ℝ) ≤ r0 * Real.sqrt t := by positivity
    nlinarith [Real.sq_sqrt ht.le, sq_nonneg (r0 * Real.sqrt t - 2)]
  have hur : 2 * u ≤ r0 := by
    have heq : 2 * u = 2 / Real.sqrt t := by rw [hu_def]; ring
    rw [heq, div_le_iff₀ hst]
    linarith
  have hwnorm : ∀ x ∈ S, ‖u • x‖ ≤ r0 := by
    intro x hxS
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.le]
    calc u * ‖x‖ ≤ u * 2 :=
          mul_le_mul_of_nonneg_left (hSnorm x hxS) hu.le
      _ = 2 * u := by ring
      _ ≤ r0 := hur
  -- Step 1: the pencil identity with observable `φ = g ψ`.
  have hpencil := pencil_identity_integrated_measure volume L₁ L₂
    (fun w ↦ (L₂ w - L₁ w) * ψ w) t hint
  beta_reduce at hpencil
  -- Step 2: every pencil slice dominates the minorant.
  have hFB : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ w, (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
        ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by
    intro s hs
    apply MeasureTheory.integral_mono hmin (hslice s hs)
    intro w
    have hle := exp_pencil_ge_scalar (t := t) (s := s)
      ht.le hs.1 hs.2 (hL1 w) (hL2 w)
    have hψw := hψ0 w
    calc (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w)))
        ≤ (L₂ w - L₁ w) ^ 2 * ψ w *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w)))) := by
          apply mul_le_mul_of_nonneg_left hle
          positivity
      _ = ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
            Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) := by ring
  -- Step 3: interval-integrate the slice bound.
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
  -- Step 4: the window, where `ψ = 1`.
  have hSm : MeasurableSet (u • S) := hS.const_smul_of_ne_zero hu.ne'
  have hwinψ : Set.EqOn
      (fun w ↦ (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
      (fun w ↦ (L₂ w - L₁ w) ^ 2 * Real.exp (-(t * (L₁ w + L₂ w))))
      (u • S) := by
    rintro w ⟨x, hxS, rfl⟩
    simp only [hψ1 _ (hwnorm x hxS), mul_one]
  have hintW : IntegrableOn
      (fun w ↦ (L₂ w - L₁ w) ^ 2 * Real.exp (-(t * (L₁ w + L₂ w))))
      (u • S) volume :=
    (hmin.integrableOn).congr_fun hwinψ hSm
  have hBwin : (∫ w in u • S,
      (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
      ≤ ∫ w, (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))) := by
    apply MeasureTheory.setIntegral_le_integral hmin
    filter_upwards with w
    have hψw := hψ0 w
    positivity
  have hwin_eq : (∫ w in u • S,
      (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))))
      = ∫ w in u • S,
        (L₂ w - L₁ w) ^ 2 * Real.exp (-(t * (L₁ w + L₂ w))) :=
    MeasureTheory.setIntegral_congr_fun hSm hwinψ
  -- Step 5: the multivariate sector bound with `K = L₁ + L₂`, `a = g`.
  have hsec := sector_lower_bound_multi (fun w ↦ L₁ w + L₂ w)
    (fun w ↦ L₂ w - L₁ w) m hS hSfin hc hC0 hr0 hrt hSnorm hgrow
    (fun w hw ↦ hsum w hw) hintW
  beta_reduce at hsec
  -- Assemble.
  calc (volume S).toReal *
        (c ^ 2 * Real.exp (-(4 * C0)) *
          (t * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2)))
      = t * ((volume S).toReal *
          (c ^ 2 * Real.exp (-(4 * C0)) *
            t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))) := by
        ring
    _ ≤ t * ∫ w, (L₂ w - L₁ w) ^ 2 * ψ w *
          Real.exp (-(t * (L₁ w + L₂ w))) := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        calc (volume S).toReal *
              (c ^ 2 * Real.exp (-(4 * C0)) *
                t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))
            ≤ ∫ w in u • S,
                (L₂ w - L₁ w) ^ 2 * Real.exp (-(t * (L₁ w + L₂ w))) := hsec
          _ = ∫ w in u • S,
                (L₂ w - L₁ w) ^ 2 * ψ w * Real.exp (-(t * (L₁ w + L₂ w))) :=
              hwin_eq.symm
          _ ≤ ∫ w, (L₂ w - L₁ w) ^ 2 * ψ w *
                Real.exp (-(t * (L₁ w + L₂ w))) := hBwin
    _ ≤ t * ∫ s in (0 : ℝ)..1, ∫ w, ((L₂ w - L₁ w) * ψ w) * ((L₂ w - L₁ w) *
          Real.exp (-(t * (L₁ w + s * (L₂ w - L₁ w))))) :=
        mul_le_mul_of_nonneg_left hIB ht.le
    _ = ∫ w, ((L₂ w - L₁ w) * ψ w) *
          (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := hpencil.symm

end Laplace
