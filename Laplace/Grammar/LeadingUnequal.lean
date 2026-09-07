/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorTreeUniform

/-!
# The leading coefficient for unequal starting exponents (grammar §4.2)

For `p₁ = (h₁+1)/k₁ < p₂ = (h₂+1)/k₂` the smallest candidate exponent is `p₁`, it is a `u`-pole but
no `v`-pole and no collision, so `A_{p₁} = 0` (no leading logarithm) and

  `B_{p₁} = k₁⁻¹ ∑_j b^{j+Δ}/(j+Δ) · M[p₁;0;c_{0j}]`,   `Δ = k₂(p₂ − p₁) > 0`

(`leading_coeff_unequal`): the finite part is a genuine integral `∫₀^b v^{Δ−1} a₀(v,s) dv`
(Astra #9 (iii)). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- For `p₁ < p₂` no `v`-pole equals the leading `u`-pole `p₁`. -/
theorem vExp_ne_uExp_zero_of_lt (h₁ h₂ k₁ k₂ : ℕ) (hk₂ : 0 < k₂) (p₁ p₂ : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (hlt : p₁ < p₂) (j : ℕ) :
    vExp h₂ k₂ j ≠ uExp h₁ k₁ 0 := by
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  rw [uExp_zero h₁ k₁ p₁ hp₁]
  have : vExp h₂ k₂ j = p₂ + (j : ℝ) / k₂ := by
    unfold vExp; push_cast; rw [← hp₂]; field_simp; ring
  rw [this]
  have : 0 ≤ (j : ℝ) / k₂ := by positivity
  linarith

/-- **The leading coefficient for `p₁ < p₂`**: no logarithm, and the constant term is the genuine
integral of the leading `u`-face, as an absolutely convergent series. -/
theorem leading_coeff_unequal (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (hlt : p₁ < p₂) (c : ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ ij, Continuous (c ij)) (H : ℝ → ℝ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) :
    canonA β h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) p₁ = 0 ∧
      canonB β b h₁ h₂ k₁ k₂ (anaFaceU c b) (anaFaceV c b) (fun i j s => c (i, j) s) p₁
        = 1 / (k₁ : ℝ) * ∑' j : ℕ, b ^ ((j : ℝ) + k₂ * (p₂ - p₁)) / ((j : ℝ) + k₂ * (p₂ - p₁))
            * logMoment β p₁ 0 (c (0, j)) := by
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have h0 : uExp h₁ k₁ 0 = p₁ := uExp_zero h₁ k₁ p₁ hp₁
  have hno : ∀ j, vExp h₂ k₂ j ≠ uExp h₁ k₁ 0 :=
    vExp_ne_uExp_zero_of_lt h₁ h₂ k₁ k₂ hk₂ p₁ p₂ hp₁ hp₂ hlt
  have hC : canonC h₁ h₂ k₁ k₂ (fun i j s => c (i, j) s) p₁ = fun _ => 0 := by
    rw [← h0]; exact canonC_uExp_of_not h₁ h₂ k₁ k₂ _ 0 hno
  have hV : canonV b h₁ h₂ k₁ k₂ (anaFaceV c b) (fun i j s => c (i, j) s) p₁ = fun _ => 0 := by
    rw [← h0]; exact canonV_of_not b h₁ h₂ k₁ k₂ _ _ _ hno
  -- the transverse parameter of the leading face is `−Δ`
  have hγ : (k₂ : ℝ) * uExp h₁ k₁ 0 - h₂ - 1 = -((k₂ : ℝ) * (p₂ - p₁)) := by
    rw [h0, ← hp₂]; field_simp; ring
  have hΔ : 0 < (k₂ : ℝ) * (p₂ - p₁) := by
    have : 0 < p₂ - p₁ := by linarith
    positivity
  refine ⟨?_, ?_⟩
  · unfold canonA
    rw [hC, logMoment_zero_fun]
  · unfold canonB
    rw [hC, hV, logMoment_zero_fun, logMoment_zero_fun, add_zero, sub_zero]
    have hU := (logMoment_canonU_series β b ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ c hcc H hc hC₀
      henv 0 0).2
    rw [h0] at hU
    rw [hU]
    congr 1
    refine tsum_congr fun j => ?_
    congr 1
    rw [← h0, hγ]
    unfold axisPrim
    have hne : (j : ℝ) ≠ -((k₂ : ℝ) * (p₂ - p₁)) := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      intro h; linarith
    rw [if_neg hne, sub_neg_eq_add, h0]

end Laplace.Grammar
