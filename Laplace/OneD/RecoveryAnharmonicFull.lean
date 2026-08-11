/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.RecoveryAnharmonic
import Laplace.OneD.Kappa4Asymptotic

/-!
# The full anharmonic jet recovery (gamma-rung finale)

The gamma-rung programme's endpoint. The merged two-rung recovery pins
`(λ, α)` from the mean and covariance susceptibilities; the
fourth-cumulant limit `t³κ₄ → 3α²/λ⁵ - γ/λ⁴` then pins `γ`:
if additionally the fourth-cumulant data streams of two anharmonic
potentials eventually agree, all three coefficients coincide
(`anharmonic_jet_recovery`). This is the germbij note's Theorem 3.1
triangular induction carried through its third rung — the complete jet
`(λ, α, γ)` of the quartic-truncated anharmonic potential is determined
by the observable data.
-/

open Real MeasureTheory Filter

namespace Laplace.OneD

/-- The fourth-cumulant moment combination, as observed data. -/
private noncomputable def kappa4Data (lam alpha gamma t : ℝ) : ℝ :=
  Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t
      (fun x ↦ x ^ 4)
    - 4 * Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 3) *
      Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x ↦ x)
    - 3 * Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 2) ^ 2
    + 12 * Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x ↦ x ^ 2) *
      Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x ↦ x) ^ 2
    - 6 * Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x ↦ x) ^ 4

/-- **Full anharmonic jet recovery** (germbij Theorem 3.1, rungs two
through four). If the mean susceptibilities, the rescaled covariance
susceptibilities, and the fourth-cumulant data of two anharmonic
potentials eventually agree, then `λ₁ = λ₂`, `α₁ = α₂`, and
`γ₁ = γ₂`. -/
theorem anharmonic_jet_recovery
    {lam₁ lam₂ alpha₁ alpha₂ gamma₁ gamma₂ : ℝ}
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hgamma₁ : 0 < gamma₁) (hgamma₂ : 0 < gamma₂)
    (hdisc₁ : alpha₁ ^ 2 < 3 * lam₁ * gamma₁)
    (hdisc₂ : alpha₂ ^ 2 < 3 * lam₂ * gamma₂)
    (hexp : (fun t : ℝ ↦ deriv
        (fun h : ℝ ↦ Threepoint.gibbsExp (volume : Measure ℝ)
          (anharmonicPotential lam₁ alpha₁ gamma₁) (fun x : ℝ ↦ x) t h
          (fun x : ℝ ↦ x)) 0)
      =ᶠ[atTop] fun t : ℝ ↦ deriv
        (fun h : ℝ ↦ Threepoint.gibbsExp (volume : Measure ℝ)
          (anharmonicPotential lam₂ alpha₂ gamma₂) (fun x : ℝ ↦ x) t h
          (fun x : ℝ ↦ x)) 0)
    (hcov : (fun t : ℝ ↦ t * deriv
        (fun h : ℝ ↦ Threepoint.gibbsCov (volume : Measure ℝ)
          (anharmonicPotential lam₁ alpha₁ gamma₁) (fun x : ℝ ↦ x) t h
          (fun x : ℝ ↦ x) (fun x : ℝ ↦ x)) 0)
      =ᶠ[atTop] fun t : ℝ ↦ t * deriv
        (fun h : ℝ ↦ Threepoint.gibbsCov (volume : Measure ℝ)
          (anharmonicPotential lam₂ alpha₂ gamma₂) (fun x : ℝ ↦ x) t h
          (fun x : ℝ ↦ x) (fun x : ℝ ↦ x)) 0)
    (hkappa : (fun t : ℝ ↦ kappa4Data lam₁ alpha₁ gamma₁ t)
      =ᶠ[atTop] fun t : ℝ ↦ kappa4Data lam₂ alpha₂ gamma₂ t) :
    lam₁ = lam₂ ∧ alpha₁ = alpha₂ ∧ gamma₁ = gamma₂ := by
  obtain ⟨hlam, halpha⟩ := anharmonic_susceptibility_recovery
    hlam₁ hlam₂ hgamma₁ hgamma₂ hdisc₁ hdisc₂ hexp hcov
  refine ⟨hlam, halpha, ?_⟩
  subst hlam
  subst halpha
  -- The two fourth-cumulant limits agree along the eventual equality.
  have h₁ := kappa4_anharmonic_asymptotic hlam₁ hgamma₁ hdisc₁
  have h₂ := kappa4_anharmonic_asymptotic hlam₁ hgamma₂ hdisc₂
  have heq : (fun t : ℝ ↦ t ^ 3 * kappa4Data lam₁ alpha₁ gamma₁ t)
      =ᶠ[atTop] fun t : ℝ ↦ t ^ 3 * kappa4Data lam₁ alpha₁ gamma₂ t := by
    filter_upwards [hkappa] with t ht
    rw [ht]
  have h₁' : Tendsto (fun t : ℝ ↦ t ^ 3 *
      kappa4Data lam₁ alpha₁ gamma₂ t) atTop
      (nhds (3 * alpha₁ ^ 2 / lam₁ ^ 5 - gamma₁ / lam₁ ^ 4)) := by
    apply Tendsto.congr' heq
    exact h₁
  have hlim := tendsto_nhds_unique h₁' h₂
  -- 3α²/λ⁵ - γ₁/λ⁴ = 3α²/λ⁵ - γ₂/λ⁴ forces γ₁ = γ₂.
  have hl4 : (lam₁ : ℝ) ^ 4 ≠ 0 := by positivity
  have : gamma₁ / lam₁ ^ 4 = gamma₂ / lam₁ ^ 4 := by linarith
  field_simp at this
  exact this

end Laplace.OneD
