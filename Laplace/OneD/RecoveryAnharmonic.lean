/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.AnharmonicFDTAsymptotic
import Laplace.OneD.AnharmonicFDTMeanAsymptotic

/-!
# Susceptibilities recover the anharmonic coefficients

The recovery reading of the germbij note's Theorem 3.1 (jet recovery at
a nondegenerate minimum) at its first two rungs, on the seabed's Stage-2
anharmonic asymptotics. For the potential
`λ/2·x² + α/6·x³ + γ/24·x⁴`, the mean susceptibility tends to `-1/λ`
and the rescaled covariance susceptibility to `α/λ³`; so eventual
equality of these two observable data streams for two parameter triples
forces `λ₁ = λ₂` and `α₁ = α₂`
(`anharmonic_susceptibility_recovery`) — the triangular induction of the
note, certified at orders two and three. The quartic coefficient `γ` is
the next rung: it requires the next cumulant's asymptotic, which the
seabed does not yet carry.
-/

open Real MeasureTheory Filter

namespace Laplace.OneD

/-- **Susceptibilities recover the anharmonic coefficients** (germbij
Theorem 3.1, first two rungs). If the mean susceptibilities and the
rescaled covariance susceptibilities of two anharmonic potentials agree
for all large `t`, the quadratic and cubic coefficients coincide. -/
theorem anharmonic_susceptibility_recovery
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
          (fun x : ℝ ↦ x) (fun x : ℝ ↦ x)) 0) :
    lam₁ = lam₂ ∧ alpha₁ = alpha₂ := by
  -- The mean susceptibility pins λ.
  have h₁ := gibbsExp_deriv_anharmonic_asymptotic hlam₁ hgamma₁ hdisc₁
  have h₂ := gibbsExp_deriv_anharmonic_asymptotic hlam₂ hgamma₂ hdisc₂
  have hlim₁ : (-1 / lam₁ : ℝ) = -1 / lam₂ :=
    tendsto_nhds_unique (h₁.congr' hexp) h₂
  have hlam : lam₁ = lam₂ := by
    have hne₁ : lam₁ ≠ 0 := hlam₁.ne'
    have hne₂ : lam₂ ≠ 0 := hlam₂.ne'
    field_simp at hlim₁
    linarith
  refine ⟨hlam, ?_⟩
  -- The covariance susceptibility pins α.
  have g₁ := gibbsCov_deriv_anharmonic_asymptotic hlam₁ hgamma₁ hdisc₁
  have g₂ := gibbsCov_deriv_anharmonic_asymptotic hlam₂ hgamma₂ hdisc₂
  have hlim₂ : (alpha₁ / lam₁ ^ 3 : ℝ) = alpha₂ / lam₂ ^ 3 :=
    tendsto_nhds_unique (g₁.congr' hcov) g₂
  subst hlam
  have hne : (lam₁ : ℝ) ^ 3 ≠ 0 := by positivity
  field_simp at hlim₂
  exact hlim₂

end Laplace.OneD
