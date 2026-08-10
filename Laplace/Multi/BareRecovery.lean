/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.RadialTaylorBound
import Laplace.Multi.LocatedAnalytic

/-!
# Bare-setup recovery: the end-to-end convenience statement

One theorem from the note's prose data to the note's conclusion:
two globally smooth losses, analytic at their unknown minima, with
vanishing recentred gradients and diagonal-matched positive-definite
matrices, whose physical localized moment families agree beyond all
orders — over every pair of ball localizations, on smooth compactly
supported tests in a common region containing balls around both
minima — have the same minimum and equal germs there modulo the
additive constant (`located_analytic_germ_recovery_of_bare_setup`).

All content lives in the earlier tides; this file only instantiates
the package constructor's ball regions in the radius-quantified data
premise and hands everything to the located analytic capstone.
-/

open Real MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-- **Located analytic germ recovery from the bare setup**: the
end-to-end form of the germbij Theorem 3.1 + Corollary 3.2 inverse
direction, with every package hypothesis discharged. -/
theorem located_analytic_germ_recovery_of_bare_setup
    {Λ₁ Λ₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    {p₁ p₂ : EuclidD d}
    (hcont₁ : ∀ k : ℕ, ContDiff ℝ k Λ₁)
    (hcont₂ : ∀ k : ℕ, ContDiff ℝ k Λ₂)
    (hgrad₁ : fderiv ℝ (fun y ↦ Λ₁ (p₁ + y)) 0 = 0)
    (hgrad₂ : fderiv ℝ (fun y ↦ Λ₂ (p₂ + y)) 0 = 0)
    (hdiag₁ : ∀ y, qform (hessianMatrix (fun y ↦ Λ₁ (p₁ + y))) y =
      qform H₁ y)
    (hdiag₂ : ∀ y, qform (hessianMatrix (fun y ↦ Λ₂ (p₂ + y))) y =
      qform H₂ y)
    (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef)
    (hA₁ : AnalyticAt ℝ Λ₁ p₁) (hA₂ : AnalyticAt ℝ Λ₂ p₂)
    {V : Set (EuclidD d)} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hb₁ : Metric.ball p₁ r₁ ⊆ V) (hb₂ : Metric.ball p₂ r₂ ⊆ V)
    (hdata : ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → 0 < ρ₂ →
      ∀ φ : EuclidD d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ V →
      Laplace.SuperPoly (fun t : ℝ ↦
        regionMomentT Λ₁
          (translatedRegion p₁ (Metric.ball (0 : EuclidD d) ρ₁)) φ t -
        regionMomentT Λ₂
          (translatedRegion p₂ (Metric.ball (0 : EuclidD d) ρ₂)) φ t)) :
    p₁ = p₂ ∧
      ∀ᶠ w in 𝓝 p₁, Λ₁ w - Λ₁ p₁ = Λ₂ w - Λ₂ p₁ := by
  -- smoothness of the recentred losses
  have hcont₁' : ∀ k : ℕ, ContDiff ℝ k fun y ↦ Λ₁ (p₁ + y) :=
    fun k ↦ (hcont₁ k).comp (contDiff_const.add contDiff_id)
  have hcont₂' : ∀ k : ℕ, ContDiff ℝ k fun y ↦ Λ₂ (p₂ + y) :=
    fun k ↦ (hcont₂ k).comp (contDiff_const.add contDiff_id)
  -- the certified package families and the located capstone;
  -- by construction each package's region is the ball of radius
  -- `delta`, so the radius-quantified data premise instantiates at
  -- the packages' own `delta` fields
  refine located_analytic_germ_recovery_of_ccData
    (higherLaplaceDomainFamily_ofContDiff hcont₁' hgrad₁ hdiag₁ hH₁)
    (higherLaplaceDomainFamily_ofContDiff hcont₂' hgrad₂ hdiag₂ hH₂)
    hA₁ hA₂ hr₁ hr₂ hb₁ hb₂ ?_
  intro k h2 φ hφs hφc hφV
  rw [show (higherLaplaceDomainFamily_ofContDiff hcont₁' hgrad₁
        hdiag₁ hH₁ k h2).toLocalLaplaceDomain.U =
      Metric.ball (0 : EuclidD d)
        (higherLaplaceDomainFamily_ofContDiff hcont₁' hgrad₁ hdiag₁
          hH₁ k h2).toLocalLaplaceDomain.delta from rfl,
    show (higherLaplaceDomainFamily_ofContDiff hcont₂' hgrad₂
        hdiag₂ hH₂ k h2).toLocalLaplaceDomain.U =
      Metric.ball (0 : EuclidD d)
        (higherLaplaceDomainFamily_ofContDiff hcont₂' hgrad₂ hdiag₂
          hH₂ k h2).toLocalLaplaceDomain.delta from rfl]
  exact hdata _ _
    (higherLaplaceDomainFamily_ofContDiff hcont₁' hgrad₁ hdiag₁ hH₁
      k h2).toLocalLaplaceDomain.delta_pos
    (higherLaplaceDomainFamily_ofContDiff hcont₂' hgrad₂ hdiag₂ hH₂
      k h2).toLocalLaplaceDomain.delta_pos φ hφs hφc hφV

end Laplace.Multi
