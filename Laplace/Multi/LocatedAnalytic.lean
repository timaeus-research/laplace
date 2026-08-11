/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.LocatedHeadline

/-!
# The located analytic capstone

The germbij Theorem 3.1 / Corollary 3.2 inverse direction in fully
located form, for the ACTUAL losses: two losses analytic at their
(unknown) minima, package families for the centred versions, one
physical compactly-supported data premise on a common region
containing balls around both minima --- stated literally in terms of
the raw losses' Gibbs moments over the translated localization
regions --- and the conclusion that the minima coincide and the germs
agree modulo the additive constant on a neighborhood of the common
minimum (`located_analytic_germ_recovery_of_ccData`). No symmetry
hypotheses: analyticity discharges them via
`AnalyticAt.iteratedFDeriv_isSymm`.
-/

open Real MeasureTheory Filter Topology Asymptotics Metric
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

open LocalLaplaceDomain in
/-- **The located analytic germ recovery** (germbij Theorem 3.1 +
Corollary 3.2, inverse direction, located capstone): two losses
analytic at their unknown minima whose physical localized moment
families agree beyond all orders on every smooth compactly supported
test in a common actual region containing balls around both minima
have the same minimum, and equal germs there modulo the additive
constant. -/
theorem located_analytic_germ_recovery_of_ccData
    {Λ₁ Λ₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    {p₁ p₂ : EuclidD d}
    (A : ∀ k, 2 < k → HigherLaplaceDomain k (fun y ↦ Λ₁ (p₁ + y)) H₁)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k (fun y ↦ Λ₂ (p₂ + y)) H₂)
    (hA₁ : AnalyticAt ℝ Λ₁ p₁) (hA₂ : AnalyticAt ℝ Λ₂ p₂)
    {V : Set (EuclidD d)} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hb₁ : Metric.ball p₁ r₁ ⊆ V) (hb₂ : Metric.ball p₂ r₂ ⊆ V)
    (hdata : ∀ k (h2 : 2 < k), ∀ φ : EuclidD d → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      Laplace.SuperPoly (fun t : ℝ ↦
        regionMomentT Λ₁
          (translatedRegion p₁ (A k h2).toLocalLaplaceDomain.U) φ t -
        regionMomentT Λ₂
          (translatedRegion p₂ (B k h2).toLocalLaplaceDomain.U) φ t)) :
    p₁ = p₂ ∧
      ∀ᶠ w in 𝓝 p₁, Λ₁ w - Λ₁ p₁ = Λ₂ w - Λ₂ p₁ := by
  -- centred losses and their analyticity
  have hshift₁ : AnalyticAt ℝ (fun w : EuclidD d ↦ p₁ + w) 0 :=
    analyticAt_const.add analyticAt_id
  have hshift₂ : AnalyticAt ℝ (fun w : EuclidD d ↦ p₂ + w) 0 :=
    analyticAt_const.add analyticAt_id
  have hA₁' : AnalyticAt ℝ (fun y ↦ Λ₁ (p₁ + y)) 0 := by
    have hg : AnalyticAt ℝ Λ₁ ((fun w : EuclidD d ↦ p₁ + w) 0) := by
      simpa using hA₁
    simpa [Function.comp] using hg.comp hshift₁
  have hA₂' : AnalyticAt ℝ (fun y ↦ Λ₂ (p₂ + y)) 0 := by
    have hg : AnalyticAt ℝ Λ₂ ((fun w : EuclidD d ↦ p₂ + w) 0) := by
      simpa using hA₂
    simpa [Function.comp] using hg.comp hshift₂
  -- the translated centred losses are the raw losses
  have hraw₁ : (fun w ↦ (fun y ↦ Λ₁ (p₁ + y)) (w - p₁)) = Λ₁ := by
    funext w
    simp
  have hraw₂ : (fun w ↦ (fun y ↦ Λ₂ (p₂ + y)) (w - p₂)) = Λ₂ := by
    funext w
    simp
  -- the located headline
  have hmain := located_positive_jet_recovery_of_ccData A B
    (fun k _ ↦ hA₁'.iteratedFDeriv_isSymm k)
    (fun k _ ↦ hA₂'.iteratedFDeriv_isSymm k)
    hr₁ hr₂ hb₁ hb₂
    (fun k h2 φ hφs hφc hφV ↦
      (hdata k h2 φ hφs hφc hφV).congr
        (Filter.Eventually.of_forall fun t ↦ by
          beta_reduce
          rw [hraw₁, hraw₂]))
  obtain ⟨hp, hjets⟩ := hmain
  subst hp
  refine ⟨rfl, ?_⟩
  -- centred germ equality, transported to the actual minimum
  have hgerm := analytic_germ_eq_of_jet_eq hA₁' hA₂' hjets
  have htend : Tendsto (fun w : EuclidD d ↦ w - p₁) (𝓝 p₁)
      (𝓝 (0 : EuclidD d)) := by
    have hc : Continuous fun w : EuclidD d ↦ w - p₁ :=
      continuous_id.sub continuous_const
    have := hc.tendsto p₁
    simpa using this
  filter_upwards [htend.eventually hgerm] with w hw
  simpa using hw

end Laplace.Multi
