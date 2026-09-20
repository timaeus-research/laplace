/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CutoffMonomialFamily

/-!
# The fixed monomial family with a positive weight in place of a window

The isolated-zero sufficiency theorem (`normalized_families_force_germ_eq_at_of_cutoff_monomials`)
takes the observables `χ · x^α` with `χ` a smooth cutoff equal to `1` near the zero. The window
normalisation is not needed: any smooth compactly supported weight `a ≥ 0` with `a ≥ a₀ > 0` near
the zero works. A smooth test `φ` supported where `a ≥ a₀` factors as `φ = a · (φ / a)` with
`φ / a` smooth and compactly supported, so the Taylor-expansion argument applies to `φ / a`
(`superPoly_projDiff_weight_mul_of_monomials`), and the polynomial bound on the scalar comes
from `a` dominating `a₀` times a bump (`exists_scalar_upper_bound_of_weight`).

This is the "positive-weight" form of the isolated-zero theorem: the ingredient needed to
replace product cutoffs by marginal weights in the non-isolated (cylinder) setting.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] {L₁ L₂ : (ι → ℝ) → ℝ} {C : ℝ → ℝ}

/-- **A fixed sufficient family with a positive weight.** Let `a` be a smooth compactly
supported nonnegative weight with `a ≥ a₀ > 0` on `ball p ρ`, and let `L₁ ≥ c ‖x - p‖^ν` on
its support. If the projective hypothesis holds beyond all orders for the family
`a · ∏ⱼ (x (m j) - p (m j))` over all words `m`, then `L₁ = L₂` near `p`. -/
theorem normalized_families_force_germ_eq_at_of_weight_monomials
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w) {p : ι → ℝ}
    (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p) (hp1 : L₁ p = 0) (hp2 : L₂ p = 0)
    {a : (ι → ℝ) → ℝ} (ha : ContDiff ℝ ∞ a) (has : HasCompactSupport a) (ha0 : ∀ w, 0 ≤ a w)
    {ρ a₀ : ℝ} (hρ : 0 < ρ) (ha₀ : 0 < a₀) (haball : ∀ w ∈ Metric.ball p ρ, a₀ ≤ a w)
    {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (hcoer : ∀ w ∈ tsupport a, c * ‖w - p‖ ^ ν ≤ L₁ w)
    (hfam : ∀ (k : ℕ) (m : Fin k → ι),
      SuperPoly (projDiff L₁ L₂ C fun w ↦ a w * coordMonomial p m w)) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  have ha₀' : ∀ᶠ w in 𝓝 p, a₀ ≤ a w :=
    (Metric.isOpen_ball.eventually_mem (Metric.mem_ball_self hρ)).mono haball
  have hpos : ∀ w ∈ Metric.ball p ρ, 0 < a w := fun w hw ↦ lt_of_lt_of_le ha₀ (haball w hw)
  -- the degree-zero member is the weight itself
  have h0 : SuperPoly (projDiff L₁ L₂ C a) := by
    have := hfam 0 Fin.elim0
    have haeq : (fun w ↦ a w * coordMonomial p Fin.elim0 w) = a := by
      funext w
      simp [coordMonomial, Finset.univ_eq_empty]
    rwa [haeq] at this
  obtain ⟨A, hA, hCbound⟩ := exists_scalar_upper_bound_of_weight h1.continuous h2.continuous
    hL1 hL2 hp1 hA1.contDiffAt ha.continuous has ha0 ha₀ ha₀' h0
  refine normalized_families_force_germ_eq_at_local (C := C) h1 h2 hL1 hL2 hA1 hA2 hp1 hp2 hρ ?_
  intro φ hφ hφs hφsupp
  -- the test divided by the weight
  set ψ : (ι → ℝ) → ℝ := fun w ↦ φ w / a w with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ Metric.ball p ρ
    · exact hφ.contDiffAt.div ha.contDiffAt (hpos w hw).ne'
    · have hnot : w ∉ tsupport φ := fun h ↦ hw (hφsupp h)
      have hev : ∀ᶠ z in 𝓝 w, z ∉ tsupport φ :=
        (isClosed_tsupport φ).isOpen_compl.eventually_mem hnot
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      simp only [hψ_def, image_eq_zero_of_notMem_tsupport hz, zero_div]
  have hψs : HasCompactSupport ψ := by
    refine hφs.mono fun w hw ↦ ?_
    rw [Function.mem_support] at hw ⊢
    intro h
    apply hw
    simp only [hψ_def, h, zero_div]
  have hφψ : (fun w ↦ a w * ψ w) = φ := by
    funext w
    by_cases hw : w ∈ tsupport φ
    · have hne := (hpos w (hφsupp hw)).ne'
      simp only [hψ_def]
      field_simp
    · simp only [hψ_def, image_eq_zero_of_notMem_tsupport hw, zero_div, mul_zero]
  have := superPoly_projDiff_weight_mul_of_monomials h1.continuous h2.continuous ha.continuous
    has ha0 hc hν hcoer hA hCbound hfam hψ hψs
  rwa [hφψ] at this

end Laplace.Multi
