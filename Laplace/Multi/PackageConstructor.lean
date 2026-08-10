/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.LocalRateDCT

/-!
# The package-derivation wrapper

The located recovery headlines consume certified package families
`∀ k, 2 < k → HigherLaplaceDomain k L H`. This file derives such a
family from a bare smooth-nondegenerate-minimum setup: global
smoothness, vanishing gradient at the minimum, a positive-definite
matrix matching the Hessian quadratic form on diagonals, and
per-order fixed-ball Taylor remainder bounds
(`higherLaplaceDomainFamily_ofTaylorBounds`). The quadratic Peano
field reuses the corpus `quadratic_peano` (transferred to `H` by the
diagonal equality), the coercivity radius comes from
`exists_local_lower_bound`, and one shrunk radius
`ρ = min δ r` serves as region, delta, and Taylor radius at once, so
both inclusion fields are reflexive.

The remaining input, `htaylor`, is the fixed-ball Taylor bound per
order; deriving it from `ContDiff` alone (the radial
Lagrange route) is deliberately a separate tide, per the scoping
consult archived in the tide log.
-/

open Real MeasureTheory Filter Topology Metric

namespace Laplace.Multi

variable {d : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The quadratic package from a bare setup: global `C²`, vanishing
gradient, and a positive-definite `H` matching the Hessian form. -/
noncomputable def LocalQuadraticApprox.ofBareSetup
    (hL2 : ContDiff ℝ 2 L) (hgrad : fderiv ℝ L 0 = 0)
    (hdiag : ∀ y, qform (hessianMatrix L) y = qform H y)
    (hH : H.PosDef) : LocalQuadraticApprox L H where
  hH_posDef := hH
  lambda := (qform_coercive hH).choose
  lambda_pos := (qform_coercive hH).choose_spec.1
  qform_lower := (qform_coercive hH).choose_spec.2
  quadratic_peano := by
    have h := _root_.Laplace.Multi.quadratic_peano hL2 hgrad
    refine h.congr' (Filter.Eventually.of_forall fun y ↦ ?_)
      (Filter.EventuallyEq.refl _ _)
    beta_reduce
    rw [hdiag]

/-- **The package family from a bare setup**: global smoothness,
vanishing gradient, diagonal-matched positive-definite `H`, and
per-order fixed-ball Taylor remainder bounds produce the certified
family the located recovery headlines consume. -/
noncomputable def higherLaplaceDomainFamily_ofTaylorBounds
    (hcont : ∀ k : ℕ, ContDiff ℝ k L)
    (hgrad : fderiv ℝ L 0 = 0)
    (hdiag : ∀ y, qform (hessianMatrix L) y = qform H y)
    (hH : H.PosDef)
    (htaylor : ∀ k : ℕ, 2 < k → ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ y ∈ Metric.ball (0 : EuclidD d) r,
        |L y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L y| ≤
          C * ‖y‖ ^ k) :
    ∀ k, 2 < k → HigherLaplaceDomain k L H := by
  intro k h2
  classical
  refine
    let Q := LocalQuadraticApprox.ofBareSetup (hcont 2) hgrad hdiag hH
    let δ := Q.exists_local_lower_bound.choose
    let c := Q.exists_local_lower_bound.choose_spec.choose
    let r := (htaylor k h2).choose
    let C := (htaylor k h2).choose_spec.choose
    let ρ := min δ r
    ?_
  have hδ : 0 < δ := Q.exists_local_lower_bound.choose_spec.choose_spec.1
  have hc : 0 < c := Q.exists_local_lower_bound.choose_spec.choose_spec.2.1
  have hlow : ∀ q : ℝ, ∀ x : EuclidD d, 0 < q → ‖q • x‖ ≤ δ →
      c * ‖x‖ ^ 2 ≤ (L (q • x) - L 0) / q ^ 2 :=
    Q.exists_local_lower_bound.choose_spec.choose_spec.2.2
  have hr : 0 < r := (htaylor k h2).choose_spec.choose_spec.1
  have hC : 0 ≤ C := (htaylor k h2).choose_spec.choose_spec.2.1
  have hbound : ∀ y ∈ Metric.ball (0 : EuclidD d) r,
      |L y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L y| ≤
        C * ‖y‖ ^ k :=
    (htaylor k h2).choose_spec.choose_spec.2.2
  have hρ : 0 < ρ := lt_min hδ hr
  exact
    { toLocalQuadraticApprox := Q
      U := Metric.ball (0 : EuclidD d) ρ
      measurableSet_U := measurableSet_ball
      delta := ρ
      delta_pos := hρ
      ball_subset_U := Set.Subset.rfl
      c := c
      c_pos := hc
      rescaled_lower := by
        intro q x hq hmem
        refine hlow q x hq ?_
        have := Metric.mem_ball.mp hmem
        rw [dist_zero_right] at this
        exact this.le.trans (min_le_left _ _)
      measurable_L := (hcont 0).continuous.measurable
      contDiff_k := hcont k
      taylorRadius := ρ
      taylorRadius_pos := hρ
      taylorBall_subset := Set.Subset.rfl
      taylorRemainderConst := C
      taylorRemainderConst_nonneg := hC
      taylorRemainder_bound := by
        intro y hy
        refine hbound y ?_
        have := Metric.mem_ball.mp hy
        rw [dist_zero_right] at this
        exact Metric.mem_ball.mpr (by
          rw [dist_zero_right]
          exact lt_of_lt_of_le this (min_le_right _ _)) }

end Laplace.Multi
