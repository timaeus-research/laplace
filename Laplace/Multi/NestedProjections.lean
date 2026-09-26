/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ObservableDefect

/-!
# Nested projections in `L²(Q)`: the affine span of the statistic inside `L²(σ(S))`

For a probability law `Q` on `X` and bounded statistics `S`, three nested closed subspaces of
`L²(Q)`:

  `A = span{1, S_j} ⊆ L²(σ(S)) ⊆ L²(Q)`,

with orthogonal projections `B` (onto `A`, the best affine predictor in the statistic) and `C`
(`condExpL2`, the conditional expectation given the statistic). Nesting gives the three-way
Pythagorean decomposition of every `h ∈ L²(Q)`:

  `‖h‖² = ‖B h‖² + ‖C h − B h‖² + ‖h − C h‖²`          (`norm_sq_eq_statSpan_add_condExpL2`),

the quadratic shadow of the nonlinear information split `KL(D‖ν) = 𝓘(M_D) + L + R`: the part of a
score explained by the response coordinates, the part explained by the law of the statistic but
not by its mean, and the part inside the fibres. The abstract statement for nested subspaces of a
real inner product space is `norm_sq_eq_three_starProjection`; `starProjection_minimal` identifies
`B h` as the affine function of the statistic closest to `h` in mean square.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace

namespace Laplace.Multi

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Three-way Pythagoras for nested subspaces** `U ≤ V`:
`‖x‖² = ‖P_U x‖² + ‖P_V x − P_U x‖² + ‖x − P_V x‖²`. -/
theorem norm_sq_eq_three_starProjection (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hUV : U ≤ V) (x : E) :
    ‖x‖ ^ 2 = ‖U.starProjection x‖ ^ 2 + ‖V.starProjection x - U.starProjection x‖ ^ 2 +
      ‖x - V.starProjection x‖ ^ 2 := by
  have h1 := Submodule.norm_sq_eq_add_norm_sq_starProjection x V
  rw [Submodule.starProjection_orthogonal_val] at h1
  have hU : U.starProjection (V.starProjection x) = U.starProjection x := by
    rw [Submodule.starProjection_apply U (V.starProjection x),
      Submodule.orthogonalProjectionOnto_starProjection_of_le hUV,
      ← Submodule.starProjection_apply]
  have h2 := Submodule.norm_sq_eq_add_norm_sq_starProjection (V.starProjection x) U
  rw [Submodule.starProjection_orthogonal_val, hU] at h2
  linarith

end Abstract

section Statistic

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Finite J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (Q : Measure X) [IsProbabilityMeasure Q]

omit [Finite J] in
/-- Bounded measurable functions are square integrable under a probability law. -/
theorem memLp_two_bdd {f : X → ℝ} (hf : Bdd f) : MemLp f 2 Q := by
  obtain ⟨hm, B, hB⟩ := hf
  exact MemLp.of_bound hm.aestronglyMeasurable B (Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs]; exact hB x)

include hS

/-- **The affine span of the statistic** in `L²(Q)`: `span{1, S_j : j ∈ J}`. -/
noncomputable def statSpan : Submodule ℝ (Lp ℝ 2 Q) :=
  Submodule.span ℝ (insert ((memLp_const (1 : ℝ)).toLp fun _ ↦ (1 : ℝ))
    (Set.range fun j ↦ (memLp_two_bdd Q (hS j)).toLp (S j)))

instance : FiniteDimensional ℝ (statSpan hS Q) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_range _).insert _)

instance : CompleteSpace (statSpan hS Q) :=
  (statSpan hS Q).complete_of_finiteDimensional.completeSpace_coe

omit [Finite J] in
/-- Affine functions of the statistic are `σ(S)`-measurable: `A ⊆ L²(σ(S))`. -/
theorem statSpan_le_lpMeas : statSpan hS Q ≤ lpMeas ℝ ℝ (statSigma S) 2 Q := by
  refine Submodule.span_le.2 ?_
  rintro f (rfl | ⟨j, rfl⟩)
  · rw [SetLike.mem_coe, mem_lpMeas_iff_aestronglyMeasurable]
    have h1 : Measurable[statSigma S] (fun _ : X ↦ (1 : ℝ)) := measurable_const
    exact h1.stronglyMeasurable.aestronglyMeasurable.congr (MemLp.coeFn_toLp _).symm
  · rw [SetLike.mem_coe, mem_lpMeas_iff_aestronglyMeasurable]
    have h1 : Measurable[statSigma S] (S j) :=
      (measurable_pi_apply j).comp (comap_measurable (statPoint S))
    exact h1.stronglyMeasurable.aestronglyMeasurable.congr (MemLp.coeFn_toLp _).symm

/-- **Three-way Pythagoras in `L²(Q)`**: `‖h‖² = ‖B h‖² + ‖C h − B h‖² + ‖h − C h‖²`, with `B` the
projection onto the affine span of the statistic and `C` the conditional expectation given the
statistic. -/
theorem norm_sq_eq_statSpan_add_condExpL2 (h : Lp ℝ 2 Q) :
    haveI : Fact (statSigma S ≤ ‹MeasurableSpace X›) := ⟨statSigma_le hS⟩
    ‖h‖ ^ 2 = ‖(statSpan hS Q).starProjection h‖ ^ 2 +
      ‖(condExpL2 ℝ ℝ (statSigma_le hS) h : Lp ℝ 2 Q) - (statSpan hS Q).starProjection h‖ ^ 2 +
      ‖h - condExpL2 ℝ ℝ (statSigma_le hS) h‖ ^ 2 := by
  have : Fact (statSigma S ≤ ‹MeasurableSpace X›) := ⟨statSigma_le hS⟩
  have e : ((condExpL2 ℝ ℝ (statSigma_le hS) h : lpMeas ℝ ℝ (statSigma S) 2 Q) : Lp ℝ 2 Q) =
      (lpMeas ℝ ℝ (statSigma S) 2 Q).starProjection h := rfl
  rw [e]
  exact norm_sq_eq_three_starProjection _ _ (statSpan_le_lpMeas hS Q) h

/-- **The best affine predictor**: `‖h − B h‖ = inf_{g ∈ A} ‖h − g‖`. -/
theorem norm_sub_statSpan_starProjection (h : Lp ℝ 2 Q) :
    ‖h - (statSpan hS Q).starProjection h‖ = ⨅ g : statSpan hS Q, ‖h - g‖ :=
  Submodule.starProjection_minimal h

omit hS [IsProbabilityMeasure Q] in
/-- The squared `L²` norm is the second moment. -/
theorem norm_sq_eq_integral_sq (h : Lp ℝ 2 Q) : ‖h‖ ^ 2 = ∫ x, (h x) ^ 2 ∂Q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [sq]

end Statistic

end Laplace.Multi
