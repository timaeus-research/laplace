/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AnalyticBridge1D

/-!
# The paper-facing Taylor tree in one variable (Stage 6c)

Unit 259 (review v24 should-fixes). The paper's hypothesis in dimension one: real functions `ξ,
η` on
`[0,b]` with holomorphic extensions `Fξ, Fη` to the open disc `|z| < R`, `R > b`, agreeing with
`ξ, η`
on `(0,b]`. Choosing `r ∈ (b, R)`, the closed disc of radius `r` lies in the open disc, so the
one-variable bridge applies, and the family standard integral **is** the original standard integral
`∫_{(0,b]} η(u) u^h e^{-βN u^{2k} + β√N u^k ξ(u)} du` (`familyPhaseIntegralBox_eq_orig_1d`,
extensional
transport through the representation identities). Hence

**Headline XXXI′** (`thm_TaylorTree_analytic_1d'`): under the paper's own hypothesis in `d = 1`,
`Z(N) = ∫_{(0,b]} η u^h e^{-βN u^{2k} + β√N u^k ξ(u)} du` satisfies the Taylor-tree conclusion with
the coefficient system of the real Cauchy-coefficient families. No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-- The original one-variable standard integral on `(0,b]` for real functions `ξ, η`. -/
noncomputable def origPhaseIntegral1D (h k : Fin 1 → ℕ) (β N b : ℝ) (ξ η : ℝ → ℝ) : ℝ :=
  ∫ u in piBox 1 (Ioc 0 b), η (u 0) * (u 0) ^ h 0 *
    Real.exp (-(β * N * (u 0) ^ (2 * k 0)) + β * (Real.sqrt N * (u 0) ^ k 0) * ξ (u 0))

/-- On `(0,b]` the family standard integral is the original standard integral, once the families
represent the functions there. -/
theorem familyPhaseIntegralBox_eq_orig_1d (h k : Fin 1 → ℕ) (β N b : ℝ)
    {cξ cη : CoeffFamily 1} {ξ η : ℝ → ℝ}
    (hξ : ∀ u ∈ piBox 1 (Ioc 0 b), evalF cξ u = ξ (u 0))
    (hη : ∀ u ∈ piBox 1 (Ioc 0 b), evalF cη u = η (u 0)) :
    familyPhaseIntegralBox 0 h k β N b cξ cη = origPhaseIntegral1D h k β N b ξ η := by
  unfold familyPhaseIntegralBox origPhaseIntegral1D
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun u hu => ?_
  rw [hξ u hu, hη u hu]
  simp

/-- A holomorphic function on the open disc `|z| < R` is differentiable on every closed disc of
radius `r < R`. -/
theorem differentiableOn_closedBall_of_ball {f : ℂ → ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f
(Metric.ball 0 R))
    {r : NNReal} (hr : (r : ℝ) < R) : DifferentiableOn ℂ f (Metric.closedBall 0 r) :=
  hf.mono (Metric.closedBall_subset_ball hr)

/-- **Headline XXXI′ — `thm:TaylorTree` in dimension one under the paper's hypothesis.** Let `ξ, η`
be real functions on `(0,b]` with holomorphic extensions `Fξ, Fη` to `|z| < R`, `R > b > 0` (`Re
Fξ = ξ`,
`Re Fη = η` on `(0,b]`). Then for any `r ∈ (b, R)` the real Cauchy-coefficient families of `Fξ,
Fη` at
radius `r` satisfy the Taylor-tree conclusion, and their family standard integral is the original
`Z(N) = ∫_{(0,b]} η u^h e^{-βN u^{2k} + β√N u^k ξ} du`. -/
theorem thm_TaylorTree_analytic_1d' (h k : Fin 1 → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {b R : ℝ} (hb : 0 < b) {r : NNReal} (hbr : b < r) (hrR : (r : ℝ) < R)
    {Fξ Fη : ℂ → ℂ} {ξ η : ℝ → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (Metric.ball 0 R)) (hFη : DifferentiableOn ℂ Fη (Metric.ball 0 R))
    (hξ : ∀ x ∈ Ioc (0 : ℝ) b, (Fξ x).re = ξ x) (hη : ∀ x ∈ Ioc (0 : ℝ) b, (Fη x).re = η x) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion 0 h k β b (toFamily1 (realCoeff Fξ r)) (toFamily1 (realCoeff Fη r)) C ∧
      ∀ N, familyPhaseIntegralBox 0 h k β N b (toFamily1 (realCoeff Fξ r))
        (toFamily1 (realCoeff Fη r)) = origPhaseIntegral1D h k β N b ξ η := by
  have hr : 0 < r := by
    have : (0 : ℝ) < r := lt_trans hb hbr
    exact_mod_cast this
  have hξ' := differentiableOn_closedBall_of_ball hFξ hrR
  have hη' := differentiableOn_closedBall_of_ball hFη hrR
  obtain ⟨hrep, C, hC⟩ := thm_TaylorTree_analytic_1d h k hk β hβ hr hb hbr hξ' hη'
  refine ⟨C, hC, fun N => familyPhaseIntegralBox_eq_orig_1d h k β N b ?_ ?_⟩
  · intro u hu
    rw [(hrep u hu).1]
    exact hξ (u 0) (hu 0 (Set.mem_univ _))
  · intro u hu
    rw [(hrep u hu).2]
    exact hη (u 0) (hu 0 (Set.mem_univ _))

end Laplace.Grammar
