/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.PairwiseRate

/-!
# The normalized pairwise moment difference

Stage J5e, closing the J5 arc: the rescaled posterior moments
`M(P,q) = ∫I(P,q)/∫I(1,q)` of two losses with matched jets below `k`
satisfy `(M₁(P,q) - M₂(P,q))/q^(k-2) → -Cov_γ(P, Q)`. The quotient
identity (one outer denominator, per the shape consult) reduces this
to J5d at `P` and at `1`, the ordinary limits of numerator and
denominator, and eventual denominator positivity. The ordinary limit
needs H4's dominated convergence at general polynomial growth, so
that generalization is proven here first.
-/

open Real MeasureTheory Filter Topology Metric

namespace Laplace.Multi

namespace LocalLaplaceDomain

variable {d : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- **H4 at polynomial growth**: the generic dominated convergence
for the rescaled Boltzmann integrand, with the quadratic-growth
hypothesis relaxed to polynomial growth (dominator integrable by the
general-rate Gaussian layer). -/
theorem tendsto_integral_rescaled_poly (A : LocalLaplaceDomain L H)
    {h : EuclidD d → ℝ} (h_cont : Continuous h)
    (h_growth : HasPolynomialGrowth h) :
    Tendsto (fun q : ℝ ↦ ∫ x : EuclidD d, A.integrand h q x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : EuclidD d, h x * quadKernel H x)) := by
  obtain ⟨C, n, hC, hg⟩ := h_growth
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : EuclidD d ↦ C * ((1 + ‖x‖ ^ n) *
      Real.exp (-A.c * ‖x‖ ^ 2))) ?_ ?_ ?_ ?_
  · filter_upwards with q
    have hset : MeasurableSet {x : EuclidD d | q • x ∈ A.U} :=
      (measurable_const_smul q) A.measurableSet_U
    have hmL : Measurable fun x : EuclidD d ↦
        Real.exp (-((L (q • x) - L 0) / q ^ 2)) := by
      have hm : Measurable fun x : EuclidD d ↦ L (q • x) :=
        A.measurable_L.comp (measurable_const_smul q)
      exact Real.measurable_exp.comp
        (((hm.sub measurable_const).div_const _).neg)
    exact ((h_cont.measurable.mul hmL).aestronglyMeasurable).indicator
      hset
  · filter_upwards [self_mem_nhdsWithin] with q hq
    refine Filter.Eventually.of_forall fun x ↦ ?_
    unfold integrand
    by_cases hmem : x ∈ {x : EuclidD d | q • x ∈ A.U}
    · rw [Set.indicator_of_mem hmem]
      have hlow := A.rescaled_lower hq hmem
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |h x| * Real.exp (-((L (q • x) - L 0) / q ^ 2))
          ≤ (C * (1 + ‖x‖ ^ n)) * Real.exp (-(A.c * ‖x‖ ^ 2)) := by
            apply mul_le_mul (hg x) _ (Real.exp_pos _).le
              (mul_nonneg hC (by positivity))
            exact Real.exp_le_exp.mpr (by linarith)
        _ = C * ((1 + ‖x‖ ^ n) * Real.exp (-A.c * ‖x‖ ^ 2)) := by
            rw [neg_mul]
            ring
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      have hx2 : (0:ℝ) ≤ (1 + ‖x‖ ^ n) * Real.exp (-A.c * ‖x‖ ^ 2) := by
        positivity
      exact mul_nonneg hC hx2
  · have hsum : Integrable (fun x : EuclidD d ↦
        Real.exp (-A.c * ‖x‖ ^ 2) +
          ‖x‖ ^ n * Real.exp (-A.c * ‖x‖ ^ 2)) :=
      (integrable_exp_neg_mul_sq_norm A.c_pos).add
        (integrable_pow_mul_exp_neg_mul_sq A.c_pos n)
    refine ((hsum.const_mul C).congr
      (Filter.Eventually.of_forall fun x ↦ ?_))
    ring
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have hev : ∀ᶠ q in 𝓝[>] (0 : ℝ), q • x ∈ A.U := by
      have hq_small : ∀ᶠ q in 𝓝[>] (0 : ℝ),
          q < A.delta / (‖x‖ + 1) := by
        apply eventually_nhdsWithin_of_eventually_nhds
        exact eventually_lt_nhds (div_pos A.delta_pos (by positivity))
      filter_upwards [hq_small, self_mem_nhdsWithin] with q hq hq0
      apply A.ball_subset_U
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_eq_abs, abs_of_pos hq0]
      calc q * ‖x‖ ≤ q * (‖x‖ + 1) := by
            apply mul_le_mul_of_nonneg_left _ hq0.le
            linarith
        _ < A.delta / (‖x‖ + 1) * (‖x‖ + 1) :=
            mul_lt_mul_of_pos_right hq (by positivity)
        _ = A.delta := by field_simp
    have hlim : Tendsto
        (fun q : ℝ ↦ h x * Real.exp (-((L (q • x) - L 0) / q ^ 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 (h x * quadKernel H x)) := by
      have h1 := A.toLocalQuadraticApprox.rescaled_tendsto x
      have h2 : Tendsto
          (fun q : ℝ ↦ Real.exp (-((L (q • x) - L 0) / q ^ 2)))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-(qform H x / 2)))) :=
        (Real.continuous_exp.continuousAt.tendsto.comp h1.neg)
      have hqk : quadKernel H x = Real.exp (-(qform H x / 2)) := by
        unfold quadKernel
        rw [neg_div]
      rw [hqk]
      exact h2.const_mul (h x)
    refine hlim.congr' ?_
    filter_upwards [hev] with q hmem
    unfold integrand
    rw [Set.indicator_of_mem
      (show x ∈ {x : EuclidD d | q • x ∈ A.U} from hmem)]

end LocalLaplaceDomain

namespace HigherLaplaceDomain

variable {d : ℕ} {k : ℕ} {L₁ L₂ : EuclidD d → ℝ}
  {H : Matrix (Fin d) (Fin d) ℝ}

/-- The rescaled posterior moment (the consult's internally-preferred
formulation). -/
noncomputable def rescaledMoment (A : HigherLaplaceDomain k L₁ H)
    (P : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  (∫ x : EuclidD d, A.toLocalLaplaceDomain.integrand P q x) /
    ∫ x : EuclidD d,
      A.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q x

/-- The rate-divided quotient identity (scalar form, per the shape
consult: only one outer denominator). -/
private theorem div_sub_div_rate (N₁ N₂ D₁ D₂ s : ℝ)
    (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0) (hs : s ≠ 0) :
    (N₁ / D₁ - N₂ / D₂) / s =
      ((N₁ - N₂) / s) / D₁ -
        (N₂ / D₂) * (((D₁ - D₂) / s) / D₁) := by
  field_simp
  ring

/-- **The normalized pairwise moment difference** (J5e, closing the
J5 arc): rescaled moments of matched-jet losses differ at rate
`q^(k-2)` by minus the Gaussian covariance with the degree-`k`
diagonal difference. -/
theorem tendsto_pairwise_normalized_moment_difference (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Tendsto (fun q : ℝ ↦
        (A₁.rescaledMoment P q - A₂.rescaledMoment P q) / q ^ (k - 2))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-gaussianCovariance H P
        (fun x ↦ taylorHomogeneousTerm k L₁ x -
          taylorHomogeneousTerm k L₂ x))) := by
  have hone_growth : HasPolynomialGrowth
      (fun _ : EuclidD d ↦ (1 : ℝ)) :=
    ⟨1, 0, zero_le_one, fun x ↦ by norm_num⟩
  have hZpos : 0 < ∫ x : EuclidD d, quadKernel H x :=
    integral_quadKernel_pos A₁.hH_posDef
  -- ordinary limits of the four scalar families
  have hD₁ := A₁.toLocalLaplaceDomain.tendsto_integral_rescaled_poly
    continuous_const hone_growth
  have hD₂ := A₂.toLocalLaplaceDomain.tendsto_integral_rescaled_poly
    continuous_const hone_growth
  have hN₂ := A₂.toLocalLaplaceDomain.tendsto_integral_rescaled_poly
    hP_cont hP_growth
  have hZone : (∫ x : EuclidD d, (1 : ℝ) * quadKernel H x) =
      ∫ x : EuclidD d, quadKernel H x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ one_mul _)
  rw [hZone] at hD₁ hD₂
  -- rate limits from J5d
  have hND := tendsto_pairwise_integral_difference hk A₁ A₂ hlower
    hP_cont hP_growth
  have hDD := tendsto_pairwise_integral_difference hk A₁ A₂ hlower
    continuous_const hone_growth
  have hDDval : (-∫ x : EuclidD d,
      (1 : ℝ) * (taylorHomogeneousTerm k L₁ x -
        taylorHomogeneousTerm k L₂ x) * quadKernel H x) =
      -∫ x : EuclidD d, (taylorHomogeneousTerm k L₁ x -
        taylorHomogeneousTerm k L₂ x) * quadKernel H x := by
    congr 1
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x ↦ by ring)
  rw [hDDval] at hDD
  -- eventual denominator positivity
  have hevD₁ : ∀ᶠ q in 𝓝[>] (0 : ℝ),
      0 < ∫ x : EuclidD d,
        A₁.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q x :=
    hD₁.eventually (eventually_gt_nhds hZpos)
  have hevD₂ : ∀ᶠ q in 𝓝[>] (0 : ℝ),
      0 < ∫ x : EuclidD d,
        A₂.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q x :=
    hD₂.eventually (eventually_gt_nhds hZpos)
  -- assemble the limit of the rearranged expression
  have hterm₁ : Tendsto (fun q : ℝ ↦
      (((∫ x : EuclidD d, A₁.toLocalLaplaceDomain.integrand P q x) -
        ∫ x : EuclidD d, A₂.toLocalLaplaceDomain.integrand P q x) /
          q ^ (k - 2)) /
        ∫ x : EuclidD d,
          A₁.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q x)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-∫ x : EuclidD d,
        P x * (taylorHomogeneousTerm k L₁ x -
          taylorHomogeneousTerm k L₂ x) * quadKernel H x) /
        ∫ x : EuclidD d, quadKernel H x)) :=
    hND.div hD₁ hZpos.ne'
  have hterm₂ : Tendsto (fun q : ℝ ↦
      ((∫ x : EuclidD d, A₂.toLocalLaplaceDomain.integrand P q x) /
        ∫ x : EuclidD d,
          A₂.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q x) *
      ((((∫ x : EuclidD d,
          A₁.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q x) -
        ∫ x : EuclidD d,
          A₂.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q x) /
          q ^ (k - 2)) /
        ∫ x : EuclidD d,
          A₁.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((∫ x : EuclidD d, P x * quadKernel H x) /
          ∫ x : EuclidD d, quadKernel H x) *
        ((-∫ x : EuclidD d, (taylorHomogeneousTerm k L₁ x -
          taylorHomogeneousTerm k L₂ x) * quadKernel H x) /
          ∫ x : EuclidD d, quadKernel H x))) :=
    (hN₂.div hD₂ hZpos.ne').mul (hDD.div hD₁ hZpos.ne')
  have hcomb := hterm₁.sub hterm₂
  -- identify the limit with minus the covariance
  have hval : ((-∫ x : EuclidD d,
      P x * (taylorHomogeneousTerm k L₁ x -
        taylorHomogeneousTerm k L₂ x) * quadKernel H x) /
        ∫ x : EuclidD d, quadKernel H x) -
      ((∫ x : EuclidD d, P x * quadKernel H x) /
          ∫ x : EuclidD d, quadKernel H x) *
        ((-∫ x : EuclidD d, (taylorHomogeneousTerm k L₁ x -
          taylorHomogeneousTerm k L₂ x) * quadKernel H x) /
          ∫ x : EuclidD d, quadKernel H x) =
      -gaussianCovariance H P
        (fun x ↦ taylorHomogeneousTerm k L₁ x -
          taylorHomogeneousTerm k L₂ x) := by
    unfold gaussianCovariance gaussianExpectation
    set Z : ℝ := ∫ x : EuclidD d, quadKernel H x with hZ_def
    set I₁ : ℝ := ∫ x : EuclidD d,
      P x * (taylorHomogeneousTerm k L₁ x -
        taylorHomogeneousTerm k L₂ x) * quadKernel H x with hI₁_def
    set I₂ : ℝ := ∫ x : EuclidD d, P x * quadKernel H x with hI₂_def
    set I₃ : ℝ := ∫ x : EuclidD d, (taylorHomogeneousTerm k L₁ x -
      taylorHomogeneousTerm k L₂ x) * quadKernel H x with hI₃_def
    ring
  rw [← hval]
  refine hcomb.congr' ?_
  filter_upwards [hevD₁, hevD₂, self_mem_nhdsWithin] with q h₁ h₂ hq
  have hq0 : (0 : ℝ) < q := hq
  have hqk : (q : ℝ) ^ (k - 2) ≠ 0 := by positivity
  rw [rescaledMoment, rescaledMoment]
  exact (div_sub_div_rate _ _ _ _ _ h₁.ne' h₂.ne' hqk).symm

end HigherLaplaceDomain

end Laplace.Multi
